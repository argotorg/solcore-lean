import Solcore.Frontend.SourceCoreCompatibleDataEquality
import Solcore.Frontend.SourceCoreCompatibleValues
import Solcore.Frontend.SourceCoreDataPlaces
import Solcore.Frontend.SourceCoreLoops

/-! Data leaves and policy factories for the separate source-compatible
profile. Original closed metadata is resolved in the compile-time registry;
input extensions preserve those IDs. Nominal members select the stored fields,
mapping lookups transport the actual header default, and mapping reads create
an empty value only when the source cell's declared type is a bare mapping.

Recursion, calls and control flow belong to the existing caller-owned policy.
No source evaluator or strict-catalog cast is used. Projected assignments and
pattern lowering are separate compatible adapters. -/

set_option autoImplicit false

namespace Solcore.Frontend.SourceCoreCompatibleDataExpressions
open SourceInference
abbrev Context := SourceCoreCompatibleValues.Context
abbrev Checked := SourceCoreCompatibleCatalog.Checked
abbrev Scope := SourceCoreBasic.Scope
abbrev Error := SourceCoreBasic.Error
abbrev LoweredExpr := SourceCoreBasic.LoweredExpr
abbrev ExpressionLowerer := SourceCoreFunctions.ExpressionLowerer

def projectType (checked : Checked) (site : SourceCoreElaboration.ErrorSite)
    (type : TypeSystem.Ty) : Except Error Core.Ty :=
  (checked.project type).map (·.type) |>.mapError
    (fun _ => .typeProjection ⟨site, .unsupportedType type⟩)

def readExpression (checked : Checked) (source : TypedSource) (id : ExpressionId) :
    Except Error (ExpressionNode × Core.Ty) := do
  if id.occurrence.owner ≠ source.owner then throw (.ownerMismatch source.owner id.occurrence.owner)
  let node ← match source.lookupExpression? id with
    | some node => pure node | none => throw (.missingExpression id)
  unless node.requirements.isEmpty do throw (.requirementsPresent id)
  unless node.coercions.isEmpty do throw (.coercionsPresent id)
  pure (node, ← projectType checked (.occurrence id.occurrence) node.type)

def readStatement (checked : Checked) (source : TypedSource) (id : StatementId) :
    Except Error (StatementNode × Core.Ty) := do
  if id.occurrence.owner ≠ source.owner then throw (.ownerMismatch source.owner id.occurrence.owner)
  let node ← match source.lookupStatement? id with
    | some node => pure node | none => throw (.missingStatement id)
  pure (node, ← projectType checked (.occurrence id.occurrence) node.type)

def lowerBinder (checked : Checked) (source : TypedSource) (scope : Scope)
    (binder : TypedBinder) : Except Error Core.Ty := do
  if binder.id.owner ≠ source.owner then throw (.ownerMismatch source.owner binder.id.owner)
  unless binder.scheme.quantified.isEmpty do throw (.polymorphicBinding binder.id)
  unless binder.schemeRequirements.isEmpty do throw (.bindingRequirementsPresent binder.id)
  if binder.comptime && !checked.catalog.callableContracts then throw (.comptimeBinding binder.id)
  if scope.any (fun entry => decide (entry.1 = binder.id)) then throw (.duplicateBinding binder.id)
  projectType checked (.binder binder.id) binder.scheme.body

def lowerAssignment (checked : Checked) (source : TypedSource) (scope : Scope)
    (assignment : AssignmentResolution) (operator : Syntax.ValueAssignOp) : Except Error (Nat × Core.Ty) := do
  if operator ≠ .equal then throw (.unsupportedAssignmentOperator operator)
  let binder := assignment.target.root
  if binder.owner ≠ source.owner then throw (.ownerMismatch source.owner binder.owner)
  unless assignment.requirements.isEmpty do throw (.assignmentRequirementsPresent binder)
  unless assignment.target.projections.isEmpty do throw (.projectedAssignment binder)
  let (index, type) ← match SourceCoreLocalCell.lookup? scope binder with
    | some entry => pure entry | none => throw (.missingBinding binder)
  let projected ← projectType checked (.binder binder) assignment.target.type
  SourceCoreBasic.ensureType (.binder binder) type projected
  pure (index, type)

private def unsupported (node : ExpressionNode) : Error := .unsupportedExpression node.id node.form

private def metadataId (context : Context) (node : ExpressionNode)
    (metadata : SourceCoreRawMetadata.Metadata) : Except Error Core.Word :=
  match context.registry.id? metadata with
  | some id => pure id | none => throw (unsupported node)

def quote : Core.Value → Option Core.Expr
  | .unit => some .unit
  | .bool value => some (.bool value)
  | .word value => some (.word value)
  | .integer value => some (.integer value)
  | .pair left right => do pure (.pair (← quote left) (← quote right))
  | .inLeft type value => do pure (.inLeft type (← quote value))
  | .inRight type value => do pure (.inRight type (← quote value))
  | .constructed constructor value => do pure (.construct constructor (← quote value))
  | _ => none

/-- Code generation does not extend the frozen static registry. A prepared
inventory must already contain the metadata of every emitted literal. -/
def staticValue (fuel : Nat) (context : Context) (node : ExpressionNode)
    (type : TypeSystem.Ty) (source : SourceCoreCompatibleValues.Value) : Except Error Core.Expr := do
  let encoded ← (SourceCoreCompatibleValues.encode fuel context type source).mapError (fun _ => unsupported node)
  unless encoded.context.registry.entries = context.registry.entries do throw (unsupported node)
  match quote encoded.value with
  | some expression => pure expression | none => throw (unsupported node)

def construct (constructor : Core.ConstructorId) (metadata : Core.Word) (arguments : Core.Expr) : Core.Expr :=
  Core.LanguageResult.bind (.namedData constructor.owner) arguments
    (Core.LanguageResult.success (.construct constructor (.pair (.word metadata) (.var 0))))

/-- The absent path computes its empty literal once before writing it to the
shared optional cell. Existing initialized mappings retain their header. -/
def readMapping (reference empty : Core.Expr) : Core.Expr :=
  .letE reference
    (.caseE (.loadCell (.var 0))
      (.letE (empty.weakenAt 0 |>.weakenAt 0)
        (.letE (.storeCell (.var 2) (.inRight .unit (.var 0)))
          (Core.LanguageResult.success (.var 1))))
      (Core.LanguageResult.success (.var 0)))

def lowerRead (fuel : Nat) (context : Context) (source : TypedSource) (scope : Scope)
    (id : ExpressionId) (reason : Core.Word) : Except Error Core.Expr := do
  let (node, type) ← readExpression context.checked source id
  let binder ← match node.form with
    | .reference _ (.local binder) => pure binder | _ => throw (unsupported node)
  if binder.owner ≠ source.owner then throw (.ownerMismatch source.owner binder.owner)
  let (index, payload) ← match SourceCoreLocalCell.lookup? scope binder with
    | some entry => pure entry | none => throw (.missingBinding binder)
  SourceCoreBasic.ensureType (.occurrence id.occurrence) type payload
  let declared ← SourceCoreDataPlaces.rootBinder source binder
  match declared.scheme.body with
  | .mapping key value =>
      let empty ← staticValue fuel context node declared.scheme.body (.mapping key value [])
      pure (readMapping (.var index) empty)
  | _ => pure (Core.OptionalCell.read payload (.var index) reason)

/-- The actual member branch generator, also used to extract static lowering
certificates for the raw constructor metadata and selected payload. -/
def memberBranches (context : Context) (node : ExpressionNode)
    (baseType : TypeSystem.Ty) (result : Core.Ty) (index : Nat) :
    Except Error (Core.DataTypeId × List Core.Expr) := do
  let baseType := SourceCoreRawMetadata.runtimeType baseType
  let (declaration, arguments) ← match SourceCoreDataCatalog.nominalParts baseType with
    | some parts => pure parts | none => throw (unsupported node)
  let signature ← match context.checked.signatures.dataTypes.filter (fun data => decide (data.id = declaration)) with
    | [signature] => pure signature | _ => throw (unsupported node)
  unless signature.parameters.length = arguments.length && !signature.constructors.isEmpty do throw (unsupported node)
  let dataType ← match context.checked.catalog.identity? baseType with
    | some identity => pure identity | none => throw (unsupported node)
  let substitution : TypeSystem.ParameterSubstitution := signature.parameters.zip arguments
  let branches ← signature.constructors.zipIdx.mapM fun (constructor, position) => do
    let payloadTypes := constructor.payloadTypes.map substitution.apply
    let instantiation : DataConstructorInstantiation := ⟨constructor.id, substitution, payloadTypes, baseType⟩
    let resolved ← (context.checked.resolveConstructor instantiation).mapError (fun _ => unsupported node)
    unless resolved.owner = dataType && resolved.index = position do throw (unsupported node)
    let selected ← match payloadTypes[index]? with
      | some selected => projectType context.checked (.occurrence node.id.occurrence) selected
      | none => throw (unsupported node)
    SourceCoreBasic.ensureType (.occurrence node.id.occurrence) result selected
    let payloads ← payloadTypes.mapM (projectType context.checked (.occurrence node.id.occurrence))
    pure (Core.LanguageResult.success (SourceCoreDataExpressions.projectPacked index payloads (.second (.var 0))))
  pure (dataType, branches)

/-- Base and key effects complete before comparator preparation. Missing
entries select the transported default of the actual evaluated mapping. -/
def index (layout : Core.OrderedMapping.Layout) (comparison base key : Core.Expr)
    (missingBase : Core.Word) : Core.Expr :=
  Core.LanguageResult.bind layout.valueType base
    (Core.LanguageResult.bind layout.valueType (key.weakenAt 0)
      (SourceCoreMappingWithDefault.lookup layout missingBase
        (comparison.weakenAt 0 |>.weakenAt 0) (.var 1) (.var 0)))

theorem index_hasType {definitions : Core.DataEnvironment} {environment : Core.Context}
    {layout : Core.OrderedMapping.Layout} {comparison base key : Core.Expr} (missingBase : Core.Word)
    (registered : layout.Registered definitions)
    (comparisonTyped : Core.HasType environment comparison
      (.function (.product layout.keyType layout.keyType) .bool) definitions)
    (baseTyped : Core.HasType environment base
      (Core.LanguageResult.resultType (SourceCoreMappingWithDefault.type layout)) definitions)
    (keyTyped : Core.HasType environment key (Core.LanguageResult.resultType layout.keyType) definitions) :
    Core.HasType environment (index layout comparison base key missingBase)
      (Core.LanguageResult.resultType layout.valueType) definitions := by
  apply Core.LanguageResult.bind_hasType registered.valueWellFormed baseTyped
  apply Core.LanguageResult.bind_hasType registered.valueWellFormed
    (by simpa [Core.Context.insertAt] using
      keyTyped.weakenAt (inserted := SourceCoreMappingWithDefault.type layout) 0)
  apply SourceCoreMappingWithDefault.lookup_hasType missingBase registered
  · simpa [Core.Context.insertAt, Core.OrderedMapping.Layout.comparisonType] using
      (comparisonTyped.weakenAt (inserted := SourceCoreMappingWithDefault.type layout) 0).weakenAt
        (inserted := layout.keyType) 0
  · exact .var rfl
  · exact .var rfl

theorem index_base_failure {environment : Core.Environment} {before after : Core.Store}
    (layout : Core.OrderedMapping.Layout) (missingBase : Core.Word) {comparison base key : Core.Expr}
    {reason : Core.Word} (failed : Core.Evaluates environment before base
      (.inLeft (SourceCoreMappingWithDefault.type layout) (.word reason)) after) :
    Core.Evaluates environment before (index layout comparison base key missingBase)
      (.inLeft layout.valueType (.word reason)) after := Core.LanguageResult.bind_failure _ failed

theorem index_key_failure {environment : Core.Environment} {before middle after : Core.Store}
    (layout : Core.OrderedMapping.Layout) (missingBase : Core.Word) {comparison base key : Core.Expr}
    {mapping : Core.Value} {reason : Core.Word}
    (baseEvaluated : Core.Evaluates environment before base (.inRight .word mapping) middle)
    (keyFailed : Core.Evaluates (mapping :: environment) middle (key.weakenAt 0)
      (.inLeft layout.keyType (.word reason)) after) :
    Core.Evaluates environment before (index layout comparison base key missingBase)
      (.inLeft layout.valueType (.word reason)) after :=
  Core.LanguageResult.bind_success _ baseEvaluated (Core.LanguageResult.bind_failure _ keyFailed)

theorem index_completed {environment : Core.Environment} {before middle selected after : Core.Store}
    (layout : Core.OrderedMapping.Layout) (missingBase : Core.Word) {comparison base key : Core.Expr}
    {mapping keyValue result : Core.Value}
    (baseEvaluated : Core.Evaluates environment before base (.inRight .word mapping) middle)
    (keyEvaluated : Core.Evaluates (mapping :: environment) middle (key.weakenAt 0)
      (.inRight .word keyValue) selected)
    (lookedUp : Core.Evaluates (keyValue :: mapping :: environment) selected
      (SourceCoreMappingWithDefault.lookup layout missingBase (comparison.weakenAt 0 |>.weakenAt 0)
        (.var 1) (.var 0)) result after) :
    Core.Evaluates environment before (index layout comparison base key missingBase) result after :=
  Core.LanguageResult.bind_success _ baseEvaluated (Core.LanguageResult.bind_success _ keyEvaluated lookedUp)

def lowerWithReasons (fuel : Nat) (context : Context) (lowerChild : ExpressionLowerer)
    (source : TypedSource) (scope : Scope) (id : ExpressionId) (reasonAt : ExpressionId → Core.Word) :
    Except Error LoweredExpr := do
  match fuel with
  | 0 => throw (.traversalExhausted (.occurrence id.occurrence))
  | fuel + 1 =>
      let (node, type) ← readExpression context.checked source id
      let site := SourceCoreElaboration.ErrorSite.occurrence id.occurrence
      match node.form with
      | .constructor instantiation arguments =>
          unless node.type = instantiation.resultType do throw (unsupported node)
          unless arguments.length = instantiation.payloadTypes.length do throw (unsupported node)
          let constructor ← (context.checked.resolveConstructor instantiation).mapError (fun _ => unsupported node)
          let metadata ← metadataId context node (.constructor instantiation)
          SourceCoreBasic.ensureType site type (.namedData constructor.owner)
          let lowered ← (arguments.zip instantiation.payloadTypes).mapM fun (argument, expected) => do
            let expected ← projectType context.checked site expected
            let argument ← lowerChild fuel source scope argument reasonAt
            SourceCoreBasic.ensureType site expected argument.type
            pure argument
          pure ⟨type, construct constructor metadata (SourceCoreCalls.packArguments lowered).expression⟩
      | .proxy inner =>
          unless node.type = .proxy inner do throw (unsupported node)
          let identity ← match context.checked.catalog.identity? node.type with
            | some identity => pure identity | none => throw (unsupported node)
          let metadata ← metadataId context node (.proxy inner)
          SourceCoreBasic.ensureType site type (.namedData identity)
          unless context.checked.catalog.definitions.lookupConstructorPayloadType? ⟨identity, 0⟩ = some .word do
            throw (unsupported node)
          pure ⟨type, Core.LanguageResult.success (.construct ⟨identity, 0⟩ (.word metadata))⟩
      | .member base _ selected =>
          let (baseNode, baseType) ← readExpression context.checked source base
          let (owner, branches) ← memberBranches context node baseNode.type type selected
          SourceCoreBasic.ensureType site (.namedData owner) baseType
          let base ← lowerChild fuel source scope base reasonAt
          SourceCoreBasic.ensureType site baseType base.type
          pure ⟨type, SourceCoreDataExpressions.member owner type branches base.expression⟩
      | .index base key =>
          let (baseNode, baseType) ← readExpression context.checked source base
          let (keyType, valueType) ← match SourceCoreRawMetadata.runtimeType baseNode.type with
            | .mapping key value => pure (key, value) | _ => throw (unsupported node)
          let layout ← (context.checked.catalog.mappingLayout keyType valueType).mapError (fun _ => unsupported node)
          SourceCoreBasic.ensureType site type layout.valueType
          SourceCoreBasic.ensureType site baseType (SourceCoreMappingWithDefault.type layout)
          let base ← lowerChild fuel source scope base reasonAt
          let key ← lowerChild fuel source scope key reasonAt
          SourceCoreBasic.ensureType site baseType base.type
          SourceCoreBasic.ensureType site layout.keyType key.type
          let comparison ← (SourceCoreCompatibleDataEquality.prepare fuel context.checked keyType).mapError
            (fun _ => unsupported node)
          pure ⟨type, index layout comparison.expression base.expression key.expression (reasonAt id)⟩
      | _ => throw (unsupported node)

def leafLowerer (context : Context) : ExpressionLowerer → ExpressionLowerer :=
  fun child fuel source scope id reasonAt => do
    let (node, type) ← readExpression context.checked source id
    match node.form with
    | .constructor .. | .member .. | .proxy .. | .index .. =>
        lowerWithReasons fuel context child source scope id reasonAt
    | .tuple elements =>
        let children ← elements.mapM fun element => child fuel source scope element reasonAt
        let packed := SourceCoreCalls.packArguments children
        SourceCoreBasic.ensureType (.occurrence id.occurrence) type packed.type
        pure ⟨type, packed.expression⟩
    | _ => SourceCoreBasic.lowerExpression fuel source scope id (reasonAt id)

/- The callable policy must use the representation selected by this catalog.
The owning program supplies its authenticated descriptor hooks. -/
def functionPolicy (fuel : Nat) (context : Context)
    (callables : SourceCoreFunctions.CallablePolicy := {}) : SourceCoreFunctions.Policy := {
  callables
  projectType := projectType context.checked
  readExpression := readExpression context.checked
  lowerBinder := lowerBinder context.checked
  lowerRead := lowerRead fuel context
  leafLowerer := leafLowerer context
}

def loopPolicy (context : Context) (lowerExpression : ExpressionLowerer) : SourceCoreLoops.Policy := {
  lowerExpression
  readStatement := readStatement context.checked
  lowerBinder := lowerBinder context.checked
  lowerAssignment := lowerAssignment context.checked
}

structure Certified (context : Context) (environment : Core.Context) where
  lowered : LoweredExpr
  typed : Core.HasType environment lowered.expression (Core.LanguageResult.resultType lowered.type)
    context.checked.catalog.definitions

def lowerChecked (fuel : Nat) (context : Context) (lowerChild : ExpressionLowerer)
    (source : TypedSource) (scope : Scope) (environment : Core.Context) (id : ExpressionId)
    (reasonAt : ExpressionId → Core.Word) : Except Error (Certified context environment) := do
  let lowered ← lowerWithReasons fuel context lowerChild source scope id reasonAt
  if accepted : Core.infer? environment lowered.expression context.checked.catalog.definitions =
      some (Core.LanguageResult.resultType lowered.type) then
    pure ⟨lowered, Core.infer_sound accepted⟩
  else
    match source.lookupExpression? id with
    | some node => throw (unsupported node) | none => throw (.missingExpression id)

theorem construct_hasType {definitions : Core.DataEnvironment} {environment : Core.Context}
    {constructor : Core.ConstructorId} {payload : Core.Ty} {arguments : Core.Expr} (metadata : Core.Word)
    (registered : definitions.lookupConstructorPayloadType? constructor = some (.product .word payload))
    (argumentsTyped : Core.HasType environment arguments (Core.LanguageResult.resultType payload) definitions) :
    Core.HasType environment (construct constructor metadata arguments)
      (Core.LanguageResult.resultType (.namedData constructor.owner)) definitions := by
  obtain ⟨_, owner⟩ := Core.DataEnvironment.lookupConstructorPayloadType?_owner registered
  exact Core.LanguageResult.bind_hasType (.namedData owner) argumentsTyped
    (.inRight .word (.construct registered (.pair .word (.var rfl))))

theorem construct_evaluates {environment : Core.Environment} {before after : Core.Store}
    (constructor : Core.ConstructorId) (metadata : Core.Word) {arguments : Core.Expr} {payload : Core.Value}
    (evaluated : Core.Evaluates environment before arguments (.inRight .word payload) after) :
    Core.Evaluates environment before (construct constructor metadata arguments)
      (.inRight .word (.constructed constructor (.pair (.word metadata) payload))) after :=
  Core.LanguageResult.bind_success _ evaluated (.inRight (.construct (.pair .word (.var rfl))))

theorem construct_failure {environment : Core.Environment} {before after : Core.Store}
    (constructor : Core.ConstructorId) (metadata : Core.Word) {payload : Core.Ty} {arguments : Core.Expr}
    {reason : Core.Word} (evaluated : Core.Evaluates environment before arguments (.inLeft payload (.word reason)) after) :
    Core.Evaluates environment before (construct constructor metadata arguments)
      (.inLeft (.namedData constructor.owner) (.word reason)) after :=
  Core.LanguageResult.bind_failure _ evaluated

theorem readMapping_hasType {definitions : Core.DataEnvironment} {environment : Core.Context}
    {payload : Core.Ty} {reference empty : Core.Expr}
    (referenceTyped : Core.HasType environment reference (Core.OptionalCell.referenceType payload) definitions)
    (emptyTyped : Core.HasType environment empty payload definitions) :
    Core.HasType environment (readMapping reference empty) (Core.LanguageResult.resultType payload) definitions := by
  apply Core.HasType.letE referenceTyped
  apply Core.HasType.caseE (.loadCell (.var rfl))
  · apply Core.HasType.letE
      (by simpa [Core.Context.insertAt] using
        (emptyTyped.weakenAt (inserted := Core.OptionalCell.referenceType payload) 0).weakenAt (inserted := .unit) 0)
    exact .letE (.storeCell (.var rfl) (.inRight .unit (.var rfl))) (.inRight .word (.var rfl))
  · exact .inRight .word (.var rfl)

theorem readMapping_present {environment : Core.Environment} {before after : Core.Store}
    {payload : Core.Ty} {reference empty : Core.Expr} {location : Core.Location} {mapping : Core.Value}
    (referenceEvaluated : Core.Evaluates environment before reference
      (.cellRef (Core.OptionalCell.cellType payload) location) after)
    (present : after.read? location = some (.inRight .unit mapping)) :
    Core.Evaluates environment before (readMapping reference empty) (.inRight .word mapping) after :=
  .letE referenceEvaluated (.caseRight (.loadCell (.var rfl) present) (.inRight (.var rfl)))

theorem readMapping_initializes {environment : Core.Environment} {before middle after : Core.Store}
    {payload : Core.Ty} {reference empty : Core.Expr} {location : Core.Location} {mapping : Core.Value}
    (referenceEvaluated : Core.Evaluates environment before reference
      (.cellRef (Core.OptionalCell.cellType payload) location) middle)
    (absent : middle.read? location = some (.inLeft payload .unit))
    (emptyEvaluated : Core.Evaluates
      (.unit :: .cellRef (Core.OptionalCell.cellType payload) location :: environment) middle
      (empty.weakenAt 0 |>.weakenAt 0) mapping after)
    (stillAbsent : after.read? location = some (.inLeft payload .unit)) :
    Core.Evaluates environment before (readMapping reference empty)
      (.inRight .word mapping) (after.set location (.inRight .unit mapping)) := by
  have bound := (List.getElem?_eq_some_iff.mp stillAbsent).1
  exact .letE referenceEvaluated (.caseLeft (.loadCell (.var rfl) absent)
    (.letE emptyEvaluated (.letE (.storeCell (.var rfl) stillAbsent (.inRight (.var rfl))
      (by simp [Core.Store.write?, bound])) (.inRight (.var rfl)))))

end Solcore.Frontend.SourceCoreCompatibleDataExpressions
