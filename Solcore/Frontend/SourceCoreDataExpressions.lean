import Solcore.Frontend.SourceCoreDataEquality
import Solcore.Frontend.SourceCoreDefaultValue
import Solcore.Frontend.SourceCoreCalls

/-! Data-expression leaves for a caller-owned expression traversal. Children
use the supplied policy, so functions, captures, and control flow keep their
existing lowering. Mapping absence uses the caller's diagnostic token; its
source diagnostic table must classify that token separately from local reads. -/

set_option autoImplicit false

namespace Solcore.Frontend.SourceCoreDataExpressions

open SourceInference
abbrev Scope := SourceCoreBasic.Scope
abbrev Error := SourceCoreBasic.Error
abbrev LoweredExpr := SourceCoreBasic.LoweredExpr
abbrev Checked := SourceCoreDataCatalog.Checked
abbrev ExpressionLowerer := Nat → TypedSource → Scope → ExpressionId →
  (ExpressionId → Core.Word) → Except Error LoweredExpr

/-- Ordinary constructor application after successful left-to-right packing. -/
def construct (constructor : Core.ConstructorId) (arguments : Core.Expr) : Core.Expr :=
  Core.LanguageResult.bind (.namedData constructor.owner) arguments
    (Core.LanguageResult.success (.construct constructor (.var 0)))

def projectPacked (index : Nat) : List Core.Ty → Core.Expr → Core.Expr
  | [], _ => .unit
  | [_], bundle => bundle
  | _ :: second :: rest, bundle =>
    if index = 0 then .first bundle else projectPacked (index - 1) (second :: rest) (.second bundle)

def member (dataType : Core.DataTypeId) (result : Core.Ty) (branches : List Core.Expr)
    (base : Core.Expr) : Core.Expr :=
  Core.LanguageResult.bind result base (.matchData dataType (Core.LanguageResult.resultType result) (.var 0) branches)

/-- Source mapping locals materialize an empty mapping on their first read.
Allocation of the optional binding itself remains the ordinary let behavior. -/
def readMapping (layout : Core.OrderedMapping.Layout) (reference : Core.Expr) : Core.Expr :=
  .letE reference
    (.caseE (.loadCell (.var 0))
      (.letE (.storeCell (.var 1) (.inRight .unit (Core.OrderedMapping.empty layout)))
        (Core.LanguageResult.success (Core.OrderedMapping.empty layout)))
      (Core.LanguageResult.success (.var 0)))

/-- Base and key effects precede comparator initialization and lookup. The
optional library result leaves default/failure policy entirely at this layer. -/
def index (layout : Core.OrderedMapping.Layout) (comparison default base key : Core.Expr)
    (missing : Core.Word) : Core.Expr :=
  Core.LanguageResult.bind layout.valueType base
    (Core.LanguageResult.bind layout.valueType (key.weakenAt 0)
      (Core.LanguageResult.bind layout.valueType
        (Core.OrderedMapping.lookup layout (comparison.weakenAt 0 |>.weakenAt 0) (.var 1) (.var 0))
        (.caseE (.var 0)
          (.caseE (default.weakenAt 0 |>.weakenAt 0 |>.weakenAt 0 |>.weakenAt 0)
            (Core.LanguageResult.failure layout.valueType (.word missing))
            (Core.LanguageResult.success (.var 0)))
          (Core.LanguageResult.success (.var 0)))))

private def project (checked : Checked) (node : ExpressionNode) (type : TypeSystem.Ty) : Except Error Core.Ty :=
  (checked.project type).mapError (fun _ => .unsupportedExpression node.id node.form) |>.map (·.type)

def readExpression (checked : Checked) (source : TypedSource) (id : ExpressionId) :
    Except Error (ExpressionNode × Core.Ty) := do
  if id.occurrence.owner ≠ source.owner then throw (.ownerMismatch source.owner id.occurrence.owner)
  let node ← match source.lookupExpression? id with
    | some node => pure node
    | none => throw (.missingExpression id)
  unless node.requirements.isEmpty do throw (.requirementsPresent id)
  unless node.coercions.isEmpty do throw (.coercionsPresent id)
  pure (node, ← project checked node node.type)

private def memberBranches (checked : Checked) (signatures : ProgramSignatures)
    (node : ExpressionNode) (baseType : TypeSystem.Ty) (result : Core.Ty) (index : Nat) :
    Except Error (Core.DataTypeId × List Core.Expr) := do
  let baseType := SourceCoreDataCatalog.erase baseType
  let (declaration, arguments) ← match SourceCoreDataCatalog.nominalParts baseType with
    | some parts => pure parts
    | none => throw (.unsupportedExpression node.id node.form)
  let signature ← match signatures.dataTypes.filter (fun data => decide (data.id = declaration)) with
    | [signature] => pure signature
    | _ => throw (.unsupportedExpression node.id node.form)
  unless signature.parameters.length = arguments.length && !signature.constructors.isEmpty do
    throw (.unsupportedExpression node.id node.form)
  let dataType ← match checked.catalog.identity? baseType with
    | some id => pure id
    | none => throw (.unsupportedExpression node.id node.form)
  let substitution : TypeSystem.ParameterSubstitution := signature.parameters.zip arguments
  let branches ← signature.constructors.zipIdx.mapM fun (constructor, position) => do
    let payloadTypes := constructor.payloadTypes.map substitution.apply
    let instantiation : DataConstructorInstantiation := {
      constructor := constructor.id, parameterSubstitution := substitution,
      payloadTypes, resultType := baseType
    }
    let resolved ← (checked.catalog.resolveConstructor signatures instantiation).mapError
      (fun _ => SourceCoreBasic.Error.unsupportedExpression node.id node.form)
    unless resolved.owner = dataType && resolved.index = position do
      throw (.unsupportedExpression node.id node.form)
    let selected ← match payloadTypes[index]? with
      | some selected => pure selected
      | none => throw (.unsupportedExpression node.id node.form)
    let selected ← project checked node selected
    SourceCoreBasic.ensureType (.occurrence node.id.occurrence) result selected
    let payloadTypes ← payloadTypes.mapM (project checked node)
    pure (Core.LanguageResult.success (projectPacked index payloadTypes (.var 0)))
  pure (dataType, branches)

/-- Only data forms are handled here. Recursion belongs to `lowerChild`.
Constructor metadata is authenticated against the exact signature catalog. -/
def lowerWithReasons (fuel : Nat) (checked : Checked) (signatures : ProgramSignatures)
    (lowerChild : ExpressionLowerer) (source : TypedSource) (scope : Scope)
    (id : ExpressionId) (reasonAt : ExpressionId → Core.Word) : Except Error LoweredExpr := do
  match fuel with
  | 0 => throw (.traversalExhausted (.occurrence id.occurrence))
  | fuel + 1 =>
    let (node, type) ← readExpression checked source id
    let site := SourceCoreElaboration.ErrorSite.occurrence id.occurrence
    match node.form with
    | .constructor instantiation arguments =>
      unless node.type = instantiation.resultType do throw (.unsupportedExpression id node.form)
      unless arguments.length = instantiation.payloadTypes.length do throw (.unsupportedExpression id node.form)
      let constructor ← (checked.catalog.resolveConstructor signatures instantiation).mapError
        (fun _ => SourceCoreBasic.Error.unsupportedExpression id node.form)
      SourceCoreBasic.ensureType site type (.namedData constructor.owner)
      let lowered ← (arguments.zip instantiation.payloadTypes).mapM fun (argument, expected) => do
        let expected ← project checked node expected
        let argument ← lowerChild fuel source scope argument reasonAt
        SourceCoreBasic.ensureType site expected argument.type
        pure argument
      pure ⟨type, construct constructor (SourceCoreCalls.packArguments lowered).expression⟩
    | .proxy inner =>
      unless node.type = .proxy inner do throw (.unsupportedExpression id node.form)
      let identity ← match checked.catalog.identity? (.proxy inner) with
        | some identity => pure identity
        | none => throw (.unsupportedExpression id node.form)
      SourceCoreBasic.ensureType site type (.namedData identity)
      unless checked.catalog.definitions.lookupConstructorPayloadType? ⟨identity, 0⟩ = some .unit do
        throw (.unsupportedExpression id node.form)
      pure ⟨type, Core.LanguageResult.success (.construct ⟨identity, 0⟩ .unit)⟩
    | .member base _ index =>
      let (baseNode, baseType) ← readExpression checked source base
      let (dataType, branches) ← memberBranches checked signatures node baseNode.type type index
      SourceCoreBasic.ensureType site (.namedData dataType) baseType
      let base ← lowerChild fuel source scope base reasonAt
      SourceCoreBasic.ensureType site baseType base.type
      pure ⟨type, member dataType type branches base.expression⟩
    | .index base key =>
      let (baseNode, baseType) ← readExpression checked source base
      let (keyType, valueType) ← match SourceCoreDataCatalog.erase baseNode.type with
        | .mapping key value => pure (key, value)
        | _ => throw (.unsupportedExpression id node.form)
      let keyProjected ← project checked node keyType
      let valueProjected ← project checked node valueType
      SourceCoreBasic.ensureType site valueProjected type
      let identity ← match checked.catalog.identity? (.mapping keyType valueType) with
        | some identity => pure identity
        | none => throw (.unsupportedExpression id node.form)
      let layout : Core.OrderedMapping.Layout := ⟨keyProjected, valueProjected, identity⟩
      unless checked.catalog.definitions[identity.index]? = some layout.definition do
        throw (.unsupportedExpression id node.form)
      SourceCoreBasic.ensureType site layout.type baseType
      let base ← lowerChild fuel source scope base reasonAt
      let key ← lowerChild fuel source scope key reasonAt
      SourceCoreBasic.ensureType site layout.type base.type
      SourceCoreBasic.ensureType site keyProjected key.type
      let comparison ← (SourceCoreDataEquality.prepare fuel checked keyType).mapError
        (fun _ => SourceCoreBasic.Error.unsupportedExpression id node.form)
      let default ← (SourceCoreDefaultValue.prepare fuel checked valueType).mapError
        (fun _ => SourceCoreBasic.Error.unsupportedExpression id node.form)
      pure ⟨type, SourceCoreDataExpressions.index layout comparison.expression default.expression
        base.expression key.expression (reasonAt id)⟩
    | _ => throw (.unsupportedExpression id node.form)

/-- Adapter matching SourceCoreFunctions' leaf callback: static catalog and
signatures are captured at compile time. -/
def leafLowerer (checked : Checked) (signatures : ProgramSignatures) :
    ExpressionLowerer → ExpressionLowerer := fun child fuel source scope id reasonAt =>
  lowerWithReasons fuel checked signatures child source scope id reasonAt

structure Certified (checked : Checked) (context : Core.Context) where
  lowered : LoweredExpr
  typed : Core.HasType context lowered.expression (Core.LanguageResult.resultType lowered.type)
    checked.catalog.definitions
  deriving Repr

/-- Useful when a caller already knows the complete ambient Core context,
including its globals and administrative binders. Normal entry assembly may
instead use its one final full-body checker. -/
def lowerChecked (fuel : Nat) (checked : Checked) (signatures : ProgramSignatures)
    (lowerChild : ExpressionLowerer) (source : TypedSource) (scope : Scope)
    (context : Core.Context) (id : ExpressionId) (reasonAt : ExpressionId → Core.Word) :
    Except Error (Certified checked context) := do
  let lowered ← lowerWithReasons fuel checked signatures lowerChild source scope id reasonAt
  if accepted : Core.infer? context lowered.expression checked.catalog.definitions =
      some (Core.LanguageResult.resultType lowered.type) then
    pure ⟨lowered, Core.infer_sound accepted⟩
  else
    match source.lookupExpression? id with
    | some node => throw (.unsupportedExpression id node.form)
    | none => throw (.missingExpression id)

theorem construct_hasType {definitions : Core.DataEnvironment} {context : Core.Context}
    {constructor : Core.ConstructorId} {payloadType : Core.Ty} {arguments : Core.Expr}
    (registered : definitions.lookupConstructorPayloadType? constructor = some payloadType)
    (argumentsTyped : Core.HasType context arguments (Core.LanguageResult.resultType payloadType) definitions) :
    Core.HasType context (construct constructor arguments)
      (Core.LanguageResult.resultType (.namedData constructor.owner)) definitions := by
  obtain ⟨definition, owner⟩ := Core.DataEnvironment.lookupConstructorPayloadType?_owner registered
  exact Core.LanguageResult.bind_hasType (.namedData owner) argumentsTyped
    (Core.LanguageResult.success_hasType (.construct registered (.var rfl)))

theorem construct_evaluates {environment : Core.Environment} {before after : Core.Store}
    (constructor : Core.ConstructorId) {arguments : Core.Expr} {payload : Core.Value}
    (evaluated : Core.Evaluates environment before arguments (.inRight .word payload) after) :
    Core.Evaluates environment before (construct constructor arguments)
      (.inRight .word (.constructed constructor payload)) after :=
  Core.LanguageResult.bind_success _ evaluated (.inRight (.construct (.var rfl)))

theorem construct_failure {environment : Core.Environment} {before after : Core.Store}
    (constructor : Core.ConstructorId) {payloadType : Core.Ty} {arguments : Core.Expr} {reason : Core.Word}
    (evaluated : Core.Evaluates environment before arguments (.inLeft payloadType (.word reason)) after) :
    Core.Evaluates environment before (construct constructor arguments)
      (.inLeft (.namedData constructor.owner) (.word reason)) after :=
  Core.LanguageResult.bind_failure _ evaluated

theorem member_hasType {definitions : Core.DataEnvironment} {context : Core.Context}
    {dataType : Core.DataTypeId} {definition : Core.DataDefinition} {result : Core.Ty}
    {branches : List Core.Expr} {base : Core.Expr}
    (registered : definitions.lookupDataType? dataType = some definition)
    (resultWF : result.WellFormed definitions)
    (baseTyped : Core.HasType context base (Core.LanguageResult.resultType (.namedData dataType)) definitions)
    (branchesTyped : Core.BranchesHaveType (.namedData dataType :: context)
      (Core.LanguageResult.resultType result) definition.constructorPayloadTypes branches definitions) :
    Core.HasType context (member dataType result branches base)
      (Core.LanguageResult.resultType result) definitions :=
  Core.LanguageResult.bind_hasType resultWF baseTyped
    (.matchData registered (.sum .word resultWF) (.var rfl) branchesTyped)

theorem member_evaluates {environment : Core.Environment} {before middle after : Core.Store}
    {dataType : Core.DataTypeId} {resultType : Core.Ty} {constructor : Core.ConstructorId}
    {branches : List Core.Expr} {base branch : Core.Expr} {payload result : Core.Value}
    (baseEvaluated : Core.Evaluates environment before base
      (.inRight .word (.constructed constructor payload)) middle)
    (owner : constructor.owner = dataType)
    (selected : branches[constructor.index]? = some branch)
    (branchEvaluated : Core.Evaluates (payload :: .constructed constructor payload :: environment)
      middle branch result after) :
    Core.Evaluates environment before (member dataType resultType branches base) result after :=
  Core.LanguageResult.bind_success _ baseEvaluated
    (.matchData (.var rfl) owner selected branchEvaluated)

theorem readMapping_hasType {definitions : Core.DataEnvironment} {context : Core.Context}
    {layout : Core.OrderedMapping.Layout} {reference : Core.Expr}
    (registered : layout.Registered definitions)
    (referenceTyped : Core.HasType context reference (Core.OptionalCell.referenceType layout.type) definitions) :
    Core.HasType context (readMapping layout reference) (Core.LanguageResult.resultType layout.type) definitions :=
  .letE referenceTyped (.caseE (.loadCell (.var rfl))
    (.letE (.storeCell (.var rfl) (.inRight .unit (Core.OrderedMapping.empty_hasType registered _)))
      (Core.LanguageResult.success_hasType (Core.OrderedMapping.empty_hasType registered _)))
    (Core.LanguageResult.success_hasType (.var rfl)))

theorem readMapping_present {environment : Core.Environment} {before after : Core.Store}
    (layout : Core.OrderedMapping.Layout) {reference : Core.Expr} {location : Core.Location} {mapping : Core.Value}
    (referenceEvaluated : Core.Evaluates environment before reference
      (.cellRef (Core.OptionalCell.cellType layout.type) location) after)
    (present : after.read? location = some (.inRight .unit mapping)) :
    Core.Evaluates environment before (readMapping layout reference) (.inRight .word mapping) after :=
  .letE referenceEvaluated (.caseRight (.loadCell (.var rfl) present) (.inRight (.var rfl)))

theorem readMapping_initializes {environment : Core.Environment} {before middle : Core.Store}
    (layout : Core.OrderedMapping.Layout) {reference : Core.Expr} {location : Core.Location}
    (referenceEvaluated : Core.Evaluates environment before reference
      (.cellRef (Core.OptionalCell.cellType layout.type) location) middle)
    (absent : middle.read? location = some (.inLeft layout.type .unit)) :
    Core.Evaluates environment before (readMapping layout reference)
      (.inRight .word (Core.OrderedMapping.encode layout []))
      (middle.set location (.inRight .unit (Core.OrderedMapping.encode layout []))) := by
  have bound := (List.getElem?_eq_some_iff.mp absent).1
  exact .letE referenceEvaluated (.caseLeft (.loadCell (.var rfl) absent)
    (.letE (.storeCell (.var rfl) absent (.inRight (.construct .unit))
      (by simp [Core.Store.write?, bound, Core.OrderedMapping.encode])) (.inRight (.construct .unit))))

theorem index_hasType {definitions : Core.DataEnvironment} {context : Core.Context}
    {layout : Core.OrderedMapping.Layout} {comparison default base key : Core.Expr} (missing : Core.Word)
    (registered : layout.Registered definitions)
    (comparisonTyped : Core.HasType context comparison layout.comparisonType definitions)
    (defaultTyped : Core.HasType context default (.sum .unit layout.valueType) definitions)
    (baseTyped : Core.HasType context base (Core.LanguageResult.resultType layout.type) definitions)
    (keyTyped : Core.HasType context key (Core.LanguageResult.resultType layout.keyType) definitions) :
    Core.HasType context (index layout comparison default base key missing)
      (Core.LanguageResult.resultType layout.valueType) definitions := by
  apply Core.LanguageResult.bind_hasType registered.valueWellFormed baseTyped
  apply Core.LanguageResult.bind_hasType registered.valueWellFormed
  · simpa [Core.Context.insertAt] using keyTyped.weakenAt (inserted := layout.type) 0
  · apply Core.LanguageResult.bind_hasType registered.valueWellFormed
    · apply Core.OrderedMapping.lookup_hasType registered
      · have outer := comparisonTyped.weakenAt (inserted := layout.type) 0
        simpa [Core.Context.insertAt] using outer.weakenAt (inserted := layout.keyType) 0
      · exact .var rfl
      · exact .var rfl
    · apply Core.HasType.caseE (.var rfl)
      · apply Core.HasType.caseE
        · have first := defaultTyped.weakenAt (inserted := layout.type) 0
          have second := first.weakenAt (inserted := layout.keyType) 0
          have third := second.weakenAt (inserted := layout.lookupResult) 0
          simpa [Core.Context.insertAt] using third.weakenAt (inserted := .unit) 0
        · exact Core.LanguageResult.failure_hasType registered.valueWellFormed .word
        · exact Core.LanguageResult.success_hasType (.var rfl)
      · exact Core.LanguageResult.success_hasType (.var rfl)

theorem index_base_failure {environment : Core.Environment} {before after : Core.Store}
    (layout : Core.OrderedMapping.Layout) {comparison default base key : Core.Expr} (missing reason : Core.Word)
    (failed : Core.Evaluates environment before base (.inLeft layout.type (.word reason)) after) :
    Core.Evaluates environment before (index layout comparison default base key missing)
      (.inLeft layout.valueType (.word reason)) after :=
  Core.LanguageResult.bind_failure _ failed

theorem index_key_failure {environment : Core.Environment} {before middle after : Core.Store}
    (layout : Core.OrderedMapping.Layout) {comparison default base key : Core.Expr} (missing reason : Core.Word)
    {mapping : Core.Value}
    (baseEvaluated : Core.Evaluates environment before base (.inRight .word mapping) middle)
    (keyFailed : Core.Evaluates (mapping :: environment) middle (key.weakenAt 0)
      (.inLeft layout.keyType (.word reason)) after) :
    Core.Evaluates environment before (index layout comparison default base key missing)
      (.inLeft layout.valueType (.word reason)) after :=
  Core.LanguageResult.bind_success _ baseEvaluated (Core.LanguageResult.bind_failure _ keyFailed)

end Solcore.Frontend.SourceCoreDataExpressions
