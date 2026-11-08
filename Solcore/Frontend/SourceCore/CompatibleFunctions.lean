import Solcore.Frontend.SourceCore.Compatible
import Solcore.Frontend.SourceCore.Lowering
import Solcore.Core.Internal.WordComparisons
import Solcore.Core.Internal.ConventionLaws
import Solcore.Frontend.SourceCore.GeneralFunctions
import Solcore.Frontend.Internal.RuntimeValues

/-!
# Compatible functions

Checked data patterns, accepted public inputs and cached functions of the source-compatible profile.
Main declarations: `SourceCoreCompatibleFunctions`, `SourceCoreCompatibleInputs`,
`SourceCoreCompatibleDataMatches`.
-/

section
-- leanmerge: from Solcore.Frontend.SourceCoreCompatibleDataMatches
/-! Checked data patterns compiled to ordinary Core functions and sums. Pattern
attempts are pure: their successful result is a packed binder-value bundle.
Only a fully matched arm allocates the source binders. The scrutinee's hidden
source cell is allocated once, before testing the first arm. The callback owns
nested statement control and the surrounding compiler checks the full body.
Raw constructor IDs must match before any child matcher runs. A supplied
source allocator marks the hidden scrutinee and only the successful arm's
binders. Pure matcher checking uses the caller's actual ambient definitions.
Groups are transparent at the root and within tuple and constructor patterns. -/

set_option autoImplicit false

namespace Solcore.Frontend.SourceCoreCompatibleDataMatches

open SourceInference
abbrev Scope := SourceCoreBasic.Scope
abbrev Error := SourceCoreBasic.Error
abbrev Checked := SourceCoreCompatibleCatalog.Checked
abbrev ExpressionLowerer := SourceCoreDataExpressions.ExpressionLowerer
abbrev BodyLowerer := Nat → TypedSource → Scope → List StatementId → Core.Ty →
  (ExpressionId → Core.Word) → Core.Word → Except Error Core.Expr

structure Context where
  values : SourceCoreCompatibleValues.Context
  solvedRequirements : List SolvedRequirement
  sourceCells : Option SourceCoreSourceCells.Allocator := none
  ambientDefinitions : Option Core.DataEnvironment := none

def Context.checked (context : Context) : Checked := context.values.checked
def Context.signatures (context : Context) : ProgramSignatures := context.checked.signatures
def Context.definitions (context : Context) : Core.DataEnvironment :=
  context.ambientDefinitions.getD context.checked.catalog.definitions

private def invalid : Error := .callPreparation .invalidPatternMetadata

/-- Unit/single/right-product representation of source-ordered binding values. -/
def bundleType : List Core.Ty → Core.Ty
  | [] => .unit
  | [type] => type
  | type :: rest => .product type (bundleType rest)

def bundle : List Core.Expr → Core.Expr
  | [] => .unit
  | [value] => value
  | value :: rest => .pair value (bundle rest)

structure Pattern where
  type : Core.Ty
  bindings : List (TypedBinder × Core.Ty)
  requirements : List RequirementId
  matcher : Core.Expr
  deriving Repr

def Pattern.bindingTypes (pattern : Pattern) : List Core.Ty := pattern.bindings.map Prod.snd
def Pattern.resultType (pattern : Pattern) : Core.Ty := .sum .unit (bundleType pattern.bindingTypes)
def Pattern.functionType (pattern : Pattern) : Core.Ty := .function pattern.type pattern.resultType

/-- Every temporary successful child bundle is lexical only. Failed children
return absence immediately and never evaluate the later matcher applications. -/
def matchChildren (outputType : Core.Ty) : List Pattern → List Core.Expr → List Core.Expr → Core.Expr
  | [], _, accumulated => .inRight .unit (bundle accumulated)
  | pattern :: rest, value :: values, accumulated =>
      .caseE (.apply pattern.matcher value) (.inLeft outputType .unit)
        (matchChildren outputType rest (values.map (·.weakenAt 0))
          (accumulated.map (·.weakenAt 0) ++ pattern.bindingTypes.zipIdx.map
            (fun (_, index) => SourceCoreDataExpressions.projectPacked index pattern.bindingTypes (.var 0))))
  | _ :: _, [], _ => .inLeft outputType .unit

def projected (context : Context) (source : TypedSource) (type : TypeSystem.Ty) : Except Error Core.Ty :=
  SourceCoreCompatibleDataExpressions.projectType context.checked (.declaration source.owner) type

def unpackTypes : Nat → TypeSystem.Ty → Option (List TypeSystem.Ty)
  | 0, type => if type = .unit then some [] else none
  | 1, type => some [type]
  | count + 2, .product left right => do pure (left :: (← unpackTypes (count + 1) right))
  | _ + 2, _ => none

def childValues (types : List Core.Ty) : List Core.Expr :=
  types.zipIdx.map fun (_, index) => SourceCoreDataExpressions.projectPacked index types (.var 0)

/-- A native constructor tag authenticates the representation shape. This
guard additionally distinguishes the exact retained source instantiation. -/
def rawConstructor (metadata : Core.Word) (outputType : Core.Ty) (children : Core.Expr) : Core.Expr :=
  .ifE (.binary .wordEq (.first (.var 0)) (.word metadata)) children (.inLeft outputType .unit)

theorem rawConstructor_matches {environment : Core.Environment} {before after : Core.Store}
    {metadata : Core.Word} {payload result : Core.Value} {outputType : Core.Ty} {children : Core.Expr}
    (evaluated : Core.Evaluates (.pair (.word metadata) payload :: environment) before children result after) :
    Core.Evaluates (.pair (.word metadata) payload :: environment) before
      (rawConstructor metadata outputType children) result after :=
  .ifTrue (Core.Evaluates.wordEq_eq rfl (.first (.var rfl)) .word) evaluated

theorem rawConstructor_misses (environment : Core.Environment) (store : Core.Store)
    (actual expected : Core.Word) (different : actual ≠ expected) (payload : Core.Value)
    (outputType : Core.Ty) (children : Core.Expr) :
    Core.Evaluates (.pair (.word actual) payload :: environment) store
      (rawConstructor expected outputType children) (.inLeft outputType .unit) store :=
  .ifFalse (Core.Evaluates.wordEq_ne different (.first (.var rfl)) .word) (.inLeft .unit)

/-- The shared literal validator consumes metadata only. Its temporary node
contains the expected type from the authenticated pattern tree, this literal's
own requirement, and the original literal spelling. `compilePattern` checks the
whole pattern's exact ordered requirement list independently. No expression
occurrence membership is inferred from this diagnostic carrier. -/
def literalMatcher (context : Context) (site : StatementId) (span : Syntax.SourceSpan)
    (type : TypeSystem.Ty) (literal : Syntax.CoreLiteralValue) (resolution : IntegerLiteralResolution) :
    Except Error Core.Expr := do
  let node : ExpressionNode := {
    id := ⟨site.occurrence⟩, span, type, form := .integerLiteral literal resolution,
    requirements := [resolution.requirement]
  }
  let (coreType, equal) ← match type with
    | .constructor (.builtin .word) => do
      let valid ← (SourceCoreElaboration.validateWordIntegerLiteral context.solvedRequirements node literal resolution)
        |>.mapError SourceCoreBasic.Error.literalEvidence
      pure (Core.Ty.word, Core.Expr.binary .wordEq (.var 0) (.word valid.value))
    | .constructor (.builtin .integer) => do
      let valid ← (SourceCoreElaboration.validateNativeIntegerLiteral context.solvedRequirements node literal resolution)
        |>.mapError SourceCoreBasic.Error.literalEvidence
      pure (Core.Ty.integer, Core.Expr.binary .integerEq (.var 0) (.integer valid.value))
    | _ => throw invalid
  pure (.lambda coreType (.sum .unit .unit)
    (.ifE equal (.inRight .unit .unit) (.inLeft .unit .unit)))

mutual
  def compileOne (context : Context) (source : TypedSource) (site : StatementId)
      (span : Syntax.SourceSpan) (scope : Scope) : Nat → TypeSystem.Ty → List MatchPatternInstruction →
        Except Error (Pattern × List MatchPatternInstruction)
    | 0, _, _ => throw (.traversalExhausted (.occurrence site.occurrence))
    | _ + 1, _, [] => throw invalid
    | fuel + 1, expected, instruction :: rest => do
      let type ← projected context source expected
      match instruction with
      | .wildcard => pure (⟨type, [], [], .lambda type (.sum .unit .unit) (.inRight .unit .unit)⟩, rest)
      | .binder binder =>
          unless binder.scheme.body = expected do throw invalid
          let actual ← SourceCoreCompatibleDataExpressions.lowerBinder context.checked source scope binder
          SourceCoreBasic.ensureType (.binder binder.id) type actual
          pure (⟨type, [(binder, type)], [], .lambda type (.sum .unit type) (.inRight .unit (.var 0))⟩, rest)
      | .integerLiteral literal resolution =>
          let matcher ← literalMatcher context site span expected literal resolution
          pure (⟨type, [], [resolution.requirement], matcher⟩, rest)
      | .tuple count =>
          let types ← match unpackTypes count expected with
            | some types => pure types
            | none => throw invalid
          let (children, rest) ← compileMany context source site span scope fuel types rest
          let bindings := children.flatMap (·.bindings)
          let outputType := bundleType (bindings.map Prod.snd)
          let types ← types.mapM (projected context source)
          pure (⟨type, bindings, children.flatMap (·.requirements),
            .lambda type (.sum .unit outputType)
              (matchChildren outputType children (childValues types) [])⟩, rest)
      | .constructor instantiation arity =>
          unless instantiation.resultType = expected && arity = instantiation.payloadTypes.length do throw invalid
          let constructor ← (context.checked.resolveConstructor instantiation)
            |>.mapError (fun _ => invalid)
          SourceCoreBasic.ensureType (.occurrence site.occurrence) type (.namedData constructor.owner)
          let rawId ← match context.values.registry.id? (.constructor instantiation) with
            | some id => pure id | none => throw invalid
          let (children, rest) ← compileMany context source site span scope fuel instantiation.payloadTypes rest
          let bindings := children.flatMap (·.bindings)
          let outputType := bundleType (bindings.map Prod.snd)
          let payloadTypes ← instantiation.payloadTypes.mapM (projected context source)
          let definition ← match context.checked.catalog.definitions[constructor.owner.index]? with
            | some definition => pure definition
            | none => throw invalid
          let branches := definition.constructorPayloadTypes.zipIdx.map fun (_, index) =>
            if index = constructor.index then
              rawConstructor rawId outputType
                (matchChildren outputType children
                  (payloadTypes.zipIdx.map fun (_, index) =>
                    SourceCoreDataExpressions.projectPacked index payloadTypes (.second (.var 0))) [])
            else .inLeft outputType .unit
          pure (⟨type, bindings, children.flatMap (·.requirements),
            .lambda type (.sum .unit outputType)
              (.matchData constructor.owner (.sum .unit outputType) (.var 0) branches)⟩, rest)

  def compileMany (context : Context) (source : TypedSource) (site : StatementId)
      (span : Syntax.SourceSpan) (scope : Scope) : Nat → List TypeSystem.Ty → List MatchPatternInstruction →
        Except Error (List Pattern × List MatchPatternInstruction)
    | _, [], instructions => pure ([], instructions)
    | 0, _ :: _, _ => throw (.traversalExhausted (.occurrence site.occurrence))
    | fuel + 1, type :: types, instructions => do
        let (head, rest) ← compileOne context source site span scope fuel type instructions
        let (tail, rest) ← compileMany context source site span scope fuel types rest
        pure (head :: tail, rest)
end

def rootInstructions (context : Context) : MatchPatternSource → MatchPatternResolution →
    Except Error (List MatchPatternInstruction)
  | .wildcard _ _, .wildcard => pure [.wildcard]
  | .integerLiteral _ literal, .integerLiteral source resolution => do
      unless literal.value = source do throw invalid
      pure [.integerLiteral source resolution]
  | .binder _ name, .binder binder => do
      unless binder.name = name do throw invalid
      pure [.binder binder]
  | .constructor _ _ _ name count, .constructor instantiation instructions => do
      let signatures := context.signatures.dataTypes.filter (fun signature =>
        decide (signature.id = instantiation.constructor.dataType))
      let [signature] := signatures | throw invalid
      let [constructor] := signature.constructors.filter (fun constructor =>
        decide (constructor.id = instantiation.constructor)) | throw invalid
      unless constructor.name = name do throw invalid
      pure (.constructor instantiation count :: instructions)
  | .tuple _ count, .tuple instructions => pure (.tuple count :: instructions)
  | .group _ inner, resolution => rootInstructions context inner resolution
  | _, _ => throw invalid

structure CertifiedPattern (definitions : Core.DataEnvironment) where
  pattern : Pattern
  typed : Core.HasType [] pattern.matcher pattern.functionType definitions
  deriving Repr

/-- Authenticates the retained source root, complete nested prefix stream,
source-order requirements, lexical binder metadata, and generated Core type. -/
def compilePattern (context : Context) (fuel : Nat) (source : TypedSource) (scope : Scope)
    (site : StatementId) (span : Syntax.SourceSpan) (expected : TypeSystem.Ty)
    (pattern : TypedMatchPattern) : Except Error (CertifiedPattern context.definitions) := do
  if site.occurrence.owner ≠ source.owner then throw (.ownerMismatch source.owner site.occurrence.owner)
  unless pattern.type = expected do throw invalid
  let instructions ← rootInstructions context pattern.source pattern.resolution
  let (compiled, rest) ← compileOne context source site span scope fuel expected instructions
  unless rest.isEmpty && compiled.requirements = pattern.requirements do throw invalid
  unless (compiled.bindings.map (·.1.id)).Nodup && (compiled.bindings.map (·.1.name)).Nodup do throw invalid
  if accepted : Core.infer? [] compiled.matcher context.definitions = some compiled.functionType then
    pure ⟨compiled, Core.infer_sound accepted⟩
  else throw invalid

/-- The raw successful bundle remains after the newly allocated source cells.
`body` already has those source cells in scope. -/
def bindArm (bindings : List (TypedBinder × Core.Ty)) (outputType : Core.Ty) (body : Core.Expr) : Core.Expr :=
  let types := bindings.map Prod.snd
  bindings.zipIdx.foldr (fun (binding, index) continuation =>
    Core.LocalSequence.letInitialized outputType binding.2
      (Core.LanguageResult.success (SourceCoreDataExpressions.projectPacked index types (.var index))) continuation)
    (body.weakenAt bindings.length)

/-- Select an arm from a pure matcher result. Both continuations are lowered
before inserting the matcher-result binder. -/
def attempt (pattern : Pattern) (outputType : Core.Ty) (body next : Core.Expr) : Core.Expr :=
  .caseE (.apply pattern.matcher (.var 0)) (next.weakenAt 0)
    (bindArm pattern.bindings outputType (body.weakenAt pattern.bindings.length))

theorem wildcard_evaluates (environment : Core.Environment) (store : Core.Store)
    (type : Core.Ty) (value : Core.Value) :
    Core.Evaluates (value :: environment) store
      (.apply (.lambda type (.sum .unit .unit) (.inRight .unit .unit)) (.var 0))
      (.inRight .unit .unit) store :=
  .apply .lambda (.var rfl) (.inRight .unit)

theorem binder_evaluates (environment : Core.Environment) (store : Core.Store)
    (type : Core.Ty) (value : Core.Value) :
    Core.Evaluates (value :: environment) store
      (.apply (.lambda type (.sum .unit type) (.inRight .unit (.var 0))) (.var 0))
      (.inRight .unit value) store :=
  .apply .lambda (.var rfl) (.inRight (.var rfl))

/-- A failed pattern returns immediately. No binding allocator, later pattern,
or selected-arm body occurs among the premises. -/
theorem matchChildren_failure {environment : Core.Environment} {store : Core.Store}
    {pattern : Pattern} {value : Core.Expr} (outputType : Core.Ty)
    (rest : List Pattern) (values accumulated : List Core.Expr)
    (failed : Core.Evaluates environment store (.apply pattern.matcher value)
      (.inLeft (bundleType pattern.bindingTypes) .unit) store) :
    Core.Evaluates environment store
      (matchChildren outputType (pattern :: rest) (value :: values) accumulated)
      (.inLeft outputType .unit) store :=
  .caseLeft failed (.inLeft .unit)

/-- Failure preserves the exact matcher store; only the next case executes. -/
theorem attempt_failure {environment : Core.Environment} {store finalStore : Core.Store}
    {pattern : Pattern} {outputType : Core.Ty} {body next : Core.Expr} {result : Core.Value}
    (failed : Core.Evaluates environment store (.apply pattern.matcher (.var 0))
      (.inLeft (bundleType pattern.bindingTypes) .unit) store)
    (nextEvaluation : Core.Evaluates (.unit :: environment) store (next.weakenAt 0) result finalStore) :
    Core.Evaluates environment store (attempt pattern outputType body next) result finalStore :=
  .caseLeft failed nextEvaluation

/-- Success executes the source-order binding allocator once and skips every
later arm. The body premise exposes the actual bundle and store boundary. -/
theorem attempt_success {environment : Core.Environment} {store finalStore : Core.Store}
    {pattern : Pattern} {outputType : Core.Ty} {body next : Core.Expr} {bindings result : Core.Value}
    (matched : Core.Evaluates environment store (.apply pattern.matcher (.var 0))
      (.inRight .unit bindings) store)
    (bodyEvaluation : Core.Evaluates (bindings :: environment) store
      (bindArm pattern.bindings outputType (body.weakenAt pattern.bindings.length)) result finalStore) :
    Core.Evaluates environment store (attempt pattern outputType body next) result finalStore :=
  .caseRight matched bodyEvaluation

/-- `scope` includes the hidden source reference. Successful child bundles
and the unpacked scrutinee are skipped when capturing source references. -/
def bindArmWithAllocator (context : Context) (source : TypedSource) (scope : Scope)
    (bindings : List (TypedBinder × Core.Ty)) (outputType : Core.Ty) (body : Core.Expr) : Except Error Core.Expr :=
  let types := bindings.map Prod.snd
  bindings.zipIdx.foldrM (fun ((binder, type), index) continuation =>
    let prior := (bindings.take index).reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope
    let references := Core.Renaming.comp (Core.Renaming.insertion (index + 1))
      (Core.Renaming.insertion index)
    SourceCoreSourceCells.letInitialized context.sourceCells source prior references binder outputType type
      (Core.LanguageResult.success (SourceCoreDataExpressions.projectPacked index types (.var index))) continuation)
    (body.weakenAt bindings.length)

/-- Lower one match statement to the caller's flow envelope. A surrounding
sequence discharges the match scope before evaluating its continuation. -/
def lowerWithReasons (context : Context) (lowerExpression : ExpressionLowerer) (lowerBody : BodyLowerer)
    (fuel : Nat) (source : TypedSource) (scope : Scope) (id : StatementId)
    (resolution : MatchResolution) (resultType : Core.Ty) (reasonAt : ExpressionId → Core.Word)
    (internalReason : Core.Word) : Except Error Core.Expr := do
  match fuel with
  | 0 => throw (.traversalExhausted (.occurrence id.occurrence))
  | fuel + 1 =>
    let (node, statementType) ← SourceCoreCompatibleDataExpressions.readStatement context.checked source id
    unless statementType = .unit || statementType = resultType do throw invalid
    unless node.form = .matchWith resolution do throw invalid
    unless resolution.requirements = resolution.cases.flatMap (·.pattern.requirements) do throw invalid
    if resolution.hiddenScrutinee.owner ≠ source.owner then
      throw (.ownerMismatch source.owner resolution.hiddenScrutinee.owner)
    if scope.any (fun entry => decide (entry.1 = resolution.hiddenScrutinee)) then
      throw (.duplicateBinding resolution.hiddenScrutinee)
    if resolution.scrutinee.occurrence.owner ≠ source.owner then
      throw (.ownerMismatch source.owner resolution.scrutinee.occurrence.owner)
    let scrutineeNode ← match source.lookupExpression? resolution.scrutinee with
      | some node => pure node
      | none => throw (.missingExpression resolution.scrutinee)
    let type ← projected context source scrutineeNode.type
    let scrutinee ← lowerExpression fuel source scope resolution.scrutinee reasonAt
    SourceCoreBasic.ensureType (.occurrence resolution.scrutinee.occurrence) type scrutinee.type
    let hiddenScope := (resolution.hiddenScrutinee, type) :: scope
    let arms ← resolution.cases.mapM fun arm => do
      let pattern ← compilePattern context fuel source hiddenScope id arm.span scrutineeNode.type arm.pattern
      let armScope := pattern.pattern.bindings.foldl (fun scope binding => (binding.1.id, binding.2) :: scope) hiddenScope
      let body ← lowerBody fuel source armScope arm.body resultType reasonAt internalReason
      pure (pattern.pattern, body)
    let fallback ← match resolution.defaultBody with
      | none => pure (Core.LocalLoop.fallthrough resultType)
      | some body => lowerBody fuel source hiddenScope body resultType reasonAt internalReason
    let controlType := Core.LocalLoop.controlType resultType
    let branches ← arms.foldrM (fun (pattern, body) next => do
      let body ← bindArmWithAllocator context source hiddenScope pattern.bindings controlType
        (body.weakenAt pattern.bindings.length)
      pure (.caseE (.apply pattern.matcher (.var 0)) (next.weakenAt 0) body))
      (fallback.weakenAt 0)
    let hiddenBinder : TypedBinder := {
      id := resolution.hiddenScrutinee, name := "", scheme := ⟨[], SourceCoreRawMetadata.runtimeType scrutineeNode.type⟩,
      span := some node.span
    }
    SourceCoreSourceCells.letInitialized context.sourceCells source scope Core.Renaming.id hiddenBinder
      controlType type scrutinee.expression
      (.caseE (.loadCell (.var 0)) (Core.LanguageResult.failure controlType (.word internalReason)) branches)

structure Certified (context : Context) (environment : Core.Context) (resultType : Core.Ty) where
  expression : Core.Expr
  typed : Core.HasType environment expression (Core.LocalLoop.resultType resultType) context.definitions
  deriving Repr

def lowerChecked (context : Context) (lowerExpression : ExpressionLowerer) (lowerBody : BodyLowerer)
    (fuel : Nat) (source : TypedSource) (scope : Scope) (environment : Core.Context) (id : StatementId)
    (resolution : MatchResolution) (resultType : Core.Ty) (reasonAt : ExpressionId → Core.Word)
    (internalReason : Core.Word) : Except Error (Certified context environment resultType) := do
  let expression ← lowerWithReasons context lowerExpression lowerBody fuel source scope id resolution resultType reasonAt internalReason
  if accepted : Core.infer? environment expression context.definitions = some (Core.LocalLoop.resultType resultType) then
    pure ⟨expression, Core.infer_sound accepted⟩
  else throw invalid

/-- A representation factory for the shared statement traversal. Missing
default providers come from the compatible range inventory. The caller keeps
its registry decoder and any later diagnostic inventories alongside it. -/
def loopPolicy (values : SourceCoreCompatibleValues.Context)
    (solvedRequirements : List SolvedRequirement)
    (assignments : SourceCoreAssignmentFaultSites.Table)
    (diagnostics : SourceCoreDataPlaceFaultSites.Program)
    (owner : SourceSpecialization.SpecializationKey) (expression : ExpressionLowerer)
    (sourceCells : Option SourceCoreSourceCells.Allocator := none)
    (ambientDefinitions : Option Core.DataEnvironment := none) : SourceCoreLoops.Policy := {
  lowerExpression := expression
  sourceCells
  readStatement := SourceCoreCompatibleDataExpressions.readStatement values.checked
  lowerBinder := SourceCoreCompatibleDataExpressions.lowerBinder values.checked
  lowerAssignment := SourceCoreCompatibleDataExpressions.lowerAssignment values.checked
  lowerMatch := some (lowerWithReasons ⟨values, solvedRequirements, sourceCells, ambientDefinitions⟩)
  assignEqual := some fun expression fuel source scope site assignment rhs output next reasonAt =>
    SourceCoreCompatibleDataPlaces.lower values values.checked.signatures expression fuel source scope site assignment
      .equal (some rhs) output next reasonAt
      (diagnostics.placeReason owner site assignment.target.root none) Core.Word.zero
      (fun type => diagnostics.placeReason owner site assignment.target.root (some type))
  assignValue := some fun expression fuel source scope site assignment operator rhs output next reasonAt =>
    SourceCoreCompatibleDataPlaces.lower values values.checked.signatures expression fuel source scope site assignment
      operator (some rhs) output next reasonAt
      (diagnostics.placeReason owner site assignment.target.root none)
      (assignments.reasonAt site assignment.target.root (.value operator))
      (fun type => diagnostics.placeReason owner site assignment.target.root (some type))
  assignBitNotWithExpression := some fun expression fuel source scope site assignment output next reasonAt =>
    SourceCoreCompatibleDataPlaces.lower values values.checked.signatures expression fuel source scope site assignment
      .equal none output next reasonAt
      (diagnostics.placeReason owner site assignment.target.root none)
      (assignments.reasonAt site assignment.target.root .bitNot)
      (fun type => diagnostics.placeReason owner site assignment.target.root (some type))
}

end Solcore.Frontend.SourceCoreCompatibleDataMatches
end

section
-- leanmerge: from Solcore.Frontend.SourceCoreCompatibleInputs
/-! Accepted public source arguments become ordinary Core expressions beneath
already installed global references. Data keeps the compatible codec and raw
registry; named functions read the cached global cell, while builtins use the
existing native template. Neither path evaluates or walks a source body.

The source validator runs before encoding, with its original plan, budget and
error order. Closure/instantiated values remain rejected at every depth. The
owning artifact supplies the actual cached global code and initialized store;
this adapter certifies expressions under those reference types, not arbitrary
host-created closure code or a foreign artifact's globals. -/

set_option autoImplicit false
namespace Solcore.Frontend.SourceCoreCompatibleInputs
open SourceInference TypeSystem
abbrev Values := SourceCoreCompatibleValues.Context
abbrev Extended := SourceCoreCompatibleValues.Extended
abbrev SourceValue := SourceTypedRuntime.Value
abbrev Key := SourceSpecialization.SpecializationKey
abbrev Plan := SourceSpecializationWorklist.Plan
abbrev Signature := SourceCoreCalls.Signature
abbrev Table := SourceCoreStageCodebook.Table
abbrev Lowered := SourceCoreBasic.LoweredExpr

inductive Error where
  | source (error : SourceCompilationPlan.Error)
  | catalog (error : SourceCoreCompatibleCatalog.Error)
  | metadata (error : SourceCoreRawMetadata.Error)
  | codec (error : SourceCoreCompatibleValues.Error)
  | globalsOrderMismatch
  | globalTypeMismatch (key : Key)
  | missingGlobal (key : Key)
  | missingContract (origin : SourceCoreStageCodebook.Origin)
  | contractMismatch (origin : SourceCoreStageCodebook.Origin)
  | identitySpaceExhausted
  | payloadCountMismatch
  | unsupportedValue
  | exhausted
  | checkFailed (expected : Core.Ty)
  deriving Repr

structure Context where private mk ::
  values : Values
  /-- Prepared runtime frontier owning all cached global slots. -/
  plan : Plan
  /-- The old public boundary validates against this plan before preparing any
  additional runtime evidence frontier. -/
  validationPlan : Plan
  globals : List Signature
  codebook : Option Table
  definitions : Core.DataEnvironment
  internalReason : Core.Word

def Context.coreContext (context : Context) : Core.Context := context.globals.map (·.referenceType)

private def native (values : Values) (type : Ty) : Except Error Core.Ty :=
  (values.checked.project type).map (·.type) |>.mapError Error.catalog

private def descriptor (table : Table) (origin : SourceCoreStageCodebook.Origin) : Except Error Core.Word :=
  match table.idAt? origin with
  | some id => pure id | none => throw (.missingContract origin)

/-- Check slot order, projected signatures and retained named staging flags
once. The artifact has already authenticated and compiled its executable plan. -/
private def validatePrepared (values : Values) (plan : Plan) (globals : List Signature)
    (codebook : Option Table) : Except Error Unit := do
  unless globals.map (·.key) = plan.specializations.reverse.map (·.key) do throw .globalsOrderMismatch
  for signature in globals do
    let specialized ← (SourceCompilationPlan.exactSpecialization plan signature.key).mapError Error.source
    let (parameter, result) ← match specialized.function.type with
      | .function parameter result => pure (parameter, result)
      | _ => throw (.globalTypeMismatch signature.key)
    let projectedParameter ← native values parameter
    let projectedResult ← native values result
    unless signature.parameterType = projectedParameter && signature.resultType = projectedResult do
      throw (.globalTypeMismatch signature.key)
    if values.checked.catalog.callableContracts then
      let table ← match codebook with
        | some table => pure table | none => throw (.missingContract (.named signature.key))
      let id ← descriptor table (.named signature.key)
      let entry ← match table.entryAt? id with
        | some entry => pure entry | none => throw (.missingContract (.named signature.key))
      let contract ← match entry.contract with
        | some contract => pure contract | none => throw (.contractMismatch (.named signature.key))
      unless contract.owner = signature.key &&
          contract.parameters = specialized.function.typedBody.inputs &&
          contract.stagedResult = (specialized.function.returnComptime ||
            SourceCompilationPlan.sourceTypeIsComptimeOnly specialized.function.inferredBodyType) &&
          entry.parameterCount = specialized.function.typedBody.inputs.length do
        throw (.contractMismatch (.named signature.key))
  pure ()

def prepare (values : Values) (plan : Plan) (globals : List Signature) (codebook : Option Table)
    (definitions : Core.DataEnvironment) (internalReason : Core.Word := Core.Word.zero)
    (validationPlan : Option Plan := none) : Except Error Context :=
  match validatePrepared values plan globals codebook with
  | .error error => .error error
  | .ok _ => .ok (.mk values plan (validationPlan.getD plan) globals codebook definitions internalReason)

/-- Preparing cached globals retains the exact compatible value owner. -/
theorem prepare_values {values : Values} {plan : Plan} {globals : List Signature}
    {codebook : Option Table} {definitions : Core.DataEnvironment} {internalReason : Core.Word}
    {validationPlan : Option Plan} {context : Context}
    (accepted : prepare values plan globals codebook definitions internalReason validationPlan = .ok context) :
    context.values = values := by
  unfold prepare at accepted
  cases checked : validatePrepared values plan globals codebook with
  | error error => simp [checked] at accepted
  | ok value => simp [checked] at accepted; cases accepted; rfl

/-- Pure data projection deliberately excludes every executable source leaf. -/
def dataOnly? : SourceValue → Option SourceCoreCompatibleValues.Value
  | .unit => some .unit
  | .bool value => some (.bool value)
  | .word value => some (.word value)
  | .integer value => some (.integer value)
  | .proxy inner => some (.proxy inner)
  | .product left right => do pure (.product (← dataOnly? left) (← dataOnly? right))
  | .constructed instantiation payloads => do
      pure (.constructed instantiation (← payloads.mapM dataOnly?))
  | .mapping key value entries => do
      pure (.mapping key value (← entries.mapM fun entry => do pure (← dataOnly? entry.1, ← dataOnly? entry.2)))
  | .global .. | .builtin .. | .closure .. | .instantiated .. => none
  decreasing_by
    all_goals first
      | decreasing_trivial
      | have smaller := List.sizeOf_lt_of_mem (by assumption)
        cases entry
        simp_all only [SourceTypedRuntime.Value.mapping.sizeOf_spec, Prod.mk.sizeOf_spec]
        omega

/-- Executable structural size for accepted input carriers. It never walks a
closure body, source table or global evidence ledger. Raw type sizes account
for the pure defaults transported beside mapping entries. -/
def encodingSize : SourceValue → Nat
  | .product left right => encodingSize left + encodingSize right + 1
  | .constructed instantiation payloads =>
      instantiation.resultType.size +
        (instantiation.payloadTypes.foldl (fun total type => total + type.size) 0) +
        (payloads.foldl (fun total value => total + encodingSize value + 1) 0) + 1
  | .mapping key value entries => key.size + value.size +
      (entries.foldl (fun total entry => total + encodingSize entry.1 + encodingSize entry.2 + 1) 0) + 1
  | .proxy inner => inner.size + 1
  | _ => 1
  decreasing_by
    all_goals first
      | decreasing_trivial
      | have smaller := List.sizeOf_lt_of_mem (by assumption)
        cases entry
        simp_all only [SourceTypedRuntime.Value.mapping.sizeOf_spec, Prod.mk.sizeOf_spec]
        omega

private def identity (index : Nat) : Except Error Core.Word :=
  match Core.Word.ofNat? (index + 1) with
  | some word => pure word | none => throw .identitySpaceExhausted

private def decorate (context : Context) (origin : SourceCoreStageCodebook.Origin)
    (type : Core.Ty) (raw : Core.Expr) : Except Error Core.Expr := do
  if context.values.checked.catalog.callableContracts then
    let table ← match context.codebook with
      | some table => pure table | none => throw (.missingContract origin)
    let id ← descriptor table origin
    pure (Core.LanguageResult.bind type raw (Core.LanguageResult.success (Core.CallableContract.wrap id (.var 0))))
  else pure raw

private def global (context : Context) (key : Key) (type : Core.Ty) : Except Error Core.Expr := do
  let (signature, index) ← match context.globals.zipIdx.find? (fun pair => decide (pair.1.key = key)) with
    | some found => pure found | none => throw (.missingGlobal key)
  decorate context (.named key) type
    (SourceCoreFunctions.namedReference signature index (← identity index) context.internalReason)

private def builtin (context : Context) (function : BuiltinFunctionId) (type : Core.Ty) : Except Error Core.Expr := do
  let index ← match BuiltinFunctionId.all.zipIdx.find? (fun pair => decide (pair.1 = function)) with
    | some (_, index) => pure index | none => throw .unsupportedValue
  if context.values.checked.catalog.callableContracts then
    let table ← match context.codebook with
      | some table => pure table | none => throw (.missingContract (.builtin function))
    let id ← descriptor table (.builtin function)
    let entry ← match table.entryAt? id with
      | some entry => pure entry | none => throw (.missingContract (.builtin function))
    unless entry.parameterCount = function.parameterTypes.length && entry.contract.isNone do
      throw (.contractMismatch (.builtin function))
  decorate context (.builtin function) type (Core.LanguageResult.success
    (Core.TaggedFunction.identified (← identity (context.globals.length + index))
      (SourceCoreInteger.builtinClosure function)))

mutual
  private def encodeRaw : Nat → Context → (values : Values) → Ty → SourceValue → Except Error (Extended values.registry Lowered)
    | 0, _, _, _, _ => throw .exhausted
    | fuel + 1, context, values, expected, value => do
        let type ← native values expected
        match dataOnly? value with
        | some data =>
            let encoded ← (SourceCoreCompatibleValues.encode (fuel + 1) values expected data).mapError Error.codec
            let expression ← match SourceCoreCompatibleDataExpressions.quote encoded.value with
              | some expression => pure expression | none => throw .unsupportedValue
            pure ⟨encoded.context.registry, encoded.preserves, ⟨type, Core.LanguageResult.success expression⟩⟩
        | none =>
            match SourceCoreRawMetadata.runtimeType expected, value with
            | .function .., .global key _ =>
                pure ⟨values.registry, .refl _, ⟨type, ← global context key type⟩⟩
            | .function .., .builtin function =>
                pure ⟨values.registry, .refl _, ⟨type, ← builtin context function type⟩⟩
            | .product leftType rightType, .product left right =>
                let left ← encodeRaw fuel context values leftType left
                let next := values.extend left.registry left.preserves
                let right ← encodeRaw fuel context next rightType right
                pure ⟨right.registry, left.preserves.trans right.preserves,
                  ⟨type, Core.LocalSequence.pair left.value.type right.value.type left.value.expression right.value.expression⟩⟩
            | .mapping keyType valueType, .mapping actualKey actualValue entries =>
                let registered ← (values.registry.intern expected (.mapping actualKey actualValue)).mapError Error.metadata
                let next := values.extend registered.registry registered.preserves
                let layout ← (values.checked.catalog.mappingLayout keyType valueType).mapError Error.catalog
                let entries ← encodeEntries fuel context next actualKey actualValue layout entries
                let next := next.extend entries.registry entries.preserves
                let fallback ← encodeDefault fuel context next actualValue layout.valueType
                pure ⟨fallback.registry, registered.preserves.trans (entries.preserves.trans fallback.preserves),
                  ⟨type, Core.LanguageResult.bind type
                    (Core.LocalSequence.pair layout.type layout.lookupResult entries.value.expression fallback.value.expression)
                    (Core.LanguageResult.success (SourceCoreMappingWithDefault.pack (.word registered.id)
                      (.second (.var 0)) (.first (.var 0))))⟩⟩
            | _, .constructed instantiation payloads =>
                let registered ← (values.registry.intern expected (.constructor instantiation)).mapError Error.metadata
                let constructor ← (values.checked.resolveConstructor instantiation).mapError Error.catalog
                let next := values.extend registered.registry registered.preserves
                let payloads ← encodePayloads fuel context next instantiation.payloadTypes payloads
                pure ⟨payloads.registry, registered.preserves.trans payloads.preserves,
                  ⟨type, SourceCoreCompatibleDataExpressions.construct constructor registered.id payloads.value.expression⟩⟩
            | _, _ => throw .unsupportedValue

  private def encodePayloads (fuel : Nat) (context : Context) (values : Values) (types : List Ty) (payloads : List SourceValue) :
      Except Error (Extended values.registry Lowered) := do
    unless types.length = payloads.length do throw .payloadCountMismatch
    match fuel, types, payloads with
    | _, [], [] => pure ⟨values.registry, .refl _, ⟨.unit, Core.LanguageResult.success .unit⟩⟩
    | 0, _, _ => throw .exhausted
    | fuel + 1, [type], [value] => encodeRaw fuel context values type value
    | fuel + 1, type :: types, value :: payloads =>
        let head ← encodeRaw fuel context values type value
        let next := values.extend head.registry head.preserves
        let tail ← encodePayloads fuel context next types payloads
        pure ⟨tail.registry, head.preserves.trans tail.preserves,
          ⟨.product head.value.type tail.value.type,
            Core.LocalSequence.pair head.value.type tail.value.type head.value.expression tail.value.expression⟩⟩
    | _, _, _ => throw .payloadCountMismatch

  private def encodeEntries : Nat → Context → (values : Values) → Ty → Ty → Core.OrderedMapping.Layout →
      List (SourceValue × SourceValue) → Except Error (Extended values.registry Lowered)
    | _, _, values, _, _, layout, [] => pure ⟨values.registry, .refl _,
        ⟨layout.type, Core.LanguageResult.success (Core.OrderedMapping.empty layout)⟩⟩
    | 0, _, _, _, _, _, _ :: _ => throw .exhausted
    | fuel + 1, context, values, keyType, valueType, layout, (key, value) :: entries => do
        let key ← encodeRaw fuel context values keyType key
        let next := values.extend key.registry key.preserves
        let value ← encodeRaw fuel context next valueType value
        let next := next.extend value.registry value.preserves
        let tail ← encodeEntries fuel context next keyType valueType layout entries
        let pair := Core.LocalSequence.pair layout.keyType layout.valueType key.value.expression value.value.expression
        pure ⟨tail.registry, key.preserves.trans (value.preserves.trans tail.preserves),
          ⟨layout.type, Core.LanguageResult.bind layout.type
            (Core.LocalSequence.pair (.product layout.keyType layout.valueType) layout.type pair tail.value.expression)
            (Core.LanguageResult.success (.construct layout.consConstructor (.var 0)))⟩⟩

  private def encodeDefault (fuel : Nat) (context : Context) (values : Values) (rawType : Ty) (type : Core.Ty) :
      Except Error (Extended values.registry Lowered) := do
    match SourceTypedRuntime.defaultValue? (rawType.size + 1) rawType with
    | none => pure ⟨values.registry, .refl _, ⟨.sum .unit type, Core.LanguageResult.success (.inLeft type .unit)⟩⟩
    | some source =>
        let encoded ← encodeRaw fuel context values rawType source
        pure ⟨encoded.registry, encoded.preserves, ⟨.sum .unit type,
          Core.LanguageResult.bind (.sum .unit type) encoded.value.expression
            (Core.LanguageResult.success (.inRight .unit (.var 0)))⟩⟩
end

private def encodeArgumentsRaw (fuel : Nat) (context : Context) (values : Values) :
    List Ty → List SourceValue → Except Error (Extended values.registry (List Lowered))
  | [], [] => pure ⟨values.registry, .refl _, []⟩
  | type :: types, value :: arguments => do
      let head ← encodeRaw fuel context values type value
      let next := values.extend head.registry head.preserves
      let tail ← encodeArgumentsRaw fuel context next types arguments
      pure ⟨tail.registry, head.preserves.trans tail.preserves, head.value :: tail.value⟩
  | _, _ => throw .payloadCountMismatch

structure Encoded (context : Context) (expected : List Ty) (arguments : List SourceValue) (validationFuel : Nat) where private mk ::
  values : Values
  preserves : SourceCoreRawMetadata.Extends context.values.registry values.registry
  parts : List Lowered
  expression : Core.Expr
  type : Core.Ty
  packed : SourceCoreCalls.packArguments parts = ⟨type, expression⟩
  typed : Core.HasType context.coreContext expression (Core.LanguageResult.resultType type) context.definitions
  validated : SourceTypedRuntime.validateInputs context.values.checked.signatures context.validationPlan
    validationFuel expected arguments = none

/-- Validation fuel controls the original deep validator, not the width of an
already accepted list. Encoding has a structural budget derived from the input
and its source types, including their pure transported defaults. -/
def encode (context : Context) (expected : List Ty) (arguments : List SourceValue)
    (validationFuel : Nat := 256) : Except Error (Encoded context expected arguments validationFuel) := do
  match validated : SourceTypedRuntime.validateInputs context.values.checked.signatures context.validationPlan
      validationFuel expected arguments with
  | some error => throw (.source error)
  | none =>
      let encodingFuel := (arguments.foldl (fun total value => total + encodingSize value) 0) +
        (expected.foldl (fun total type => total + type.size) 0) + 32
      let raw ← encodeArgumentsRaw encodingFuel context context.values expected arguments
      let values := context.values.extend raw.registry raw.preserves
      let packed := SourceCoreCalls.packArguments raw.value
      if typed : Core.infer? context.coreContext packed.expression context.definitions = some (Core.LanguageResult.resultType packed.type) then
        pure (.mk values raw.preserves raw.value packed.expression packed.type rfl (Core.infer_sound typed) validated)
      else throw (.checkFailed packed.type)

end Solcore.Frontend.SourceCoreCompatibleInputs
end

section
-- leanmerge: from Solcore.Frontend.SourceCoreCompatibleFunctions
/-! Cached source-compatible functions reuse the contextual compiler and
native runner. Original contracts and local-evidence receipts own the inventory;
data inputs extend only the raw metadata registry. Dynamic missing-default
diagnostics use disjoint reserved ranges before callable tokens are assigned.

This artifact supplies native typed execution and a data codec. Legacy source
heap export and global/builtin/function value adapters are separate boundaries.
It does not evaluate source expressions or change checker admission. -/
set_option autoImplicit false
namespace Solcore.Frontend.SourceCoreCompatibleFunctions
open SourceInference
abbrev Checked := SourceCoreCompatibleCatalog.Checked
abbrev Key := SourceSpecialization.SpecializationKey
abbrev Plan := SourceSpecializationWorklist.Plan
abbrev DataValue := SourceCoreCompatibleValues.Value
abbrev Values := SourceCoreCompatibleValues.Context
abbrev Native := SourceCoreGeneralEntry.NativeEntry
abbrev NativeResult := SourceCoreGeneralEntry.Result

inductive Error where
  | plan (error : SourceCompilationPlan.Error)
  | catalog (error : SourceCoreCompatibleCatalog.Error)
  | locals (error : SourceCoreLocalPolymorphism.Error)
  | contexts (error : SourceCoreStageCodebook.Error)
  | functions (error : SourceCoreGeneralFunctions.Error)
  | diagnostics (error : SourceCoreCompatibleDataPlaceFaultSites.Error)
  | callables (error : SourceCoreCallableFaultSites.Error)
  | native (error : SourceCoreGeneralEntry.NativeCompileError)
  | missingRoot (key : Key)
  | inputs (error : SourceCoreCompatibleInputs.Error)
  deriving Repr

structure Entry (checked : Checked) where private mk ::
  key : Key
  inputs : List TypedBinder
  sourceResultType : TypeSystem.Ty
  native : Native checked.catalog.definitions

structure SourceInputs (checked : Checked) where private mk ::
  context : SourceCoreCompatibleInputs.Context
  valuesExact : context.values = SourceCoreCompatibleValues.Context.initial checked

private def prepareSourceInputs (checked : Checked) (plan validationPlan : Plan)
    (globals : List SourceCoreCalls.Signature)
    (native : Option SourceCoreGeneralFunctions.CallableContext) : Except Error (SourceInputs checked) :=
  match accepted : SourceCoreCompatibleInputs.prepare
      (SourceCoreCompatibleValues.Context.initial checked) plan globals (native.map (·.table))
      checked.catalog.definitions Core.Word.zero (some validationPlan) with
  | .error error => .error (.inputs error)
  | .ok context => .ok ⟨context, SourceCoreCompatibleInputs.prepare_values accepted⟩

structure Prepared (checked : Checked) where private mk ::
  sourceProgram : CheckedProgram
  signatureOwnership : checked.signatures = sourceProgram.signatures
  validationPlan : Plan
  plan : Plan
  planPrepared : SourceCompilationPlan.prepareExecutablePlanEvidence sourceProgram validationPlan = .ok plan
  locals : SourceCoreLocalPolymorphism.Catalog
  contexts : List SourceCoreLocalEvidence.Prepared
  functions : List SourceCoreGeneralFunctions.Function
  globals : List SourceCoreCalls.Signature
  closures : List Core.Expr
  callableContext : Option SourceCoreGeneralFunctions.CallableContext
  sourceInputs : Option (SourceInputs checked)
  diagnostics : Option (SourceCoreCompatibleDataPlaceFaultSites.Program (SourceCoreCompatibleValues.Context.initial checked))
  callableDiagnostics : Option SourceCoreCallableFaultSites.Program
  entries : List (Entry checked)

def Prepared.find? {checked : Checked} (prepared : Prepared checked) (key : Key) : Option (Entry checked) :=
  prepared.entries.find? (fun entry => decide (entry.key = key))

def representation (context : Values) (fuel : Nat) : SourceCoreGeneralFunctions.Representation := {
  expressions := SourceCoreCompatibleDataExpressions.functionPolicy fuel context
  allowStaged := context.checked.catalog.callableContracts
  loops := fun solved assignments diagnostics owner expression =>
    SourceCoreCompatibleDataMatches.loopPolicy context solved assignments diagnostics owner expression
  loopsWithSourceCells := fun cells solved assignments diagnostics owner expression =>
    SourceCoreCompatibleDataMatches.loopPolicy context solved assignments diagnostics owner expression cells
}

private def project (checked : Checked) (type : TypeSystem.Ty) :
    Except SourceCoreLocalPolymorphism.Error Core.Ty :=
  (checked.project type).map (·.type) |>.mapError fun
    | .catalog error => .projection error
    | .metadata _ => .projection (.unsupportedType type)

private def prepareExecutable (program : CheckedProgram) (validationPlan : Plan) :
    Except SourceCompilationPlan.Error
      {actual : Plan // SourceCompilationPlan.prepareExecutablePlanEvidence program validationPlan = .ok actual} :=
  match _selected : SourceCompilationPlan.prepareExecutablePlanEvidence program validationPlan with
  | .error error => .error error
  | .ok executable => .ok ⟨executable, rfl⟩

def prepareWithCatalog (program : CheckedProgram) (plan : Plan) (checked : Checked)
    (ownership : checked.signatures = program.signatures) (fuel : Nat) :
    Except Error (Prepared checked) := do
  let validationPlan := plan
  let executable ← (prepareExecutable program validationPlan).mapError Error.plan
  let plan := executable.val
  let context := SourceCoreCompatibleValues.Context.initial checked
  let representation := representation context fuel
  let locals ← (SourceCoreLocalPolymorphism.prepareWithProjection (project checked) plan).mapError Error.locals
  let contexts ← (SourceCoreStageCodebook.prepareContexts program plan (locals.bindings.flatMap (·.instances)))
    |>.mapError Error.contexts
  let functions ← (plan.specializations.reverse.mapM
    (SourceCoreGeneralFunctions.prepareFunctionWithRepresentation program representation)).mapError Error.functions
  let globals := functions.map (·.signature)
  match plan.seedKeys with
  | [] => pure ⟨program, ownership, validationPlan, plan, executable.property, locals, contexts,
      functions, globals, [], none, none, none, none, []⟩
  | first :: _ =>
      let diagnostics ← (SourceCoreCompatibleDataPlaceFaultSites.prepare context plan first
        (contexts.map (fun prepared => (prepared.caller.key, prepared.source)))).mapError Error.diagnostics
      let native ← if checked.catalog.callableContracts then do
          let table ← (SourceCoreStageCodebook.prepareWithProjection program plan (project checked)).mapError Error.contexts
          let callableDiagnostics ← (SourceCoreCallableFaultSites.prepare plan table diagnostics.program.rootTable
            diagnostics.nextReason).mapError Error.callables
          pure (some {table, diagnostics := callableDiagnostics : SourceCoreGeneralFunctions.CallableContext})
        else pure none
      let locals ← match native with
        | none => pure locals
        | some native => (locals.withCallableContracts (fun caller initializer active =>
            native.table.idAt? (.lambda caller initializer active))).mapError Error.locals
      let loweredDiagnostics := match native with
        | none => diagnostics.program
        | some native => {diagnostics.program with rootTable := native.diagnostics.rootTable}
      let closures ← (functions.mapM (SourceCoreGeneralFunctions.compileClosureWithRepresentation
        program representation program.signatures plan globals loweredDiagnostics locals native fuel)).mapError Error.functions
      let sourceInputs ← prepareSourceInputs checked plan validationPlan globals native
      let entries ← plan.seedKeys.mapM fun key => do
        let function ← match functions.find? (fun function => decide (function.signature.key = key)) with
          | some function => pure function
          | none => throw (.missingRoot key)
        let arguments := SourceCoreCalls.packArguments (function.inputs.zipIdx.map fun ((_, type), index) =>
          ⟨type, Core.OptionalCell.read type (.var (globals.length + (function.inputs.length - 1 - index))) Core.Word.zero⟩)
        let body ← (SourceCoreGeneralFunctions.assembleCall globals functions closures key arguments).mapError Error.functions
        let native ← (SourceCoreGeneralEntry.NativeEntry.compile checked.catalog.definitions (function.inputs.map Prod.snd)
          function.signature.resultType body).mapError Error.native
        pure (Entry.mk key (function.inputs.map Prod.fst) function.specialized.function.inferredBodyType native)
      pure ⟨program, ownership, validationPlan, plan, executable.property, locals, contexts,
        functions, globals, closures, native, some sourceInputs, some diagnostics, native.map (·.diagnostics), entries⟩

structure Automatic where private mk ::
  checked : Checked
  prepared : Prepared checked

private def originalMetadata (source : TypedSource) : List SourceCoreRawMetadata.Metadata :=
  source.nodes.filterMap fun
    | .expression {form := .constructor instantiation _, ..} =>
        if SourceCoreDataCatalog.closed instantiation.resultType &&
            instantiation.payloadTypes.all SourceCoreDataCatalog.closed &&
            instantiation.parameterSubstitution.all (fun entry => SourceCoreDataCatalog.closed entry.2) then
          some (.constructor instantiation) else none
    | .expression {form := .proxy inner, ..} =>
        if SourceCoreDataCatalog.closed inner then some (.proxy inner) else none
    | _ => none

def prepare (program : CheckedProgram) (plan : Plan) (fuel : Nat)
    (limits : SourceCoreRawMetadata.Limits := {}) : Except Error Automatic := do
  let executable ← (SourceCompilationPlan.prepareExecutablePlanEvidence program plan).mapError Error.plan
  let locals ← (SourceCompilationPlan.localLambdaCatalog executable).mapError
    (Error.locals ∘ SourceCoreLocalPolymorphism.Error.discovery)
  let sources := executable.specializations.map (·.function.typedBody) ++
    locals.map (fun candidate => candidate.source.applySubstitution candidate.substitution)
  let types := (SourceCorePlanCatalog.planTypes executable ++ sources.flatMap (fun source =>
    SourceCorePlanCatalog.sourceTypes source ++ source.nodes.filterMap (fun
      | .expression node => some node.rawType
      | _ => none))).filter SourceCoreDataCatalog.closed |>.eraseDups
  match accepted : SourceCoreCompatibleCatalog.prepare program.signatures fuel types
      (sources.flatMap originalMetadata) limits with
  | .error error => throw (.catalog error)
  | .ok checked =>
      let prepared ← prepareWithCatalog program plan checked
        (SourceCoreCompatibleCatalog.prepare_signatures accepted) fuel
      pure ⟨checked, prepared⟩

inductive RunError where
  | argumentCountMismatch (expected actual : Nat)
  | missingEntry (key : Key)
  | input (index : Nat) (error : SourceCoreCompatibleValues.Error)
  | native (error : SourceCoreGeneralEntry.RunError)
  | diagnostics (error : SourceCoreCompatibleDataPlaceFaultSites.Error)
  | sourceInputsUnavailable
  | sourceInput (error : SourceCoreCompatibleInputs.Error)
  | functions (error : SourceCoreGeneralFunctions.Error)
  | compile (error : SourceCoreGeneralEntry.NativeCompileError)
  deriving Repr

private def encodeArguments (fuel : Nat) (context : Values) (index : Nat) :
    List TypedBinder → List DataValue → Except RunError (SourceCoreCompatibleValues.Extended context.registry (List Core.Value))
  | [], [] => pure (.pure context.registry [])
  | input :: inputs, value :: values => do
      let encoded ← (SourceCoreCompatibleValues.encode fuel context input.scheme.body value).mapError (RunError.input index)
      let rest ← encodeArguments fuel encoded.context (index + 1) inputs values
      pure ⟨rest.registry, encoded.preserves.trans rest.preserves, encoded.value :: rest.value⟩
  | inputs, values => throw (.argumentCountMismatch (index + inputs.length) (index + values.length))

structure Result {checked : Checked} (entry : Entry checked) where private mk ::
  context : Values
  contextOwner : context.checked = checked
  extension : SourceCoreRawMetadata.Extends checked.staticRegistry context.registry
  diagnostics : SourceCoreFaultSites.Table
  native : NativeResult checked.catalog.definitions entry.native.resultType

private def diagnosticTable {checked : Checked} (prepared : Prepared checked) (entry : Entry checked)
    (registry : SourceCoreRawMetadata.Registry)
    (extension : SourceCoreRawMetadata.Extends checked.staticRegistry registry) :
    Except RunError SourceCoreFaultSites.Table := do
  let table ← match prepared.diagnostics with
    | some diagnostics => (diagnostics.tableForRegistry registry extension).mapError RunError.diagnostics
    | none => pure {
        owner := entry.key.declaration, resultType := entry.sourceResultType
        reads := [], escapedReason := Core.Word.zero }
  pure <| match prepared.callableDiagnostics with
    | none => table
    | some diagnostics => {table with additional := table.additional ++
        diagnostics.rootTable.additional.filter (fun item => diagnostics.unknown.val ≤ item.1.val)}

private def runEntryData {checked : Checked} (prepared : Prepared checked) (entry : Entry checked)
    (arguments : List DataValue) (executionFuel : Nat) (validationFuel : Nat := 256) :
    Except RunError (Result entry) := do
  let context := SourceCoreCompatibleValues.Context.initial checked
  let encoded ← encodeArguments validationFuel context 0 entry.inputs arguments
  let context := context.extend encoded.registry encoded.preserves
  let native ← (entry.native.run encoded.value executionFuel).mapError RunError.native
  let table ← diagnosticTable prepared entry encoded.registry encoded.preserves
  pure ⟨context, rfl, encoded.preserves, table, native⟩

structure Completion (checked : Checked) where private mk ::
  entry : Entry checked
  result : Result entry

def Prepared.runData {checked : Checked} (prepared : Prepared checked) (key : Key)
    (arguments : List DataValue) (executionFuel : Nat) (validationFuel : Nat := 256) :
    Except RunError (Completion checked) := do
  let entry ← match prepared.find? key with
    | some entry => pure entry
    | none => throw (.missingEntry key)
  let result ← runEntryData prepared entry arguments executionFuel validationFuel
  pure ⟨entry, result⟩

/-- Source inputs retain the original validation plan. Only argument carriers
are injected below cached globals; source bodies and staging are already compiled. -/
def Prepared.runSource {checked : Checked} (prepared : Prepared checked) (key : Key)
    (arguments : List SourceTypedRuntime.Value) (executionFuel : Nat) (validationFuel : Nat := 256) :
    Except RunError (Completion checked) := do
  let entry ← match prepared.find? key with
    | some entry => pure entry
    | none => throw (.missingEntry key)
  let ready ← match prepared.sourceInputs with
    | some ready => pure ready
    | none => throw .sourceInputsUnavailable
  let encoded ← (SourceCoreCompatibleInputs.encode ready.context (entry.inputs.map (·.scheme.body))
    arguments validationFuel).mapError RunError.sourceInput
  have extension : SourceCoreRawMetadata.Extends checked.staticRegistry encoded.values.registry := by
    change SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial checked).registry _
    rw [← ready.valuesExact]
    exact encoded.preserves
  let context := (SourceCoreCompatibleValues.Context.initial checked).extend encoded.values.registry extension
  let body ← (SourceCoreGeneralFunctions.assembleCall prepared.globals prepared.functions prepared.closures
    key ⟨encoded.type, encoded.expression⟩).mapError RunError.functions
  let native ← match accepted : SourceCoreGeneralEntry.NativeEntry.compile checked.catalog.definitions []
      entry.native.resultType body with
    | .error error => throw (.compile error)
    | .ok runner =>
        let result ← (runner.run [] executionFuel).mapError RunError.native
        have resultType := (SourceCoreGeneralEntry.NativeEntry.compile_fields accepted).2.1
        pure (resultType ▸ result)
  let table ← diagnosticTable prepared entry encoded.values.registry extension
  pure ⟨entry, ⟨context, rfl, extension, table, native⟩⟩

def Completion.resume {checked : Checked} (completion : Completion checked) (fuel : Nat) : Completion checked :=
  match completion.result.native.checkpoint? with
  | none => completion
  | some checkpoint => ⟨completion.entry, {completion.result with native := checkpoint.resume fuel}⟩

end Solcore.Frontend.SourceCoreCompatibleFunctions
end
