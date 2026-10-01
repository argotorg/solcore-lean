import Solcore.Frontend.SourceCoreCompatibleDataExpressions
import Solcore.Frontend.SourceCoreSourceCells
import Solcore.Frontend.SourceCoreCompatibleDataPlaceFaultSites
import Solcore.Core.DirectWordComparisons
import Solcore.Core.LocalLoop

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
