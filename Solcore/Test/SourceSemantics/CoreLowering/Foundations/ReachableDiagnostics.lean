import Solcore.SourceSemantics.CoreLowering.GenericHeap
import Solcore.SourceSemantics.CoreLowering.GenericImperativeMatchCertificates
import Solcore.Test.Frontend.Source.CompilerFeatureSupport
import Solcore.SourceSemantics.CoreLowering.BuiltinImperativeMatchExtraction
import Solcore.SourceSemantics.CoreLowering.GenericImperativeMatchReadyFactory
import Solcore.SourceSemantics.CoreLowering.GenericMatchMeaning
import Solcore.SourceSemantics.CoreLowering.GenericMatchPreservation
import Solcore.SourceSemantics.CoreLowering.GenericMatchScopedContexts
import Solcore.SourceSemantics.CoreLowering.BuiltinImperativeFor
import Solcore.SourceSemantics.CoreLowering.NamedImperativeForStatements
import Solcore.SourceSemantics.CoreLowering.GenericAssignmentDiagnosticCertificates
import Solcore.SourceSemantics.CoreLowering.ImperativeNativePolicyTyping
import Solcore.SourceSemantics.CoreLowering.CaptureCopyTyping
import Solcore.SourceSemantics.CoreLowering.BuiltinImperativeMatchBodyMeaning
import Solcore.SourceSemantics.CoreLowering.GenericImperativeForCertificates
import Solcore.SourceSemantics.CoreLowering.NamedForFunctionBodyMeaning
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedCatalogProfiles
import Solcore.SourceSemantics.CoreLowering.BuiltinImperativeMatchPreparedDiagnostics
import Solcore.SourceSemantics.CoreLowering.NamedForFunctionFallthrough
import Solcore.SourceSemantics.CoreLowering.CallableIndexedNamedGeneration
import Solcore.Test.SourceSemantics.CoreLowering.Recursive.NamedStatements
import Solcore.Test.SourceSemantics.CoreLowering.UnifiedCorpusSupport
import Solcore.SourceSemantics.CoreLowering.CallableLambdaViewBodyTree
import Solcore.SourceSemantics.CoreLowering.CallableLambdaViewSourceTyping
import Solcore.SourceSemantics.CoreLowering.NamedLoopFunctionFallthrough
import Solcore.SourceSemantics.CoreLowering.ReachableStatementContinuationMeaning
import Solcore.SourceSemantics.CoreLowering.ReachableMatchContinuationMeaning
import Solcore.SourceSemantics.CoreLowering.GenericLexicalStatementTree
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedImperativeMatchSyntaxFactory

/-!
# Reachable statement tests

Reachable diagnostics and continuations of imperative, match and terminal statements, and generic matches.
-/

section
-- leanmerge: from Solcore.Test.SourceCoreGenericHeap
/-! Representation-interface regressions. The finite specialization is exactly
the existing DataHeap. A deliberately narrow, syntactically fixed closure model
also demonstrates cyclic captured references and world extension. This test
does not claim general source function-body or mapping semantics. -/

set_option autoImplicit false
namespace Tests.SourceCoreGenericHeap
open Solcore Solcore.Frontend Solcore.Frontend.SourceInference
open Solcore.SourceSemantics Solcore.SourceSemantics.CoreLowering
open GeneralHeap GenericHeap

example {catalog : SourceCoreDataCatalog.Catalog} {signatures : ProgramSignatures}
    {mapping : LocationMap} {world : Core.StoreTyping} {heap : Dynamic.Heap} {store : Core.Store}
    (old : DataHeap.HeapRepresents catalog signatures mapping world heap store) :
    GenericHeap.HeapRepresents (finitePayload catalog signatures) mapping world heap store := finiteHeap_iff.mpr old

private def moduleId : Workspace.ModuleId :=
  ⟨.main, ⟨[⟨"generic_heap", by decide⟩], by decide⟩⟩
private def owner : Resolved.DeclarationId := ⟨moduleId, 0⟩
private def self : Resolved.LocalId := ⟨owner, 0⟩
private def signatures : ProgramSignatures := ⟨[], [], [], [], [], []⟩
private def catalog : SourceCoreDataCatalog.Catalog := {}
private def sourceType : TypeSystem.Ty := .function .unit .unit
private def functionType : Core.Ty := Core.TaggedFunction.functionType .unit .unit
private def cellType : Core.Ty := Core.OptionalCell.cellType functionType
private def sourceClosure : Dynamic.Closure := {
  parameters := [], resultType := .unit, body := []
  source := { owner, inputs := [], roots := [], nodes := [] }
  captured := [(self, ⟨0⟩)]
  context := (SourceSemantics.Context.ofSignatures signatures).withLocal self (.mono sourceType) []
  evidence := []
}
private def coreClosure (location : Core.Location) : Core.Value :=
  .pair (.inLeft .word .unit)
    (.closure .unit (Core.LanguageResult.resultType .unit) (Core.LanguageResult.success .unit)
      [.cellRef cellType location])

private inductive Captured (mapping : LocationMap) (world : Core.StoreTyping) :
    TypeSystem.Ty → Dynamic.Value → Core.Value → Core.Ty → Prop where
  | closure {location : Core.Location} (captured : ReferenceRepresents mapping world ⟨0⟩ location functionType) :
      Captured mapping world sourceType (.closure sourceClosure) (coreClosure location) functionType

private def model : PayloadModel catalog where
  Represents := Captured
  projection := by intro mapping world type source value payload represented; cases represented; rfl
  runtime_hasType := by
    intro mapping world type source value payload represented
    cases represented with
    | closure captured =>
      exact .pair (.inLeft .unit) (.closure (.cons (.cellRef captured.typed) .nil) (.inRight .word .unit))
  extend := by
    intro mapping futureMap world futureWorld type source value payload represented maps worlds
    cases represented with
    | closure captured => exact .closure (captured.extend maps worlds)

private def initialHeap : Dynamic.Heap := ⟨[⟨sourceType, none, none⟩]⟩
private def initialWorld : Core.StoreTyping := [cellType]
private def initialStore : Core.Store := [.inLeft functionType .unit]
private theorem initialRelated : GenericHeap.HeapRepresents model [0] initialWorld initialHeap initialStore :=
  (GenericHeap.HeapRepresents.empty.allocate (.uninitialized rfl) .append).1
private def installedHeap : Dynamic.Heap := ⟨[⟨sourceType, some (.closure sourceClosure), none⟩]⟩
private def installedStore : Core.Store := [.inRight .unit (coreClosure 0)]
private theorem closureRelated : model.Represents [0] initialWorld sourceType (.closure sourceClosure)
    (coreClosure 0) functionType := .closure ⟨rfl, rfl⟩

/-- The stored source closure captures source location zero, and the Core
closure captures its mapped cell zero. Neither proof recursively follows it. -/
private theorem installedRelated : GenericHeap.HeapRepresents model [0] initialWorld installedHeap installedStore := by
  obtain ⟨updated, written, related, _⟩ := initialRelated.write_initialized
    (reference := ⟨rfl, rfl⟩) (.intro .head) closureRelated (.intro (.intro .head) .head)
  have expected : initialStore.write? 0 (.inRight .unit (coreClosure 0)) = some installedStore := rfl
  have same := Option.some.inj (written.symm.trans expected)
  exact same ▸ related

example : Core.RuntimeStoreHasTypes initialWorld installedStore catalog.definitions := installedRelated.runtime_hasTypes

private def extendedWorld : Core.StoreTyping := initialWorld ++ [functionType]
private def extendedStore : Core.Store := installedStore ++ [coreClosure 0]
example : GenericHeap.HeapRepresents model [0] extendedWorld installedHeap extendedStore :=
  installedRelated.allocate_administrative (model.runtime_hasType closureRelated)
example : model.Represents [0] extendedWorld sourceType (.closure sourceClosure) (coreClosure 0) functionType :=
  model.extend closureRelated (.refl _) ⟨_, rfl⟩
example : GeneralHeap.AdministrativePreserved [0] installedStore [0] extendedStore :=
  GeneralHeap.AdministrativePreserved.allocate_administrative [0] installedStore (coreClosure 0)

end Tests.SourceCoreGenericHeap
end

section
-- leanmerge: from Solcore.Test.SourceCoreGenericImperativeMatch
/-! Finite actual match children preserve duplicate occurrence order. The
recursive statement receipt admits matches inside loops and restores source
contexts from declarative pattern typing, independently of native type equality.
Whole match meaning is a separate consumer of this static extraction. -/
#check_failure Solcore.Frontend.SourceTypedRuntime.run
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreGenericImperativeMatch
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open GenericMatchChildren
private def moduleId : Workspace.ModuleId := ⟨.main, ⟨[⟨"generic_match", by decide⟩], by decide⟩⟩
private def owner : Resolved.DeclarationId := ⟨moduleId, 0⟩
private def span : Solcore.Syntax.SourceSpan := ⟨⟨.main, "generic_match.solc"⟩, 0, 1⟩
private def site : StatementId := ⟨⟨owner, 0⟩⟩
private def scrutinee : ExpressionId := ⟨⟨owner, 1⟩⟩
private def hidden : Resolved.LocalId := ⟨owner, 0⟩
private def pattern : TypedMatchPattern := {source := .wildcard span span, type := .unit, resolution := .wildcard}
private def arm : TypedMatchCase := ⟨span, pattern, []⟩
private def resolution : MatchResolution := ⟨scrutinee, hidden, [arm, arm], some [], []⟩
private def scrutineeNode : ExpressionNode := {id := scrutinee, span, type := .unit, form := .tuple []}
private def statementNode : StatementNode := ⟨site, span, .unit, .matchWith resolution⟩
private def source : TypedSource := {
  owner, inputs := [], roots := [.statement site]
  nodes := [.statement statementNode, .expression scrutineeNode]}
private def signatures : ProgramSignatures := ⟨[], [], [], [], [], []⟩
private def context : SourceSemantics.Context := .ofSignatures signatures
private def control : ControlContext := ⟨.unit, 0⟩
private theorem catalogExists : (SourceCoreCompatibleCatalog.prepare signatures 20 [.unit]).toOption.isSome = true := by cbv
private def checked := (SourceCoreCompatibleCatalog.prepare signatures 20 [.unit]).toOption.get catalogExists
private def values := SourceCoreCompatibleValues.Context.initial checked
private def ambient : AmbientDefinitions checked.catalog.definitions := .append _ [⟨[.unit]⟩]
private def compilation : SourceCoreCompatibleDataMatches.Context := ⟨values, [], none, some ambient.definitions⟩
private def lowerExpression : SourceCoreCompatibleDataMatches.ExpressionLowerer := fun _ _ _ _ _ =>
  .ok ⟨.unit, LanguageResult.success .unit⟩
private def lowerBody : SourceCoreCompatibleDataMatches.BodyLowerer := fun _ _ _ _ _ _ _ => .ok (LocalLoop.fallthrough .unit)
private def reasonAt : ExpressionId → Word := fun _ => Word.zero
private def compiled : Expr := match SourceCoreCompatibleDataMatches.lowerWithReasons compilation lowerExpression lowerBody
    20 source [] site resolution .unit reasonAt Word.zero with | .ok code => code | .error _ => .unit
private theorem accepted : SourceCoreCompatibleDataMatches.lowerWithReasons compilation lowerExpression lowerBody
    20 source [] site resolution .unit reasonAt Word.zero = .ok compiled := by rfl

/-- Even equal request data appears three times: both source arms and default. -/
theorem finite_actual_children : ∃ requests,
    CompatibleMatchCertificates.Certificate compilation source [] site resolution .unit Word.zero
      (fun _ _ lowered => lowered = ⟨.unit, LanguageResult.success .unit⟩) (Occurs requests) compiled ∧
    requests.length = 3 ∧ ∀ request ∈ requests, ∃ fuel,
      lowerBody fuel source request.scope request.statements .unit reasonAt Word.zero = .ok request.code := by
  simpa only [resolution, List.length_cons, List.length_nil, Option.isSome_some, ↓reduceIte] using
    finite_of_lower (fun _ _ generated => Except.ok.inj generated.symm) accepted

private def request : Request := ⟨[(hidden, .unit)], [], LocalLoop.fallthrough .unit⟩
private def compiledPattern : SourceCoreCompatibleDataMatches.Pattern :=
  ⟨.unit, [], [], .lambda .unit (.sum .unit .unit) (.inRight .unit .unit)⟩
example : armRequests [(hidden, .unit)] resolution.cases
    [(compiledPattern, LocalLoop.fallthrough .unit), (compiledPattern, LocalLoop.fallthrough .unit)] ++
    fallbackRequests [(hidden, .unit)] resolution.defaultBody (LocalLoop.fallthrough .unit) =
      [request, request, request] := rfl

private theorem patternTyped : TypedMatchPatternHasType context pattern .unit [] 0 :=
  ⟨rfl, .wildcard, .wildcard, ⟨by simp, by simp⟩⟩
private theorem casesTyped : MatchCasesHaveType source control context .unit resolution.cases
    [BodyFacts.empty, BodyFacts.empty] := by
  exact .cons (.intro patternTyped (.nil _) (.nil _ _))
    (.cons (.intro patternTyped (.nil _) (.nil _ _)) (.nil _ _ _))
private theorem sourceSelected : Dynamic.MatchCasesSelect context .unit resolution.cases resolution.defaultBody (.arm [] []) :=
  .head (.intro .wildcard .wildcard)

theorem selected_context_is_source : ContextFor source context .unit resolution.cases resolution.defaultBody request context :=
  ContextFor.selected_arm_at request rfl casesTyped sourceSelected (.nil _)

private theorem unique : NodeOccurrencesUnique source := by cbv; decide
private theorem scrutineeTyped : ExpressionHasType source context scrutinee .unit := by
  have admitted : TypeAdmissible context .unit := .unit (by simp [TypeParameterBindersWellFormed, context, Context.ofSignatures])
  apply ExpressionHasType.ofOrdinary (node := scrutineeNode) (rawType := .unit) (lookupExpression?_sound (by cbv))
    (.tuple (.nil _)) admitted admitted
  · intro requirement member; cases member
  · exact .nil _
  · rfl
private def expressionSyntax (id : ExpressionId) : Prop := id = scrutinee
private theorem syntaxTree (mode : Bool) : GenericImperativeMatch.Syntax source expressionSyntax context (.statements mode [site]) .unit := by
  apply GenericImperativeMatch.Syntax.matchWith (expressionSyntax := expressionSyntax) (node := statementNode) (scrutineeNode := scrutineeNode)
    (control := control) (caseFacts := [BodyFacts.empty, BodyFacts.empty]) rfl rfl (.inl rfl) rfl scrutineeTyped rfl casesTyped
  · intro statements selected
    have same : statements = [] := Option.some.inj selected.symm
    subst statements
    exact ⟨context, _, .nil _ _⟩
  · rfl
  · intro arm member binder found; rfl
  · intro request childContext selected
    have empty : request.statements = [] := by
      cases selected with
      | @arm actualArm binders arity childContext member same typed extended =>
        have armEq : actualArm = arm := by simpa [resolution] using member
        exact same.trans (congrArg TypedMatchCase.body armEq)
      | default same => exact Option.some.inj same.symm
    rw [empty]
    exact .body (.nil (.inl rfl))
  · exact .body (.nil (.inr rfl))

private theorem hiddenSourceFresh : GenericImperativeMatch.MatchHiddenFresh source := by
  intro id node actualResolution found form
  have sameNode : node = statementNode := by
    have member := (lookupStatement?_sound found).1
    simpa [source] using member
  subst node
  have sameResolution : actualResolution = resolution := StatementForm.matchWith.inj form.symm
  subst actualResolution
  simp [SourceCoreDataPlaces.declaredBinders, SourceCoreDataPlaces.patternBinders,
    source, statementNode, scrutineeNode, resolution, arm, pattern]

section ActualFlow
variable {layouts : SourceCoreAllocationLayouts.Prepared} {specialization : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context} {definitions : DataEnvironment}
  {policy : SourceCoreLoops.Policy} {matchCompilation : SourceCoreCompatibleDataMatches.Context}
  {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  (matchPolicy : policy.lowerMatch = some (SourceCoreCompatibleDataMatches.lowerWithReasons matchCompilation))
  (matchValues : matchCompilation.values = values) (matchDefinitions : matchCompilation.definitions = definitions)
  (matchAllocator : matchCompilation.sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator frame globals
    (layouts.allocatorAt specialization active onError)))
  (readPolicy : policy.readStatement = SourceCoreCompatibleDataExpressions.readStatement values.checked)
  (binderPolicy : ∀ scope binder, binder.scheme.quantified = [] →
    policy.lowerBinder source scope binder = SourceCoreCompatibleDataExpressions.lowerBinder values.checked source scope binder)
  (allocationPolicy : policy.sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator frame globals
    (layouts.allocatorAt specialization active onError)))
  (expressions : ∀ sourceContext, sourceContext.typeVariables = [] → sourceContext.residualTypeVariables = false →
    sourceContext.signatures = values.checked.signatures →
    ∀ {scope fuel id node lowered}, CompatibleExpressionReads.ScopeDeclarations source scope sourceContext → expressionSyntax id →
    source.lookupExpression? id = some node → ExpressionHasType source sourceContext id node.type →
    policy.lowerExpression fuel source scope id reasonAt = .ok lowered → certificates sourceContext scope id lowered)
  {invalidProjection : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Word}
  {invalidOperand : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Solcore.Syntax.ValueAssignOp → Word}
  {invalidUnary : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Word}
  {missingDefault : SourceCoreElaboration.ErrorSite → Resolved.LocalId → TypeSystem.Ty → Word}
  (assignments : CompatibleAssignmentStatements.AssignmentPolicy policy values invalidProjection invalidOperand missingDefault)
  (unaryPolicy : CompatibleBitNotStatements.Policy policy values invalidProjection invalidUnary missingDefault)
  (assignmentExpressions : ∀ sourceContext scope fuel id lowered,
    sourceContext.typeVariables = [] → sourceContext.residualTypeVariables = false →
    sourceContext.signatures = values.checked.signatures → CompatibleExpressionReads.ScopeDeclarations source scope sourceContext →
    expressionSyntax id → ∀ node, source.lookupExpression? id = some node → ExpressionHasType source sourceContext id node.type →
    policy.lowerExpression fuel source scope id reasonAt = .ok lowered → certificates sourceContext scope id lowered ∧
      HasType (SourceCoreLocalCell.coreContext scope ++ administrative) lowered.expression (LanguageResult.resultType lowered.type) definitions)
  (declarations : CompatibleExpressionReads.ScopeDeclarations source scope context)
  {mode : Bool} {fuel : Nat} {selfReason : Word} {code : Expr} {nativeType : Ty}
  (flowAccepted : SourceCoreLoops.lowerFlowStatementsWithPolicy policy fuel source scope [site] .unit reasonAt mode selfReason = .ok code)
  (nativeTyped : infer? (SourceCoreLocalCell.coreContext scope ++ administrative) code definitions = some nativeType)

include matchPolicy matchValues matchDefinitions matchAllocator readPolicy binderPolicy allocationPolicy expressions assignments unaryPolicy assignmentExpressions declarations flowAccepted nativeTyped in
/-- A real accepted emitted flow exposes finite recursive match children;
there is no semantic body assumption in this extraction. -/
theorem actual_flow_tree : GenericImperativeMatch.Tree layouts specialization active frame globals onError values source
    expressionSyntax certificates definitions administrative context scope (.statements mode [site]) .unit .unit code := by
  exact GenericImperativeMatch.tree_of_typed_flow matchPolicy matchValues matchDefinitions matchAllocator (GenericImperativeMatch.MatchChildStatic.of_hidden hiddenSourceFresh)
    readPolicy binderPolicy allocationPolicy expressions assignments unaryPolicy unique assignmentExpressions
    (syntaxTree mode) rfl rfl rfl declarations (by cbv) flowAccepted (infer_sound nativeTyped)
end ActualFlow

private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "function nested(seed: Word) returns (integer) { let result = seed; for (let i = seed; integerLt(wordToInteger(i), 3); i = wordFromInteger(integerAdd(wordToInteger(i), 1))) { match ((i, 7)) { case (0, x) { continue; } case (1, x) { let inner = x; while (integerLt(wordToInteger(inner), 9)) { inner += 1; match (inner) { case 8 { result += inner; } default { break; } } } } default { result += 1; } } } return wordToInteger(result); }",
    "function defaults(seed: Word) returns (integer) { let result = seed; match (seed) { case 0 {} default { let result = 9; match (result) { case 9 { result += 1; } default {} } } } return wordToInteger(result); }",
    "function failed(seed: Word) returns (integer) { let missing: Word; let seen: mapping(Bool => Word); for (let i = seed; true; let never = 99) { match (i) { case 0 { let first = wordFromInteger(wordToInteger(seen[false])); let dead = wordToInteger(missing); return dead; } default { return wordToInteger(i); } } } return wordToInteger(seed); }" ]}] }

def run : IO Unit := do
  let program ← SourceCompilerFeatureSupport.get "generic imperative match checker" (checkProgram workspace)
  let w := SourceCompilerFeatureSupport.scalar
  let nested ← SourceCompilerFeatureSupport.compileNamed program "nested"
  SourceCompilerFeatureSupport.require ((← nested.run [w 0]) == .integer 9) "match/for/while changed control transfer or builtin result"
  for fuel in [0, 7, 43] do nested.checkResume [w 0] (.integer 9) fuel
  let defaults ← SourceCompilerFeatureSupport.compileNamed program "defaults"
  for n in [0, 3] do
    SourceCompilerFeatureSupport.require ((← defaults.run [w n]) == .integer n) "nested match binding escaped lexical scope"
    for fuel in [0, 7, 43] do defaults.checkResume [w n] (.integer n) fuel
  let failed ← SourceCompilerFeatureSupport.compileNamed program "failed"
  let completed ← failed.invoke [w 0]
  match completed.outcome with
  | .failed token _ => SourceCompilerFeatureSupport.require (← completed.diagnostic token).isSome "match body fault lost diagnostic"
  | _ => throw (IO.userError "match body fault executed the post/body continuation")
  failed.checkCells [w 0] [(.word, some (w 0)), (.word, none), (.mapping .bool .word, some (.mapping .bool .word [])),
    (.word, some (w 0)), (.word, some (w 0)), (.word, some (w 0))]
  IO.println "generic imperative match receipts: finite duplicate children, independent arm contexts, nested loop/control, fault effects and resume GREEN"
end Tests.SourceCoreGenericImperativeMatch
end

section
-- leanmerge: from Solcore.Test.SourceCoreGenericImperativeMatchExtraction
/-! Actual flow extraction now retains all fixed match ledgers. The formal
consumer builds Ready from source context validity and the unchanged diagnostic
obligations, without a caller-supplied ledger tree or runtime child premise. -/
#check_failure Solcore.Frontend.SourceTypedRuntime.run
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreGenericImperativeMatchExtraction
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open GenericMatchChildren BuiltinImperativeMatch GeneralHeap CompatiblePayload CompatibleEquality ReadOnly
private def moduleId : Workspace.ModuleId := ⟨.main, ⟨[⟨"generic_match", by decide⟩], by decide⟩⟩
private def owner : Resolved.DeclarationId := ⟨moduleId, 0⟩
private def span : Solcore.Syntax.SourceSpan := ⟨⟨.main, "generic_match.solc"⟩, 0, 1⟩
private def site : StatementId := ⟨⟨owner, 0⟩⟩
private def scrutinee : ExpressionId := ⟨⟨owner, 1⟩⟩
private def hidden : Resolved.LocalId := ⟨owner, 0⟩
private def pattern : TypedMatchPattern := {source := .wildcard span span, type := .unit, resolution := .wildcard}
private def arm : TypedMatchCase := ⟨span, pattern, []⟩
private def resolution : MatchResolution := ⟨scrutinee, hidden, [arm, arm], some [], []⟩
private def scrutineeNode : ExpressionNode := {id := scrutinee, span, type := .unit, form := .tuple []}
private def statementNode : StatementNode := ⟨site, span, .unit, .matchWith resolution⟩
private def source : TypedSource := {
  owner, inputs := [], roots := [.statement site]
  nodes := [.statement statementNode, .expression scrutineeNode]}
private def signatures : ProgramSignatures := ⟨[], [], [], [], [], []⟩
private def context : SourceSemantics.Context := .ofSignatures signatures
private def control : ControlContext := ⟨.unit, 0⟩
private theorem catalogExists : (SourceCoreCompatibleCatalog.prepare signatures 20 [.unit]).toOption.isSome = true := by cbv
private def checked := (SourceCoreCompatibleCatalog.prepare signatures 20 [.unit]).toOption.get catalogExists
private def values := SourceCoreCompatibleValues.Context.initial checked
private def ambient : AmbientDefinitions checked.catalog.definitions := .append _ [⟨[.unit]⟩]
private def compilation : SourceCoreCompatibleDataMatches.Context := ⟨values, [], none, some ambient.definitions⟩
private def lowerExpression : SourceCoreCompatibleDataMatches.ExpressionLowerer := fun _ _ _ _ _ =>
  .ok ⟨.unit, LanguageResult.success .unit⟩
private def lowerBody : SourceCoreCompatibleDataMatches.BodyLowerer := fun _ _ _ _ _ _ _ => .ok (LocalLoop.fallthrough .unit)
private def reasonAt : ExpressionId → Word := fun _ => Word.zero
private def compiled : Expr := match SourceCoreCompatibleDataMatches.lowerWithReasons compilation lowerExpression lowerBody
    20 source [] site resolution .unit reasonAt Word.zero with | .ok code => code | .error _ => .unit
private theorem accepted : SourceCoreCompatibleDataMatches.lowerWithReasons compilation lowerExpression lowerBody
    20 source [] site resolution .unit reasonAt Word.zero = .ok compiled := by rfl

/-- Even equal request data appears three times: both source arms and default. -/
theorem finite_actual_children : ∃ requests,
    CompatibleMatchCertificates.Certificate compilation source [] site resolution .unit Word.zero
      (fun _ _ lowered => lowered = ⟨.unit, LanguageResult.success .unit⟩) (Occurs requests) compiled ∧
    requests.length = 3 ∧ ∀ request ∈ requests, ∃ fuel,
      lowerBody fuel source request.scope request.statements .unit reasonAt Word.zero = .ok request.code := by
  simpa only [resolution, List.length_cons, List.length_nil, Option.isSome_some, ↓reduceIte] using
    finite_of_lower (fun _ _ generated => Except.ok.inj generated.symm) accepted

private def request : Request := ⟨[(hidden, .unit)], [], LocalLoop.fallthrough .unit⟩
private def compiledPattern : SourceCoreCompatibleDataMatches.Pattern :=
  ⟨.unit, [], [], .lambda .unit (.sum .unit .unit) (.inRight .unit .unit)⟩
example : armRequests [(hidden, .unit)] resolution.cases
    [(compiledPattern, LocalLoop.fallthrough .unit), (compiledPattern, LocalLoop.fallthrough .unit)] ++
    fallbackRequests [(hidden, .unit)] resolution.defaultBody (LocalLoop.fallthrough .unit) =
      [request, request, request] := rfl

private theorem patternTyped : TypedMatchPatternHasType context pattern .unit [] 0 :=
  ⟨rfl, .wildcard, .wildcard, ⟨by simp, by simp⟩⟩
private theorem casesTyped : MatchCasesHaveType source control context .unit resolution.cases
    [BodyFacts.empty, BodyFacts.empty] := by
  exact .cons (.intro patternTyped (.nil _) (.nil _ _))
    (.cons (.intro patternTyped (.nil _) (.nil _ _)) (.nil _ _ _))
private theorem sourceSelected : Dynamic.MatchCasesSelect context .unit resolution.cases resolution.defaultBody (.arm [] []) :=
  .head (.intro .wildcard .wildcard)

theorem selected_context_is_source : ContextFor source context .unit resolution.cases resolution.defaultBody request context :=
  ContextFor.selected_arm_at request rfl casesTyped sourceSelected (.nil _)

private theorem unique : NodeOccurrencesUnique source := by cbv; decide
private theorem scrutineeTyped : ExpressionHasType source context scrutinee .unit := by
  have admitted : TypeAdmissible context .unit := .unit (by simp [TypeParameterBindersWellFormed, context, Context.ofSignatures])
  apply ExpressionHasType.ofOrdinary (node := scrutineeNode) (rawType := .unit) (lookupExpression?_sound (by cbv))
    (.tuple (.nil _)) admitted admitted
  · intro requirement member; cases member
  · exact .nil _
  · rfl
private abbrev expressionSyntax := CompatibleExpressionBuiltins.Syntax source
private theorem unitSyntax : expressionSyntax scrutinee :=
  .fragment (.fragment (.fragment (.fragment (.fragment (.primitive (.product (.literal (node := scrutineeNode) rfl .unit)))))))
private theorem syntaxTree (mode : Bool) : GenericImperativeMatch.Syntax source expressionSyntax context (.statements mode [site]) .unit := by
  apply GenericImperativeMatch.Syntax.matchWith (expressionSyntax := expressionSyntax) (node := statementNode) (scrutineeNode := scrutineeNode)
    (control := control) (caseFacts := [BodyFacts.empty, BodyFacts.empty]) rfl rfl (.inl rfl) rfl scrutineeTyped unitSyntax casesTyped
  · intro statements selected
    have same : statements = [] := Option.some.inj selected.symm
    subst statements
    exact ⟨context, _, .nil _ _⟩
  · rfl
  · intro arm member binder found; rfl
  · intro request childContext selected
    have empty : request.statements = [] := by
      cases selected with
      | @arm actualArm binders arity childContext member same typed extended =>
        have armEq : actualArm = arm := by simpa [resolution] using member
        exact same.trans (congrArg TypedMatchCase.body armEq)
      | default same => exact Option.some.inj same.symm
    rw [empty]
    exact .body (.nil (.inl rfl))
  · exact .body (.nil (.inr rfl))

private def program : SourceSemantics.Program := ⟨signatures, [], []⟩
private def environment : Dynamic.Environment := []
private def before : Dynamic.Heap := ⟨[]⟩
private def after : Dynamic.Heap := ⟨[{type := .unit, value := some .unit}]⟩
private def functionCompilation : SourceCoreFunctions.Context := ⟨⟨[], [], [], []⟩, ⟨owner, []⟩, [], 0, [], Word.zero⟩
private def noBody : SourceCoreFunctions.BodyLowerer := fun _ _ _ _ _ _ _ _ _ => .ok .unit
private def expressionPolicy (native : SourceCoreGeneralFunctions.CallableContext) : SourceCoreFunctions.Policy :=
  {SourceCoreCompatibleDataExpressions.functionPolicy 100 values with callables := SourceCoreGeneralFunctions.callablePolicy (some native) []}
private theorem noCoercions : ∀ id node, source.lookupExpression? id = some node → node.coercions = [] := by
  intro id node found
  have member := (lookupExpression?_sound found).1
  simp [source] at member
  subst member
  rfl
private theorem sourceTrace (mode : Bool) : TypedScopedStatements.Executes mode program context [] source environment before
    [site] context (.fallthrough environment) after := by
  have evaluated : Dynamic.ExpressionEvaluates program context [] source environment before scrutinee .unit before :=
    .intro (lookupExpression?_sound (show source.lookupExpression? scrutinee = some scrutineeNode from rfl)) (.tuple rfl .nil .nil) .nil
  have matched : Dynamic.StatementExecutes program context [] source environment before site context (.fallthrough environment) after :=
    .matchArm (lookupStatement?_sound (node := statementNode) rfl) rfl (lookupExpression?_sound (node := scrutineeNode) rfl)
      evaluated .append sourceSelected rfl rfl (.nil _) (.nil _ _) .nil
  exact TypedScopedStatements.prepend (lookupStatement?_sound (node := statementNode) rfl)
    (by intro _ _ _ impossible; cases impossible) matched (by cases mode <;> exact .control .nil)

private theorem hiddenSourceFresh : GenericImperativeMatch.MatchHiddenFresh source := by
  intro id node actualResolution found form
  have sameNode : node = statementNode := by
    have member := (lookupStatement?_sound found).1
    simpa [source] using member
  subst node
  have sameResolution : actualResolution = resolution := StatementForm.matchWith.inj form.symm
  subst actualResolution
  simp [SourceCoreDataPlaces.declaredBinders, SourceCoreDataPlaces.patternBinders,
    source, statementNode, scrutineeNode, resolution, arm, pattern]

section CompilerBridge
variable {layouts : SourceCoreAllocationLayouts.Prepared} {specialization : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {administrative : Core.Context} {definitions : DataEnvironment} {loopPolicy : SourceCoreLoops.Policy}
  (nativeContext : SourceCoreGeneralFunctions.CallableContext)
  (expressionPolicy : loopPolicy.lowerExpression = fun fuel source scope id reasonAt =>
    SourceCoreFunctions.lowerExpressionWithPolicy (expressionPolicy nativeContext) noBody fuel functionCompilation source scope id reasonAt)
  {invalidProjection : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Word}
  {invalidOperand : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Solcore.Syntax.ValueAssignOp → Word}
  {invalidUnary : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Word}
  {missingReason : SourceCoreElaboration.ErrorSite → Resolved.LocalId → TypeSystem.Ty → Word}
  (matched : CompatibleAssignmentStatements.AssignmentPolicy loopPolicy values invalidProjection invalidOperand missingReason)
  (unaryPolicy : CompatibleBitNotStatements.Policy loopPolicy values invalidProjection invalidUnary missingReason)
  (binderPolicy : ∀ scope binder, binder.scheme.quantified = [] →
    loopPolicy.lowerBinder source scope binder = SourceCoreCompatibleDataExpressions.lowerBinder values.checked source scope binder)
  (allocationPolicy : loopPolicy.sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator frame globals
    (layouts.allocatorAt specialization active onError)))
  (nativeChildren : ∀ current scope fuel id node lowered,
    current.typeVariables = [] → current.residualTypeVariables = false →
    current.signatures = values.checked.signatures → CompatibleExpressionReads.ScopeDeclarations source scope current →
    CompatibleExpressionBuiltins.Syntax source id → source.lookupExpression? id = some node → ExpressionHasType source current id node.type →
    loopPolicy.lowerExpression fuel source scope id reasonAt = .ok lowered →
    HasType (SourceCoreLocalCell.coreContext scope ++ administrative) lowered.expression (LanguageResult.resultType lowered.type) definitions)
  {matchCompilation : SourceCoreCompatibleDataMatches.Context}
  (matchPolicy : loopPolicy.lowerMatch = some (SourceCoreCompatibleDataMatches.lowerWithReasons matchCompilation))
  (matchValues : matchCompilation.values = values) (matchDefinitions : matchCompilation.definitions = definitions)
  (matchAllocator : matchCompilation.sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator frame globals
    (layouts.allocatorAt specialization active onError)))
  {scope : SourceCoreLocalCell.Scope}
  (declarations : CompatibleExpressionReads.ScopeDeclarations source scope context)
  {mode : Bool} {fuel : Nat} {selfReason : Word} {code : Expr} {nativeType : Ty}
  (accepted : SourceCoreLoops.lowerFlowStatementsWithPolicy loopPolicy fuel source scope [site] .unit reasonAt mode selfReason = .ok code)
  (nativeTyped : infer? (SourceCoreLocalCell.coreContext scope ++ administrative) code definitions = some nativeType)

include matchPolicy matchValues matchDefinitions matchAllocator expressionPolicy matched unaryPolicy binderPolicy allocationPolicy nativeChildren declarations accepted nativeTyped in
/-- Every builtin child is extracted from the actual expression lowerer. Only
source typing and actual native checker facts remain as static conditions. -/
theorem extracted : Nonempty (GenericImperativeMatch.Extraction layouts specialization active frame globals onError values source
    expressionSyntax (fun current => CompatibleExpressionBuiltins.Tree 100 values source current [] reasonAt)
    definitions administrative matchCompilation.solvedRequirements context scope (.statements mode [site]) .unit .unit code) := by
  apply GenericImperativeMatch.extraction_of_typed_flow (certificates := fun current => CompatibleExpressionBuiltins.Tree 100 values source current [] reasonAt) matchPolicy matchValues matchDefinitions matchAllocator (GenericImperativeMatch.MatchChildStatic.of_hidden (matchCompilation := matchCompilation) (certificates := fun current => CompatibleExpressionBuiltins.Tree 100 values source current [] reasonAt) (definitions := definitions) (administrative := administrative) hiddenSourceFresh) matched.read binderPolicy allocationPolicy ?_ matched unaryPolicy unique ?_
    (syntaxTree mode) rfl rfl rfl declarations (by cbv) accepted (infer_sound nativeTyped)
  · intro current closed residual signatures scope budget expression node lowered declarations syntaxValue found typed generated
    exact CompatibleExpressionBuiltins.tree_of_functions unique declarations signatures closed residual
      ⟨by intros; rfl, by intros; rfl, rfl, rfl⟩ nativeContext [] rfl
      (fun _ _ _ found => noCoercions _ _ found) syntaxValue found typed (expressionPolicy ▸ generated)
  · intro current scope budget expression lowered closed residual signatures declarations syntaxValue node found typed generated
    exact ⟨CompatibleExpressionBuiltins.tree_of_functions unique declarations signatures closed residual
      ⟨by intros; rfl, by intros; rfl, rfl, rfl⟩ nativeContext [] rfl
      (fun _ _ _ found => noCoercions _ _ found) syntaxValue found typed (expressionPolicy ▸ generated),
      nativeChildren current scope budget expression node lowered closed residual signatures declarations syntaxValue found typed generated⟩

include matchPolicy matchValues matchDefinitions matchAllocator expressionPolicy matched unaryPolicy binderPolicy allocationPolicy nativeChildren declarations accepted nativeTyped in
/-- The actual compiler receipt yields the match ledger at every recursive site.
Only diagnostic interpretation is deferred; there is no SiteLedgers or Ready input. -/
theorem accepted_ready_factory
    (sameLedger : matchCompilation.solvedRequirements = [])
    {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
    (valid : CompatibleExpressionLiterals.ContextValid [] context []) :
    ∃ certificate : GenericImperativeMatch.Extraction layouts specialization active frame globals onError values source
      expressionSyntax (fun current => CompatibleExpressionBuiltins.Tree 100 values source current [] reasonAt)
      definitions administrative matchCompilation.solvedRequirements context scope (.statements mode [site]) .unit .unit code,
      certificate.diagnostics registry faults → GenericImperativeMatch.Tree.Ready registry faults certificate.tree := by
  obtain ⟨certificate⟩ := extracted nativeContext expressionPolicy matched unaryPolicy binderPolicy allocationPolicy nativeChildren
    matchPolicy matchValues matchDefinitions matchAllocator declarations accepted nativeTyped
  exact ⟨certificate, fun diagnostics => certificate.ready diagnostics (sameLedger.symm ▸ valid) rfl⟩

end CompilerBridge

/-- The ledger used by the real fixed match policy is definitionally the caller's
ledger, even when the values catalog and emitted empty bodies are identical. -/
theorem actual_policy_ledger (solved : List SolvedRequirement)
    (assignments : SourceCoreAssignmentFaultSites.Table) (diagnostics : SourceCoreDataPlaceFaultSites.Program)
    (expression : SourceCoreLoops.ExpressionLowerer)
    (sourceCells : Option SourceCoreSourceCells.Allocator) (definitions : Option DataEnvironment) :
    let policy := SourceCoreCompatibleDataMatches.loopPolicy values solved assignments diagnostics ⟨owner, []⟩ expression sourceCells definitions
    let compilation : SourceCoreCompatibleDataMatches.Context := ⟨values, solved, sourceCells, definitions⟩
    policy.lowerMatch = some (SourceCoreCompatibleDataMatches.lowerWithReasons compilation) ∧
      compilation.solvedRequirements = solved := by
  exact ⟨rfl, rfl⟩

private def extractionWorkspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "enum Choice { Left(Word), Right(Word) }",
    "function sharedArms(seed: Word) returns (integer) { for (let i = 0; integerLt(wordToInteger(i), 2); i += 1) { match (Choice.Left(seed)) { case .Left(x) {} case .Right(y) {} default {} } } return wordToInteger(seed); }",
    "function scoped(seed: Word) returns (integer) { let total = seed; for (let i = 0; integerLt(wordToInteger(i), 2); i += 1) { match (Choice.Left(i)) { case .Left(0) { let x = 7; total += x; continue; } case .Left(x) { let y = x; total += y; } case .Right(y) {} default {} } } return wordToInteger(total); }"
  ]}] }

def run : IO Unit := do
  let checked ← SourceCompilerFeatureSupport.get "match extraction checker" (checkProgram extractionWorkspace)
  let shared ← SourceCompilerFeatureSupport.compileNamed checked "sharedArms"
  let scopeEntry ← SourceCompilerFeatureSupport.compileNamed checked "scoped"
  for seed in [0, 3] do
    let args := [SourceCompilerFeatureSupport.scalar seed]
    SourceCompilerFeatureSupport.require ((← shared.run args) == .integer seed) "equal empty arm bodies changed their source scopes"
    SourceCompilerFeatureSupport.require ((← scopeEntry.run args) == .integer (seed + 8)) "nested match/let/continue order changed"
    for fuel in [0, 7, 43] do
      shared.checkResume args (.integer seed) fuel
      scopeEntry.checkResume args (.integer (seed + 8)) fuel
  IO.println "match extraction: exact fixed ledger, duplicate empty arm scopes, lexical for/continue and resume GREEN"

end Tests.SourceCoreGenericImperativeMatchExtraction
end

section
-- leanmerge: from Solcore.Test.SourceCoreGenericImperativeMatchReadyFactory
/-! The fixed loop policy supplies actual match ledger provenance. Independent
source validity reaches distinct same-body arms, the default, and lexical
bindings without a second ledger-validity assumption. The ready factory leaves
all existing diagnostic laws explicit. This file has no runtime evaluator. -/
#check_failure Solcore.Frontend.SourceTypedRuntime.run
set_option autoImplicit false
set_option maxRecDepth 65536
namespace Tests.SourceCoreGenericImperativeMatchReadyFactory
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open SourceCoreCompatibleDataMatches CompatibleMatchCertificates CompatibleMatchArmScopes GenericMatchChildren
private def moduleId : Workspace.ModuleId := ⟨.main, ⟨[⟨"match_scoped_contexts", by decide⟩], by decide⟩⟩
private def owner : Resolved.DeclarationId := ⟨moduleId, 0⟩
private def span : Solcore.Syntax.SourceSpan := ⟨⟨.main, "match_scoped_contexts.solc"⟩, 0, 1⟩
private def site : StatementId := ⟨⟨owner, 0⟩⟩
private def hidden : Resolved.LocalId := ⟨owner, 2⟩
private def binder (index : Nat) : TypedBinder :=
  ⟨⟨owner, index⟩, toString index, .mono .unit, [], false, none⟩
private def pattern (index : Nat) : TypedMatchPattern := {
  source := .group span (.binder span (toString index)), type := .unit, resolution := .binder (binder index) }
private def arm (index : Nat) : TypedMatchCase := ⟨span, pattern index, []⟩
private def resolution : MatchResolution := ⟨⟨⟨owner, 1⟩⟩, hidden, [arm 0, arm 1], some [], []⟩
private def node : StatementNode := ⟨site, span, .unit, .matchWith resolution⟩
private def source : TypedSource := {owner, inputs := [], roots := [.statement site], nodes := [.statement node]}
private def signatures : ProgramSignatures := ⟨[], [], [], [], [], []⟩
private def context : SourceSemantics.Context := .ofSignatures signatures
private theorem admitted : TypeAdmissible context .unit := .unit (by simp [TypeParameterBindersWellFormed, context, Context.ofSignatures])
private theorem patternTyped (index : Nat) : TypedMatchPatternHasType context (pattern index) .unit [binder index] 0 := {
  type_eq := rfl, source_represents := .group (.binder rfl)
  resolution_type := .binder {
    scheme_eq := rfl, runtime := rfl
    wellFormed := by intro declaration installed; cases installed }
  binders_distinct := ⟨by simp, by simp⟩ }
private def armContext (index : Nat) : SourceSemantics.Context :=
  context.withLocal (binder index).id (binder index).scheme []
private theorem extended (index : Nat) : BindersExtend source.owner context [binder index] (armContext index) := by
  apply BindersExtend.cons (middle := armContext index)
  · apply BinderExtends.intro
    · exact {
        owned := rfl, scheme := SchemeWellFormed.monoAdmissible admitted
        quantified_fresh := by intro metavariable member; cases member
        monomorphic_requirements_empty := by intro mono; rfl }
    · simp [LocalFresh, context, Context.ofSignatures]
  · exact .nil _
private theorem catalogExists : (SourceCoreCompatibleCatalog.prepare signatures 20 [.unit]).toOption.isSome = true := by cbv
private def checked := (SourceCoreCompatibleCatalog.prepare signatures 20 [.unit]).toOption.get catalogExists
private def values := SourceCoreCompatibleValues.Context.initial checked
private def compilation : SourceCoreCompatibleDataMatches.Context := ⟨values, [], none, some checked.catalog.definitions⟩
private def hiddenScope : Scope := [(hidden, .unit)]
private def fallback : CertifiedPattern compilation.definitions := {
  pattern := ⟨.unit, [], [], .lambda .unit (.sum .unit .unit) (.inRight .unit .unit)⟩
  typed := .lambda .unit (.sum .unit .unit) (.inRight .unit .unit) }
private def compiled (index : Nat) : CertifiedPattern compilation.definitions :=
  match compilePattern compilation 20 source hiddenScope site span .unit (pattern index) with
  | .ok result => result | .error _ => fallback
private theorem firstAccepted : compilePattern compilation 20 source hiddenScope site span .unit (pattern 0) = .ok (compiled 0) := by rfl
private theorem secondAccepted : compilePattern compilation 20 source hiddenScope site span .unit (pattern 1) = .ok (compiled 1) := by rfl
private theorem emptyScope : CompatibleExpressionReads.ScopeDeclarations source [] context := by
  intro binder declared index type selected authentic
  cases selected
private theorem hiddenAbsent : hidden ∉ (SourceCoreDataPlaces.declaredBinders source).map (·.id) := by
  simp [SourceCoreDataPlaces.declaredBinders, SourceCoreDataPlaces.patternBinders,
    source, node, resolution, arm, pattern, binder, hidden]

private def request (index : Nat) : Request :=
  ⟨armScope hiddenScope (compiled index).pattern, [], LocalLoop.fallthrough .unit⟩
private def defaultRequest : Request := ⟨hiddenScope, [], LocalLoop.fallthrough .unit⟩

theorem first_scoped : ScopedContextFor source context [hidden] .unit resolution.cases resolution.defaultBody
    (request 0) (armContext 0) :=
  ScopedContextFor.compiled_arm (scope := hiddenScope) (arm := arm 0)
    (cases := resolution.cases) (fallback := resolution.defaultBody)
    (LocalLoop.fallthrough .unit) (List.mem_cons_self)
    (CompatiblePatternCertificates.certificate_of_compilePattern compilation 20 source hiddenScope site span .unit
      (pattern 0) (compiled 0) firstAccepted) rfl (patternTyped 0) (extended 0)

theorem second_scoped : ScopedContextFor source context [hidden] .unit resolution.cases resolution.defaultBody
    (request 1) (armContext 1) :=
  ScopedContextFor.compiled_arm (scope := hiddenScope) (arm := arm 1)
    (cases := resolution.cases) (fallback := resolution.defaultBody)
    (LocalLoop.fallthrough .unit) (List.mem_cons_of_mem _ List.mem_cons_self)
    (CompatiblePatternCertificates.certificate_of_compilePattern compilation 20 source hiddenScope site span .unit
      (pattern 1) (compiled 1) secondAccepted) rfl (patternTyped 1) (extended 1)

theorem default_scoped : ScopedContextFor source context [hidden] .unit resolution.cases resolution.defaultBody
    defaultRequest context := .default rfl rfl


private theorem valid : CompatibleExpressionLiterals.ContextValid [] context [] := by
  refine ⟨rfl, ⟨?_, ?_⟩, ?_⟩
  · simp [RequirementIdsUnique, context, SourceSemantics.Context.ofSignatures]
  · intro requirement member
    simp [context, SourceSemantics.Context.ofSignatures] at member
  · constructor
    · intro goal evidence found; cases found
    · intro predicate member
      simp [context, SourceSemantics.Context.ofSignatures] at member

theorem first_arm_context : CompatiblePatternLeaves.ContextValid compilation (armContext 0) :=
  CompatibleMatchContextFactory.of_context
    (CompatibleMatchContextFactory.scoped_context first_scoped valid)
    first_scoped.closed_fields.1 rfl rfl

theorem second_arm_context : CompatiblePatternLeaves.ContextValid compilation (armContext 1) :=
  CompatibleMatchContextFactory.of_context
    (CompatibleMatchContextFactory.scoped_context second_scoped valid)
    second_scoped.closed_fields.1 rfl rfl

theorem default_context : CompatiblePatternLeaves.ContextValid compilation context :=
  CompatibleMatchContextFactory.of_context
    (CompatibleMatchContextFactory.scoped_context default_scoped valid) rfl rfl rfl

/-- Both ordinary declarations and for initializers use this same independent
binder extension. Its local table differs while the ledger stays fixed. -/
theorem after_let_or_for_initializer (index : Nat) :
    CompatibleExpressionLiterals.ContextValid [] (armContext index) [] ∧
      CompatiblePatternLeaves.ContextValid compilation (armContext index) := by
  have extendedValid := CompatibleMatchMeaning.valid_binders [] valid (extended index)
  exact ⟨extendedValid, CompatibleMatchContextFactory.of_context extendedValid
    (extended index).signatures_eq rfl rfl⟩

/-- Equal value catalogs do not authenticate an unrelated, unused ledger. -/
theorem different_ledger_not_authenticated (entry : SolvedRequirement) :
    ¬ CompatiblePatternLeaves.ContextValid { compilation with solvedRequirements := [entry] } context := by
  intro wrong
  have ledger := wrong.ledger
  cases ledger

end Tests.SourceCoreGenericImperativeMatchReadyFactory

namespace Tests.SourceCoreGenericImperativeMatchReadyFactory.ActualPolicy
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open GenericImperativeMatch GenericImperativeMatch.Tree
open TypedLexicalWhile (absentRequest initializedRequest)
variable {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {values : GenericImperativeMatch.ValuesContext} {source : TypedSource}
  {expressionSyntax : ExpressionId → Prop}
  {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {definitions : DataEnvironment} {administrative : Core.Context}
  {solved : List SolvedRequirement} {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}

/-- The concrete compatible loop policy fixes the compilation ledger; the
actual match receipt, ordered child scopes and existing errors feed Ready.
There is no caller-supplied pattern context or runtime child contract. -/
theorem actual_fixed_match_ready
      {context scope mode id node resolution scrutineeNode rest expected type matched body selfReason control caseFacts}
      {found : source.lookupStatement? id = some node}
      (form : node.form = .matchWith resolution)
      {scrutineeFound : source.lookupExpression? resolution.scrutinee = some scrutineeNode}
      {scrutineeTyped : ExpressionHasType source context resolution.scrutinee scrutineeNode.type}
      {casesTyped : MatchCasesHaveType source control context scrutineeNode.type resolution.cases caseFacts}
      {defaultTyped : ∀ statements, resolution.defaultBody = some statements →
        ∃ finalContext facts, StatementsHaveType source control context statements finalContext facts}
      {compilation : SourceCoreCompatibleDataMatches.Context}
      {sameValues : compilation.values = values}
      (sameDefinitions : compilation.definitions = definitions)
      {allocator : compilation.sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator frame globals
        (layouts.allocatorAt owner active onError))}
      {requests : List GenericMatchChildren.Request}
      {receipt : CompatibleMatchCertificates.Certificate compilation source scope id resolution type selfReason
        (certificates context) (GenericMatchChildren.Occurs requests) matched}
      {ordinary : CompatibleMatchSelectionPrefix.Ordinary receipt}
      {children : ∀ request, request ∈ requests → ∀ childContext,
        GenericMatchChildren.ScopedContextFor source context (resolution.hiddenScrutinee :: scope.map Prod.fst) scrutineeNode.type resolution.cases resolution.defaultBody request childContext →
        Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
          childContext request.scope (.statements false request.statements) expected type request.code}
      {remaining : Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
        context scope (.statements mode rest) expected type body}
      {childErrors : ∀ request member childContext valid, Errors registry faults (children request member childContext valid)}
      {remainingErrors : Errors registry faults remaining}
      (childLedgers : ∀ request member childContext related, SiteLedgers solved registry faults (childErrors request member childContext related))
      (remainingErrorsLedger : SiteLedgers solved registry faults remainingErrors)
    (assignments : SourceCoreAssignmentFaultSites.Table)
    (diagnostics : SourceCoreDataPlaceFaultSites.Program)
    (expression : SourceCoreCompatibleDataMatches.ExpressionLowerer)
    (fixed : compilation = ⟨values, solved,
      some (SourceCoreCallableIndexedAllocationFrames.allocator frame globals (layouts.allocatorAt owner active onError)),
      some definitions⟩)
    {evidence : Dynamic.EvidenceEnvironment}
    (contextValid : CompatibleExpressionLiterals.ContextValid solved context evidence)
    (signatures : context.signatures = values.checked.signatures) :
    (SourceCoreCompatibleDataMatches.loopPolicy values solved assignments diagnostics owner expression
      (some (SourceCoreCallableIndexedAllocationFrames.allocator frame globals (layouts.allocatorAt owner active onError)))
      (some definitions)).lowerMatch = some (SourceCoreCompatibleDataMatches.lowerWithReasons compilation) ∧
    Ready registry faults (.matchWith found form scrutineeFound scrutineeTyped casesTyped defaultTyped compilation
      sameValues sameDefinitions allocator requests receipt ordinary children remaining) := by
  have policy := CompatibleMatchContextFactory.fixed_policy contextValid signatures assignments diagnostics owner expression
    (some (SourceCoreCallableIndexedAllocationFrames.allocator frame globals (layouts.allocatorAt owner active onError)))
    (some definitions)
  have sameLedger : compilation.solvedRequirements = solved := by rw [fixed]
  refine ⟨by simpa only [fixed] using policy.1, ?_⟩
  exact (@SiteLedgers.matchWith layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative solved registry faults context scope mode id node resolution scrutineeNode rest expected type matched body selfReason control caseFacts found form scrutineeFound scrutineeTyped casesTyped defaultTyped compilation sameValues sameDefinitions allocator requests receipt ordinary children remaining childErrors remainingErrors sameLedger childLedgers remainingErrorsLedger).ready contextValid signatures

end Tests.SourceCoreGenericImperativeMatchReadyFactory.ActualPolicy
end

section
-- leanmerge: from Solcore.Test.SourceCoreGenericMatch
/-! Actual match acceptance plus universally proved child reflection constructs
the independent source trace. The initial Core store contains an administrative
closure, so the hidden source location zero maps to Core location one. -/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
namespace Tests.SourceCoreGenericMatch
open Solcore Solcore.Frontend Solcore.Frontend.SourceInference
open Solcore.SourceSemantics Solcore.SourceSemantics.CoreLowering
open GenericMatchMeaning

private def moduleId : Workspace.ModuleId :=
  ⟨.main, ⟨[⟨"generic_match", by decide⟩], by decide⟩⟩
private def owner : Resolved.DeclarationId := ⟨moduleId, 0⟩
private def span : Syntax.SourceSpan := ⟨⟨.main, "generic_match.solc"⟩, 0, 1⟩
private def site : StatementId := ⟨⟨owner, 0⟩⟩
private def scrutinee : ExpressionId := ⟨⟨owner, 1⟩⟩
private def hidden : Resolved.LocalId := ⟨owner, 0⟩
private def pattern : TypedMatchPattern := { source := .wildcard span span, type := .unit, resolution := .wildcard }
private def resolution : MatchResolution := ⟨scrutinee, hidden, [⟨span, pattern, []⟩], some [], []⟩
private def node : ExpressionNode := { id := scrutinee, span, type := .unit, form := .tuple [] }
private def source : TypedSource := {
  owner, inputs := [], roots := [.statement site]
  nodes := [.statement ⟨site, span, .unit, .matchWith resolution⟩, .expression node]
}
private def checked : SourceCoreDataCatalog.Checked := ⟨{}, Core.DataEnvironment.isWellFormed_sound (by decide)⟩
private def compilation : SourceCoreDataMatches.Context := ⟨checked, ⟨[], [], [], [], [], []⟩, []⟩
private def model := GenericHeap.finitePayload compilation.checked.catalog compilation.signatures
private def context := SourceSemantics.Context.ofSignatures compilation.signatures
private def control : ControlContext := ⟨.unit, 0⟩
private def program : Program := ⟨compilation.signatures, [], []⟩
private def expression : SourceCoreDataMatches.ExpressionLowerer := fun _ _ _ id _ =>
  if id = scrutinee then .ok ⟨.unit, Core.LanguageResult.success .unit⟩ else .error (.missingExpression id)
private def body : SourceCoreDataMatches.BodyLowerer := fun _ _ _ statements _ _ _ =>
  if statements = [] then .ok (Core.LocalLoop.fallthrough .unit) else .error (.missingStatement site)
private def reasonAt : ExpressionId → Core.Word := fun _ => Core.Word.zero
private def expressionCertificate : DataMatchCertificates.ExpressionCertificate := fun _ id lowered =>
  id = scrutinee ∧ lowered = ⟨.unit, Core.LanguageResult.success .unit⟩
private def bodyCertificate : DataMatchCertificates.BodyCertificate := fun _ statements code =>
  statements = [] ∧ code = Core.LocalLoop.fallthrough .unit
private def faults : FaultRep := fun _ _ => False
private def code : Core.Expr :=
  match SourceCoreDataMatches.lowerWithReasons compilation expression body 10 source [] site resolution .unit reasonAt Core.Word.zero with
  | .ok code => code
  | .error _ => .unit
private theorem accepted : SourceCoreDataMatches.lowerWithReasons compilation expression body 10 source [] site resolution
    .unit reasonAt Core.Word.zero = .ok code := by rfl
private theorem expressionExtract : ∀ fuel scope id lowered,
    expression fuel source scope id reasonAt = .ok lowered → expressionCertificate scope id lowered := by
  intro fuel scope id lowered accepted
  unfold expression at accepted
  split at accepted
  · exact ⟨by assumption, (Except.ok.inj accepted).symm⟩
  · cases accepted
private theorem bodyExtract : ∀ fuel scope statements code,
    body fuel source scope statements .unit reasonAt Core.Word.zero = .ok code → bodyCertificate scope statements code := by
  intro fuel scope statements code accepted
  unfold body at accepted
  split at accepted
  · exact ⟨by assumption, (Except.ok.inj accepted).symm⟩
  · cases accepted

private theorem expressionMeaning : ExpressionReflects compilation model program context [] source expressionCertificate faults := by
  intro scope id lowered certified selected found mapping world admin environment canonical actual before store ξ value finalStore
    environments heaps locals layout evaluated
  rcases certified with ⟨rfl, rfl⟩
  have same : selected = node := Option.some.inj (found.symm.trans (show source.lookupExpression? scrutinee = some node from rfl))
  subst selected
  have coreEval : Core.Evaluates actual store ((Core.LanguageResult.success .unit).rename ξ) (.inRight .word .unit) store := .inRight .unit
  obtain ⟨rfl, rfl⟩ := Core.evaluation_deterministic evaluated coreEval
  refine ⟨.value .unit, before, mapping, world, .value ?_, .value .unit, heaps, .refl _, .refl _, .refl _ _, .refl _⟩
  exact .intro (lookupExpression?_sound found) (.tuple rfl .nil .nil) .nil

private theorem bodyMeaning : BodyReflects compilation model program control [] source bodyCertificate .unit .unit faults := by
  intro scope statements code certified context staticFinal facts typed mapping world admin environment canonical actual before store ξ value finalStore
    environments heaps locals layout evaluated
  rcases certified with ⟨rfl, rfl⟩
  have coreEval : Core.Evaluates actual store ((Core.LocalLoop.fallthrough .unit).rename ξ)
      (.inRight .word (.inLeft Core.LocalLoop.transferType (.inLeft .unit .unit))) store := .inRight (.inLeft (.inLeft .unit))
  obtain ⟨rfl, rfl⟩ := Core.evaluation_deterministic evaluated coreEval
  exact ⟨context, .fallthrough environment, before, mapping, world, .control .nil, .fallthrough _, heaps, .refl _, .refl _, .refl _ _, .refl _⟩

private theorem valid : DataPatternLeaves.ContextValid compilation context := {
  signatures := rfl, ledger := rfl
  valid := ⟨by simp [RequirementIdsUnique, context, SourceSemantics.Context.ofSignatures],
    by intro requirement member; simp [context, SourceSemantics.Context.ofSignatures] at member⟩
}
private theorem casesTyped : MatchCasesHaveType source control context .unit resolution.cases [.empty] :=
  .cons (.intro ⟨rfl, .wildcard, .wildcard, ⟨by decide, by decide⟩⟩ (.nil _) (.nil _ _)) (.nil _ _ _)
private theorem defaultTyped : ∀ {statements}, resolution.defaultBody = some statements →
    ∃ finalContext facts, StatementsHaveType source control context statements finalContext facts := by
  intro statements same
  have empty : statements = [] := (Option.some.inj same).symm
  subst statements
  exact ⟨context, .empty, .nil _ _⟩

private def admin : Core.Value := .closure .unit .unit .unit []
private def initialStore : Core.Store := [admin]
private def world : Core.StoreTyping := [.function .unit .unit]
private def finalStore : Core.Store := [admin, .inRight .unit .unit]
private def result : Core.Value := .inRight .word (.inLeft Core.LocalLoop.transferType (.inLeft .unit .unit))
private theorem run : Core.runStateful 150 (Core.State.initial code [] initialStore) = .done result finalStore := by cbv
private theorem heaps : GenericHeap.HeapRepresents model [] world ⟨[]⟩ initialStore :=
  GenericHeap.HeapRepresents.empty.allocate_administrative (.closure .nil .unit)

/-- The only execution premise is the kernel-checked Core run. Every child
semantic hypothesis above was proved universally over related initial states. -/
example : ∃ outcome after finalMap finalWorld,
    Dynamic.StatementExecutesOutcome program context [] source [] ⟨[]⟩ site context outcome after ∧
    OutcomeRepresents model finalMap finalWorld .unit .unit faults outcome result ∧
    GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
    GeneralHeap.LocationMap.Extends [] finalMap ∧ Core.WorldExtends world finalWorld ∧
    GeneralHeap.AdministrativePreserved [] initialStore finalMap finalStore ∧ Dynamic.HeapMetadataExtend ⟨[]⟩ after := by
  apply lowerWithReasons_reflects GenericMatchAllocation.finite_includes expressionExtract bodyExtract accepted
    expressionMeaning bodyMeaning valid (show source.lookupExpression? resolution.scrutinee = some node from rfl)
    casesTyped defaultTyped (DataHeap.EnvRepresents.nil Core.RuntimeEnvironmentHasTypes.nil) heaps
    Dynamic.EnvironmentAgrees.nil
    (ξ := Core.Renaming.id)
  · intro index value found; exact found
  · simpa using Core.runStateful_evaluation_sound run

end Tests.SourceCoreGenericMatch
end

section
-- leanmerge: from Solcore.Test.SourceCoreGenericMatchPreservation
/-! Actual match acceptance and universal child preservation compile an
independent source trace to finite Core evaluation. The initial Core store contains an administrative
closure, so the hidden source location zero maps to Core location one. -/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
namespace Tests.SourceCoreGenericMatchPreservation
open Solcore Solcore.Frontend Solcore.Frontend.SourceInference
open Solcore.SourceSemantics Solcore.SourceSemantics.CoreLowering
open GenericMatchMeaning

private def moduleId : Workspace.ModuleId :=
  ⟨.main, ⟨[⟨"generic_match", by decide⟩], by decide⟩⟩
private def owner : Resolved.DeclarationId := ⟨moduleId, 0⟩
private def span : Syntax.SourceSpan := ⟨⟨.main, "generic_match.solc"⟩, 0, 1⟩
private def site : StatementId := ⟨⟨owner, 0⟩⟩
private def scrutinee : ExpressionId := ⟨⟨owner, 1⟩⟩
private def hidden : Resolved.LocalId := ⟨owner, 0⟩
private def pattern : TypedMatchPattern := { source := .wildcard span span, type := .unit, resolution := .wildcard }
private def resolution : MatchResolution := ⟨scrutinee, hidden, [⟨span, pattern, []⟩], some [], []⟩
private def node : ExpressionNode := { id := scrutinee, span, type := .unit, form := .tuple [] }
private def source : TypedSource := {
  owner, inputs := [], roots := [.statement site]
  nodes := [.statement ⟨site, span, .unit, .matchWith resolution⟩, .expression node]
}
private def checked : SourceCoreDataCatalog.Checked := ⟨{}, Core.DataEnvironment.isWellFormed_sound (by decide)⟩
private def compilation : SourceCoreDataMatches.Context := ⟨checked, ⟨[], [], [], [], [], []⟩, []⟩
private def model := GenericHeap.finitePayload compilation.checked.catalog compilation.signatures
private def context := SourceSemantics.Context.ofSignatures compilation.signatures
private def control : ControlContext := ⟨.unit, 0⟩
private def program : Program := ⟨compilation.signatures, [], []⟩
private def expression : SourceCoreDataMatches.ExpressionLowerer := fun _ _ _ id _ =>
  if id = scrutinee then .ok ⟨.unit, Core.LanguageResult.success .unit⟩ else .error (.missingExpression id)
private def body : SourceCoreDataMatches.BodyLowerer := fun _ _ _ statements _ _ _ =>
  if statements = [] then .ok (Core.LocalLoop.fallthrough .unit) else .error (.missingStatement site)
private def reasonAt : ExpressionId → Core.Word := fun _ => Core.Word.zero
private def expressionCertificate : DataMatchCertificates.ExpressionCertificate := fun _ id lowered =>
  id = scrutinee ∧ lowered = ⟨.unit, Core.LanguageResult.success .unit⟩
private def bodyCertificate : DataMatchCertificates.BodyCertificate := fun _ statements code =>
  statements = [] ∧ code = Core.LocalLoop.fallthrough .unit
private def faults : FaultRep := fun _ _ => False
private def code : Core.Expr :=
  match SourceCoreDataMatches.lowerWithReasons compilation expression body 10 source [] site resolution .unit reasonAt Core.Word.zero with
  | .ok code => code
  | .error _ => .unit
private theorem accepted : SourceCoreDataMatches.lowerWithReasons compilation expression body 10 source [] site resolution
    .unit reasonAt Core.Word.zero = .ok code := by rfl
private theorem expressionExtract : ∀ fuel scope id lowered,
    expression fuel source scope id reasonAt = .ok lowered → expressionCertificate scope id lowered := by
  intro fuel scope id lowered accepted
  unfold expression at accepted
  split at accepted
  · exact ⟨by assumption, (Except.ok.inj accepted).symm⟩
  · cases accepted
private theorem bodyExtract : ∀ fuel scope statements code,
    body fuel source scope statements .unit reasonAt Core.Word.zero = .ok code → bodyCertificate scope statements code := by
  intro fuel scope statements code accepted
  unfold body at accepted
  split at accepted
  · exact ⟨by assumption, (Except.ok.inj accepted).symm⟩
  · cases accepted

private theorem unique : NodeOccurrencesUnique source := by
  unfold NodeOccurrencesUnique nodeOccurrenceIds source
  decide
private theorem node_unique {selected : ExpressionNode} (contains : ContainsExpression source scrutinee selected) : selected = node :=
  Option.some.inj ((lookupExpression?_complete unique contains).symm.trans (show source.lookupExpression? scrutinee = some node from rfl))

private theorem unit_outcome {environment : Dynamic.Environment} {before after : Dynamic.Heap} {outcome : Dynamic.ExpressionOutcome}
    (evaluated : Dynamic.ExpressionEvaluatesOutcome program context [] source environment before scrutinee outcome after) :
    outcome = .value .unit ∧ after = before := by
  cases evaluated with
  | value evaluated =>
    cases evaluated with
    | intro contains form coercions =>
      have same := node_unique contains
      subst_vars
      cases coercions
      cases form with
      | tuple _ elements packed => cases elements; cases packed; exact ⟨rfl, rfl⟩
    | generalizedLocal contains form =>
      have same := node_unique contains
      subst_vars
      cases form
  | fault fault =>
    cases fault with
    | missing absent => exact False.elim (Dynamic.ExpressionAbsentIn.excludes_contains absent
        (lookupExpression?_sound (show source.lookupExpression? scrutinee = some node from rfl)))
    | form contains fault =>
      have same := node_unique contains
      subst_vars
      cases fault with
      | tuple _ elements => cases elements
    | coercion contains form fault =>
      have same := node_unique contains
      subst_vars
      cases fault
    | generalizedLocalRequirement contains form | generalizedLocalCoercion contains form =>
      have same := node_unique contains
      subst_vars
      cases form

private theorem expressionMeaning : GenericMatchPreservation.ExpressionPreserves compilation model program context [] source expressionCertificate faults := by
  intro scope id lowered certified selected found mapping world admin environment canonical actual before store ξ outcome after
    environments heaps locals layout evaluated
  rcases certified with ⟨rfl, rfl⟩
  have same : selected = node := Option.some.inj (found.symm.trans (show source.lookupExpression? scrutinee = some node from rfl))
  subst selected
  obtain ⟨rfl, rfl⟩ := unit_outcome evaluated
  exact ⟨_, store, mapping, world, .inRight .unit, .value .unit, heaps, .refl _, .refl _, .refl _ _, .refl _⟩

private theorem bodyMeaning : GenericMatchPreservation.BodyPreserves compilation model program control [] source bodyCertificate .unit .unit faults := by
  intro scope statements code certified context staticFinal facts typed mapping world admin environment canonical actual before store ξ finalContext outcome after
    environments heaps locals layout evaluated
  rcases certified with ⟨rfl, rfl⟩
  cases evaluated with
  | control executed =>
    cases executed
    exact ⟨_, store, mapping, world, .inRight (.inLeft (.inLeft .unit)), .fallthrough _, heaps,
      .refl _, .refl _, .refl _ _, .refl _⟩
  | fault fault => cases fault

private theorem valid : DataPatternLeaves.ContextValid compilation context := {
  signatures := rfl, ledger := rfl
  valid := ⟨by simp [RequirementIdsUnique, context, SourceSemantics.Context.ofSignatures],
    by intro requirement member; simp [context, SourceSemantics.Context.ofSignatures] at member⟩
}
private theorem casesTyped : MatchCasesHaveType source control context .unit resolution.cases [.empty] :=
  .cons (.intro ⟨rfl, .wildcard, .wildcard, ⟨by decide, by decide⟩⟩ (.nil _) (.nil _ _)) (.nil _ _ _)
private theorem defaultTyped : ∀ {statements}, resolution.defaultBody = some statements →
    ∃ finalContext facts, StatementsHaveType source control context statements finalContext facts := by
  intro statements same
  have empty : statements = [] := (Option.some.inj same).symm
  subst statements
  exact ⟨context, .empty, .nil _ _⟩

private def admin : Core.Value := .closure .unit .unit .unit []
private def initialStore : Core.Store := [admin]
private def world : Core.StoreTyping := [.function .unit .unit]
private def finalStore : Core.Store := [admin, .inRight .unit .unit]
private def result : Core.Value := .inRight .word (.inLeft Core.LocalLoop.transferType (.inLeft .unit .unit))
private theorem run : Core.runStateful 150 (Core.State.initial code [] initialStore) = .done result finalStore := by cbv
private theorem heaps : GenericHeap.HeapRepresents model [] world ⟨[]⟩ initialStore :=
  GenericHeap.HeapRepresents.empty.allocate_administrative (.closure .nil .unit)

private theorem sourceExecution : Dynamic.StatementExecutesOutcome program context [] source [] ⟨[]⟩ site context
    (.fallthrough []) ⟨[⟨.unit, some .unit, none⟩]⟩ := by
  apply Dynamic.StatementExecutesOutcome.control
  apply Dynamic.StatementExecutes.matchArm
      (contains := show ContainsStatement source site ⟨site, span, .unit, .matchWith resolution⟩ from ⟨by simp [source], rfl⟩)
      (form_eq := rfl) (scrutinee_contains := lookupExpression?_sound (show source.lookupExpression? scrutinee = some node from rfl))
      (scrutinee_evaluates := Dynamic.ExpressionEvaluates.intro
        (lookupExpression?_sound (show source.lookupExpression? scrutinee = some node from rfl))
        (.tuple rfl .nil .nil) .nil)
      (allocate_hidden := Dynamic.Heap.Allocates.append)
      (select := Dynamic.MatchCasesSelect.head (Dynamic.PatternMatches.intro .wildcard .wildcard))
      (binders_eq := rfl) (values_eq := rfl) (binders_extend := BindersExtend.nil context)
      (allocate_bindings := Dynamic.BindersAllocate.nil _ _) (execute := Dynamic.StatementsExecute.nil)

/-- Independent source execution, actual lowering acceptance and universal
child preservation yield the Core evaluation with final heap/frame evidence. -/
example : ∃ value store finalMap finalWorld,
    Core.Evaluates [] initialStore code value store ∧
    OutcomeRepresents model finalMap finalWorld .unit .unit faults (.fallthrough []) value ∧
    GenericHeap.HeapRepresents model finalMap finalWorld ⟨[⟨.unit, some .unit, none⟩]⟩ store ∧
    GeneralHeap.LocationMap.Extends [] finalMap ∧ Core.WorldExtends world finalWorld ∧
    GeneralHeap.AdministrativePreserved [] initialStore finalMap store ∧
    Dynamic.HeapMetadataExtend ⟨[]⟩ ⟨[⟨.unit, some .unit, none⟩]⟩ := by
  have result := GenericMatchPreservation.lowerWithReasons_preserves GenericMatchAllocation.finite_includes
    expressionExtract bodyExtract accepted expressionMeaning bodyMeaning valid unique
    (show source.lookupExpression? resolution.scrutinee = some node from rfl)
    casesTyped defaultTyped (DataHeap.EnvRepresents.nil Core.RuntimeEnvironmentHasTypes.nil) heaps
    Dynamic.EnvironmentAgrees.nil (ξ := Core.Renaming.id)
    (show Core.ReadOnly.EnvironmentsAgree Core.Renaming.id [] [] from fun {_ _} found => found) sourceExecution
  simpa [model] using result

end Tests.SourceCoreGenericMatchPreservation
end

section
-- leanmerge: from Solcore.Test.SourceCoreGenericMatchScopedContexts
/-! Same-body arms and a same-body default retain different source scope IDs.
Actual compiled pattern scopes select the right independent context, while
duplicated equal requests remain in source order. Payload annotations are not
used to infer source context or native typing. -/
#check_failure Solcore.Frontend.SourceTypedRuntime.run
set_option autoImplicit false
set_option maxRecDepth 65536
namespace Tests.SourceCoreGenericMatchScopedContexts
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open SourceCoreCompatibleDataMatches CompatibleMatchCertificates CompatibleMatchArmScopes GenericMatchChildren
private def moduleId : Workspace.ModuleId := ⟨.main, ⟨[⟨"match_scoped_contexts", by decide⟩], by decide⟩⟩
private def owner : Resolved.DeclarationId := ⟨moduleId, 0⟩
private def span : Solcore.Syntax.SourceSpan := ⟨⟨.main, "match_scoped_contexts.solc"⟩, 0, 1⟩
private def site : StatementId := ⟨⟨owner, 0⟩⟩
private def hidden : Resolved.LocalId := ⟨owner, 2⟩
private def binder (index : Nat) : TypedBinder :=
  ⟨⟨owner, index⟩, toString index, .mono .unit, [], false, none⟩
private def pattern (index : Nat) : TypedMatchPattern := {
  source := .group span (.binder span (toString index)), type := .unit, resolution := .binder (binder index) }
private def arm (index : Nat) : TypedMatchCase := ⟨span, pattern index, []⟩
private def resolution : MatchResolution := ⟨⟨⟨owner, 1⟩⟩, hidden, [arm 0, arm 1], some [], []⟩
private def node : StatementNode := ⟨site, span, .unit, .matchWith resolution⟩
private def source : TypedSource := {owner, inputs := [], roots := [.statement site], nodes := [.statement node]}
private def signatures : ProgramSignatures := ⟨[], [], [], [], [], []⟩
private def context : SourceSemantics.Context := .ofSignatures signatures
private theorem admitted : TypeAdmissible context .unit := .unit (by simp [TypeParameterBindersWellFormed, context, Context.ofSignatures])
private theorem patternTyped (index : Nat) : TypedMatchPatternHasType context (pattern index) .unit [binder index] 0 := {
  type_eq := rfl, source_represents := .group (.binder rfl)
  resolution_type := .binder {
    scheme_eq := rfl, runtime := rfl
    wellFormed := by intro declaration installed; cases installed }
  binders_distinct := ⟨by simp, by simp⟩ }
private def armContext (index : Nat) : SourceSemantics.Context :=
  context.withLocal (binder index).id (binder index).scheme []
private theorem extended (index : Nat) : BindersExtend source.owner context [binder index] (armContext index) := by
  apply BindersExtend.cons (middle := armContext index)
  · apply BinderExtends.intro
    · exact {
        owned := rfl, scheme := SchemeWellFormed.monoAdmissible admitted
        quantified_fresh := by intro metavariable member; cases member
        monomorphic_requirements_empty := by intro mono; rfl }
    · simp [LocalFresh, context, Context.ofSignatures]
  · exact .nil _
private theorem catalogExists : (SourceCoreCompatibleCatalog.prepare signatures 20 [.unit]).toOption.isSome = true := by cbv
private def checked := (SourceCoreCompatibleCatalog.prepare signatures 20 [.unit]).toOption.get catalogExists
private def values := SourceCoreCompatibleValues.Context.initial checked
private def compilation : SourceCoreCompatibleDataMatches.Context := ⟨values, [], none, some checked.catalog.definitions⟩
private def hiddenScope : Scope := [(hidden, .unit)]
private def fallback : CertifiedPattern compilation.definitions := {
  pattern := ⟨.unit, [], [], .lambda .unit (.sum .unit .unit) (.inRight .unit .unit)⟩
  typed := .lambda .unit (.sum .unit .unit) (.inRight .unit .unit) }
private def compiled (index : Nat) : CertifiedPattern compilation.definitions :=
  match compilePattern compilation 20 source hiddenScope site span .unit (pattern index) with
  | .ok result => result | .error _ => fallback
private theorem firstAccepted : compilePattern compilation 20 source hiddenScope site span .unit (pattern 0) = .ok (compiled 0) := by rfl
private theorem secondAccepted : compilePattern compilation 20 source hiddenScope site span .unit (pattern 1) = .ok (compiled 1) := by rfl
private theorem emptyScope : CompatibleExpressionReads.ScopeDeclarations source [] context := by
  intro binder declared index type selected authentic
  cases selected
private theorem hiddenAbsent : hidden ∉ (SourceCoreDataPlaces.declaredBinders source).map (·.id) := by
  simp [SourceCoreDataPlaces.declaredBinders, SourceCoreDataPlaces.patternBinders,
    source, node, resolution, arm, pattern, binder, hidden]

private def request (index : Nat) : Request :=
  ⟨armScope hiddenScope (compiled index).pattern, [], LocalLoop.fallthrough .unit⟩
private def defaultRequest : Request := ⟨hiddenScope, [], LocalLoop.fallthrough .unit⟩

theorem first_scoped : ScopedContextFor source context [hidden] .unit resolution.cases resolution.defaultBody
    (request 0) (armContext 0) :=
  ScopedContextFor.compiled_arm (scope := hiddenScope) (arm := arm 0)
    (cases := resolution.cases) (fallback := resolution.defaultBody)
    (LocalLoop.fallthrough .unit) (List.mem_cons_self)
    (CompatiblePatternCertificates.certificate_of_compilePattern compilation 20 source hiddenScope site span .unit
      (pattern 0) (compiled 0) firstAccepted) rfl (patternTyped 0) (extended 0)

theorem second_scoped : ScopedContextFor source context [hidden] .unit resolution.cases resolution.defaultBody
    (request 1) (armContext 1) :=
  ScopedContextFor.compiled_arm (scope := hiddenScope) (arm := arm 1)
    (cases := resolution.cases) (fallback := resolution.defaultBody)
    (LocalLoop.fallthrough .unit) (List.mem_cons_of_mem _ List.mem_cons_self)
    (CompatiblePatternCertificates.certificate_of_compilePattern compilation 20 source hiddenScope site span .unit
      (pattern 1) (compiled 1) secondAccepted) rfl (patternTyped 1) (extended 1)

theorem default_scoped : ScopedContextFor source context [hidden] .unit resolution.cases resolution.defaultBody
    defaultRequest context := .default rfl rfl

theorem first_declarations : CompatibleExpressionReads.ScopeDeclarations source (request 0).scope (armContext 0) :=
  first_scoped.source_declarations (scope := []) (site := site) (node := node) (by rfl) rfl hiddenAbsent emptyScope

theorem second_declarations : CompatibleExpressionReads.ScopeDeclarations source (request 1).scope (armContext 1) :=
  second_scoped.source_declarations (scope := []) (site := site) (node := node) (by rfl) rfl hiddenAbsent emptyScope

theorem default_declarations : CompatibleExpressionReads.ScopeDeclarations source defaultRequest.scope context :=
  default_scoped.source_declarations (scope := []) (site := site) (node := node) (by rfl) rfl hiddenAbsent emptyScope

private theorem wrong_declarations : ¬ CompatibleExpressionReads.ScopeDeclarations source (request 0).scope (armContext 1) := by
  intro declarations
  have selected := declarations (binder 0).id (binder 0) 0 .unit (by rfl) (by rfl)
  have selected := Resolved.LocalScope.lookup?_iff.mpr selected
  simp [armContext, context, Context.ofSignatures, Context.withLocal, Resolved.LocalScope.lookup?, binder] at selected

/-- The old source-only relation admitted this context for the shared body.
Its scope refinement excludes it without using native payload types. -/
theorem wrong_arm_excluded : ¬ ScopedContextFor source context [hidden] .unit resolution.cases
    resolution.defaultBody (request 0) (armContext 1) := by
  intro related
  exact wrong_declarations
    (related.source_declarations (scope := []) (site := site) (node := node) (by rfl) rfl hiddenAbsent emptyScope)

theorem old_relation_admits_other_context : ContextFor source context .unit resolution.cases
    resolution.defaultBody (request 0) (armContext 1) :=
  .arm (List.mem_cons_of_mem _ List.mem_cons_self) rfl (patternTyped 1) (extended 1)

theorem arm_cannot_be_default : ¬ ScopedContextFor source context [hidden] .unit resolution.cases
    resolution.defaultBody (request 0) context := by
  intro related
  have declarations := related.source_declarations (scope := []) (site := site) (node := node)
    (by rfl) rfl hiddenAbsent emptyScope
  have selected := declarations (binder 0).id (binder 0) 0 .unit (by rfl) (by rfl)
  cases selected

theorem default_cannot_be_arm : ¬ ScopedContextFor source context [hidden] .unit resolution.cases
    resolution.defaultBody defaultRequest (armContext 0) := by
  intro related
  cases related with
  | @arm actual binders arity _ member statements typed extended ids =>
    have member : actual = arm 0 ∨ actual = arm 1 := by simpa [resolution] using member
    rcases member with rfl | rfl
    · have same := CompatiblePatternSourceBinders.pattern_binders typed
      simp [SourceCoreDataPlaces.patternBinders, arm, pattern] at same
      rw [← same] at ids
      have length := congrArg List.length ids
      simp [defaultRequest, hiddenScope] at length
    · have same := CompatiblePatternSourceBinders.pattern_binders typed
      simp [SourceCoreDataPlaces.patternBinders, arm, pattern] at same
      rw [← same] at ids
      have length := congrArg List.length ids
      simp [defaultRequest, hiddenScope] at length

theorem duplicate_requests_preserved :
    let requests := [request 0, request 0, request 1, defaultRequest]
    requests.length = 4 ∧ requests[0]? = requests[1]? ∧
      Occurs requests (request 0).scope [] (LocalLoop.fallthrough .unit) := by
  exact ⟨rfl, rfl, List.mem_cons_self⟩

theorem raw_payload_annotations_are_independent :
    let altered : Request := ⟨[((binder 0).id, .word), (hidden, .bool)], [], .unit⟩
    ScopedContextFor source context [hidden] .unit resolution.cases resolution.defaultBody altered (armContext 0) ∧
      CompatibleExpressionReads.ScopeDeclarations source altered.scope (armContext 0) := by
  have related : ScopedContextFor source context [hidden] .unit resolution.cases resolution.defaultBody
      ⟨[((binder 0).id, .word), (hidden, .bool)], [], .unit⟩ (armContext 0) :=
    .arm List.mem_cons_self rfl (patternTyped 0) (extended 0) rfl
  exact ⟨related, related.source_declarations (scope := []) (site := site) (node := node)
    (by rfl) rfl hiddenAbsent emptyScope⟩

theorem selected_source_arm_context (control : ControlContext) :
    ScopedContextFor source context [hidden] .unit resolution.cases resolution.defaultBody
      (request 0) (armContext 0) := by
  have typed : MatchCasesHaveType source control context .unit resolution.cases [.empty, .empty] :=
    .cons (.intro (patternTyped 0) (extended 0) (.nil control _))
      (.cons (.intro (patternTyped 1) (extended 1) (.nil control _)) (.nil _ _ _))
  have selected : Dynamic.MatchCasesSelect context .unit resolution.cases resolution.defaultBody
      (.arm [] [(binder 0, .unit)]) := .head (.intro (.group (.binder rfl)) .binder)
  exact ScopedContextFor.selected_arm_at (request 0) rfl rfl typed selected (extended 0)

theorem allocation_order :
    ([(binder 0, Ty.word), (binder 1, Ty.bool)].foldl
      (fun scope binding => (binding.1.id, binding.2) :: scope) hiddenScope).map Prod.fst =
      [(binder 1).id, (binder 0).id, hidden] :=
  scope_binder_ids _ _

example : (request 0).statements = (request 1).statements ∧ (request 0).statements = defaultRequest.statements := ⟨rfl, rfl⟩
example : (request 0).scope.map Prod.fst ≠ (request 1).scope.map Prod.fst := by decide
example : (request 0).scope.map Prod.fst ≠ defaultRequest.scope.map Prod.fst := by decide
example : ContextFor source context .unit resolution.cases resolution.defaultBody (request 0) (armContext 0) := first_scoped.forget
private theorem hiddenSourceFresh : GenericImperativeMatch.MatchHiddenFresh source := by
  intro id actualNode actualResolution found form
  have sameNode : actualNode = node := by
    have member := (lookupStatement?_sound found).1
    simpa [source] using member
  subst actualNode
  have sameResolution : actualResolution = resolution := StatementForm.matchWith.inj form.symm
  subst actualResolution
  exact hiddenAbsent

theorem automatic_child_scopes {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
    {definitions : DataEnvironment} {administrative : Core.Context} :
    GenericImperativeMatch.MatchChildStatic compilation source certificates definitions administrative :=
  GenericImperativeMatch.MatchChildStatic.of_hidden hiddenSourceFresh

end Tests.SourceCoreGenericMatchScopedContexts
end

section
-- leanmerge: from Solcore.Test.SourceCoreImperativeForReachableDiagnostics
#check_failure Solcore.Frontend.SourceTypedRuntime.run
/-! Reachable assignment diagnostics pass through the same ordinary statement,
while/for and header/post Trees. Concrete builtin and named consumers close
child meanings. Equal-only fixtures have an empty actual assignment table;
compound and RHS faults retain their effects and exact diagnostics. Match Ready
and function-body/catalog wrappers remain separate consumers. -/
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 65536
namespace Tests.SourceCoreImperativeForReachableDiagnostics
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open GeneralHeap ReadOnly CompatiblePayload CoreProof CallableAncestryPairedLookup
open TypedLexicalWhile (Scope ValuesContext)
open CallableIndexedHistory (NativeFrame)
open NamedImperativeForStatements
section Static
variable {checked : Checked} {base : Base checked}
  {prepared : SourceCoreCallableIndexedAncestry.Prepared base} {values : TypedLexicalWhile.ValuesContext}
  {ambient : AmbientDefinitions values.checked.catalog.definitions} {program : SourceSemantics.Program}
  {bodies : NamedCallExpressions.Bodies prepared values ambient.definitions program}
  {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {compilation : SourceCoreFunctions.Context} {fuel : Nat} {source : TypedSource}
  {expressionSyntax : ExpressionId → Prop} {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word}
  (functions : FunctionModel values.checked.catalog ambient)
  (definitions : layouts.definitions = ambient.definitions) (registered : frame.Registered ambient.definitions)
  {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends values.registry registry)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)
  (runtimeViews : FunctionRuntimeViews functions) (evidence : Dynamic.EvidenceEnvironment)
  (unique : NodeOccurrencesUnique source)
  (owners : (program.functions.map (fun definition => definition.body.owner)).Nodup)
  {faults : FunctionCalls.FaultRep}
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))
  (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((reasonAt id).add tag))
  (bodyUninitialized : ∀ body, body ∈ bodies → ∀ id location,
    faults (.uninitializedLocation location) (body.reasonAt id))
  (bodyMissing : ∀ body, body ∈ bodies → ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((body.reasonAt id).add tag))

include definitions registered extension faithful observations runtimeViews unique owners uninitialized missing bodyUninitialized bodyMissing in
/-- The finite statement tree and concrete expression/body certificates close
all runtime child obligations, including after source bindings, condition slots and seven-slot writes. The actual protected entry is retained as a runtime boundary. -/
theorem concrete_named_preserves {context : SourceSemantics.Context} {scope : TypedLexicalWhile.Scope} {mode : Bool}
    {statements : List StatementId} {expected : TypeSystem.Ty} {type : Ty} {code : Expr} {administrative : Core.Context}
    (tree : Tree bodies layouts owner active frame globals onError compilation fuel source expressionSyntax solved reasonAt administrative
      context scope (.statements mode statements) expected type code)
    (errors : GenericImperativeFor.Tree.ReachableErrors registry faults tree) :
    ProtectedWhile.Body.Preserves functions program evidence
      (administrative := administrative) (entry := NamedCallExpressions.Entry functions registry bodies compilation.administrativePrefix)
      (source := source) (context := context) (registry := registry) (faults := faults)
      (solved := solved) (frameLayout := frame) (globals := globals)
      (scope := scope) mode statements expected type code :=
  NamedImperativeForStatements.Tree.preserves_reachable functions definitions registered extension faithful observations runtimeViews evidence
    unique owners uninitialized missing bodyUninitialized bodyMissing tree errors

include definitions registered extension faithful observations runtimeViews unique owners uninitialized missing bodyUninitialized bodyMissing in
/-- Every completed native lexical tree reconstructs its independent source
trace. Actual captured code/environment and frame history come from the entry,
not from native typing or the source heap relation. -/
theorem concrete_named_reflects {context : SourceSemantics.Context} {scope : TypedLexicalWhile.Scope} {mode : Bool}
    {statements : List StatementId} {expected : TypeSystem.Ty} {type : Ty} {code : Expr} {administrative : Core.Context}
    (tree : Tree bodies layouts owner active frame globals onError compilation fuel source expressionSyntax solved reasonAt administrative
      context scope (.statements mode statements) expected type code)
    (errors : GenericImperativeFor.Tree.ReachableErrors registry faults tree) :
    ProtectedWhile.Body.Reflects functions program evidence
      (administrative := administrative) (entry := NamedCallExpressions.Entry functions registry bodies compilation.administrativePrefix)
      (source := source) (context := context) (registry := registry) (faults := faults)
      (solved := solved) (frameLayout := frame) (globals := globals)
      (scope := scope) mode statements expected type code :=
  NamedImperativeForStatements.Tree.reflects_reachable functions definitions registered extension faithful observations runtimeViews evidence
    unique owners uninitialized missing bodyUninitialized bodyMissing tree errors


include definitions registered extension faithful observations runtimeViews unique owners uninitialized missing bodyUninitialized bodyMissing in
/-- Initializers and the nested body inhabit the same recursive grammar. The
head is followed by its concrete tail with no runtime endpoint premise. -/
theorem concrete_for_preserves {context : SourceSemantics.Context} {scope : TypedLexicalWhile.Scope} {mode : Bool}
    {id : StatementId} {node : StatementNode} {items post : List ForItemForm}
    {condition : ExpressionId} {statements rest : List StatementId}
    {expected : TypeSystem.Ty} {type : Ty} {initialCode body : Expr} {administrative : Core.Context}
    (found : source.lookupStatement? id = some node) (form : node.form = .forLoop items condition post statements)
    (initial : Tree bodies layouts owner active frame globals onError compilation fuel source expressionSyntax solved reasonAt administrative
      context scope (.initializers items condition post statements) expected type initialCode)
    (initialErrors : GenericImperativeFor.Tree.ReachableErrors registry faults initial)
    (tail : Tree bodies layouts owner active frame globals onError compilation fuel source expressionSyntax solved reasonAt administrative
      context scope (.statements mode rest) expected type body)
    (tailErrors : GenericImperativeFor.Tree.ReachableErrors registry faults tail) :
    ProtectedWhile.Body.Preserves functions program evidence
      (administrative := administrative) (entry := NamedCallExpressions.Entry functions registry bodies compilation.administrativePrefix)
      (source := source) (context := context) (registry := registry) (faults := faults)
      (solved := solved) (frameLayout := frame) (globals := globals) (scope := scope)
      mode (id :: rest) expected type (LocalLoop.sequence type initialCode body) :=
  concrete_named_preserves functions definitions registered extension faithful observations runtimeViews evidence
    unique owners uninitialized missing bodyUninitialized bodyMissing (.forLoop found form initial tail)
    (.forLoop (found := found) (form := form) initialErrors tailErrors)

include definitions registered extension faithful observations runtimeViews unique owners uninitialized missing bodyUninitialized bodyMissing in
/-- Completed initializers, finite iterations and post are inverted before the
tail. Break/return skip post and continue/fallthrough run it in source order. -/
theorem concrete_for_reflects {context : SourceSemantics.Context} {scope : TypedLexicalWhile.Scope} {mode : Bool}
    {id : StatementId} {node : StatementNode} {items post : List ForItemForm}
    {condition : ExpressionId} {statements rest : List StatementId}
    {expected : TypeSystem.Ty} {type : Ty} {initialCode body : Expr} {administrative : Core.Context}
    (found : source.lookupStatement? id = some node) (form : node.form = .forLoop items condition post statements)
    (initial : Tree bodies layouts owner active frame globals onError compilation fuel source expressionSyntax solved reasonAt administrative
      context scope (.initializers items condition post statements) expected type initialCode)
    (initialErrors : GenericImperativeFor.Tree.ReachableErrors registry faults initial)
    (tail : Tree bodies layouts owner active frame globals onError compilation fuel source expressionSyntax solved reasonAt administrative
      context scope (.statements mode rest) expected type body)
    (tailErrors : GenericImperativeFor.Tree.ReachableErrors registry faults tail) :
    ProtectedWhile.Body.Reflects functions program evidence
      (administrative := administrative) (entry := NamedCallExpressions.Entry functions registry bodies compilation.administrativePrefix)
      (source := source) (context := context) (registry := registry) (faults := faults)
      (solved := solved) (frameLayout := frame) (globals := globals) (scope := scope)
      mode (id :: rest) expected type (LocalLoop.sequence type initialCode body) :=
  concrete_named_reflects functions definitions registered extension faithful observations runtimeViews evidence
    unique owners uninitialized missing bodyUninitialized bodyMissing (.forLoop found form initial tail)
    (.forLoop (found := found) (form := form) initialErrors tailErrors)

end Static

section Builtin
open BuiltinImperativeFor
open TypedScopedStatements (Executes)
open TypedLexicalWhile (FlowRep)
open TypedLexicalControl (LexicalResult)
variable {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {readFuel : Nat} {values : TypedLexicalWhile.ValuesContext} {source : TypedSource} {solved : List SolvedRequirement}
  {reasonAt : ExpressionId → Word} {administrative : Core.Context}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient)
  (definitions : layouts.definitions = ambient.definitions) (registered : frame.Registered ambient.definitions)
  {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends values.registry registry)
  (program : SourceSemantics.Program) (evidence : Dynamic.EvidenceEnvironment)
  {faults : FunctionCalls.FaultRep}
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))
  (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((reasonAt id).add tag))
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)
  (functionTypes : FunctionRuntimeViews functions)

include definitions registered extension uninitialized missing faithful observations functionTypes in
theorem concrete_builtin_preserves {context : SourceSemantics.Context} {scope : TypedLexicalWhile.Scope} {mode : Bool} {statements : List StatementId}
    {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (tree : BuiltinImperativeFor.Tree layouts owner active frame globals onError readFuel values source solved reasonAt ambient.definitions administrative
      context scope (.statements mode statements) expected type code)
    (errors : GenericImperativeFor.Tree.ReachableErrors registry faults tree)
    (contextValid : CompatibleExpressionLiterals.ContextValid solved context evidence)
    (unique : NodeOccurrencesUnique source)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {contextLocation : Location} {native : NativeFrame}
    {outcome : Dynamic.ControlOutcome} {resultContext : SourceSemantics.Context}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native))
    (unmapped : contextLocation ∉ mapping)
    (trace : Executes mode program context evidence source environment before statements resultContext outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (code.rename ξ) value finalStore ∧
      FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      LexicalResult values.checked ambient.definitions finalMap finalWorld administrative source.owner
        context scope environment resultContext after := by
  apply BuiltinImperativeFor.Tree.preserves_reachable (functions := functions) (tree := tree)
  all_goals assumption

include definitions registered extension uninitialized missing faithful observations functionTypes in
theorem concrete_builtin_reflects {context : SourceSemantics.Context} {scope : TypedLexicalWhile.Scope} {mode : Bool} {statements : List StatementId}
    {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (tree : BuiltinImperativeFor.Tree layouts owner active frame globals onError readFuel values source solved reasonAt ambient.definitions administrative
      context scope (.statements mode statements) expected type code)
    (errors : GenericImperativeFor.Tree.ReachableErrors registry faults tree)
    (contextValid : CompatibleExpressionLiterals.ContextValid solved context evidence)
    (unique : NodeOccurrencesUnique source)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
    {store finalStore : Store} {ξ : Renaming} {contextLocation : Location} {native : NativeFrame} {value : Value}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native))
    (unmapped : contextLocation ∉ mapping)
    (evaluated : Evaluates actual store (code.rename ξ) value finalStore) :
    ∃ resultContext outcome after finalMap finalWorld,
      Executes mode program context evidence source environment before statements resultContext outcome after ∧
      FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      LexicalResult values.checked ambient.definitions finalMap finalWorld administrative source.owner
        context scope environment resultContext after := by
  apply BuiltinImperativeFor.Tree.reflects_reachable (functions := functions) (tree := tree)
  all_goals assumption

end Builtin

section Receipt
variable {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {values : TypedLexicalWhile.ValuesContext} {source : TypedSource} {context : SourceSemantics.Context}
  {expressionSyntax : ExpressionId → Prop}
  {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {definitions : DataEnvironment} {administrative : Core.Context} {scope : TypedLexicalWhile.Scope} {type : Ty}
  {assignment : AssignmentResolution} {rhs : ExpressionId}
  (head : GenericAssignmentStatements.Head values source context (certificates context) scope administrative definitions assignment .equal rhs)
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  (missing : ∀ {root resolved reason token count},
    CompatibleMixedRoute.FaultToken values.checked registry root head.prepared.steps resolved reason token count → faults reason token)
  (uninitialized : ∀ location, faults (.uninitializedLocation location) head.prepared.invalidProjection)

include missing uninitialized in
/-- Equal introduces no operand-token law at a statement position. -/
theorem equal_statement_receipt {id : StatementId} {node : StatementNode} {mode : Bool}
    {statements : List StatementId} {expected : TypeSystem.Ty} {code : Expr}
    (found : source.lookupStatement? id = some node) (form : node.form = .assignValue assignment .equal rhs)
    (tail : GenericImperativeFor.Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
      context scope (.statements mode statements) expected type code)
    (errors : GenericImperativeFor.Tree.ReachableErrors registry faults tail) :
    GenericImperativeFor.Tree.ReachableErrors registry faults (.assign found form head tail) :=
  .assign (found := found) (form := form) errors
    (GenericAssignmentStatements.Head.ReachableErrors.equal missing uninitialized)

include missing uninitialized in
/-- The initializer position uses exactly the same policy and static Tree. -/
theorem equal_initializer_receipt {items post : List ForItemForm} {condition : ExpressionId}
    {statements : List StatementId} {expected : TypeSystem.Ty} {code : Expr}
    (tail : GenericImperativeFor.Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
      context scope (.initializers items condition post statements) expected type code)
    (errors : GenericImperativeFor.Tree.ReachableErrors registry faults tail) :
    GenericImperativeFor.Tree.ReachableErrors registry faults (.initializerAssign head tail) :=
  .initializerAssign errors (GenericAssignmentStatements.Head.ReachableErrors.equal missing uninitialized)

/-- The reachable receipt cannot be strengthened to the old operand law for
an empty diagnostic interpretation. -/
theorem equal_strict_impossible (noOperand : ∀ token, ¬ faults (.invalidAssignmentOperands .equal) token) :
    ¬ head.Errors registry faults := by
  intro errors
  exact noOperand _ errors.operands

end Receipt

private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := []
  mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "function copied(value: Word) returns (Word) { let local = value; return local; }",
    "function bad(value: Word) returns (Word) { let local = value; let gap: Word; return gap; }",
    "function equalLoops(seed: Word) returns (Word) { let result = 0; for (let outer: Word, outer = copied(0); outer < 1; let post: Word, post = copied(outer + 1), outer = post) { let inner = 0; while (inner < 1) { result = copied(seed); inner = inner + 1; if (inner < 1) { continue; } break; } } return result; }",
    "function builtinEqual(seed: Word) returns (integer) { let root = wordFromInteger(wordToInteger(seed)); for (root = wordFromInteger(wordToInteger(seed)); integerEq(wordToInteger(root), wordToInteger(seed)); root = 99) { break; } return wordToInteger(root); }",
    "function returnSkipsPost(seed: Word) returns (Word) { let root = 0; for (let index = 0; true; root = bad(seed)) { while (true) { root = copied(seed); return root; } } return 99; }",
    "function bodyRhsFault(seed: Word) returns (Word) { let root = 1; for (let index = 0; true; root = 99) { while (true) { root = copied(seed); root = bad(seed); } } return 99; }",
    "function bodyCompound(seed: Word) returns (Word) { let root: Word; for (let index = 0; true; index = 99) { while (true) { index = copied(1); root += copied(seed); } } return 99; }",
    "function postRhsFault(seed: Word) returns (Word) { let root = 0; for (let index = 0; true; let post: Word, post = bad(seed), root = 99) { root = copied(seed); continue; } return 99; }"
  ]}]
}

open Tests.SourceCompilerFeatureSupport in
private def sourceFor (entry : Entry) (name : String) : IO TypedSource := do
  let key ← match entry.cached.sourceProgram.signatures.functions.filter (·.name == name) with
    | [signature] => pure (SourceSpecialization.SpecializationKey.mk signature.id [])
    | _ => throw (IO.userError s!"missing checked function {name}")
  let exact ← get "actual specialized source" (SourceCompilationPlan.exactSpecialization entry.cached.validationPlan key)
  pure exact.function.typedBody

open Tests.SourceCompilerFeatureSupport in
private def failure (entry : Entry) (expected : SourceCoreFaultSites.Diagnostic)
    (expectedCells : List (TypeSystem.Ty × Option SourceCoreExecution.Value)) : IO Unit := do
  let invocation ← entry.invoke [scalar 7]
  let token ← match invocation.outcome with
    | .failed token _ => pure token
    | _ => throw (IO.userError "expected a guarded language failure")
  require (token != Word.zero && decide ((← invocation.diagnostic token) = some expected))
    "guarded failure lost the exact decoded diagnostic"
  entry.checkCells [scalar 7] expectedCells
  let complete ← entry.audit [scalar 7]
  match complete.observation with
  | .fault error _ => require (decide (error = expected.error)) "guarded failure priority changed"
  | _ => throw (IO.userError "native source observation lost the failure")
  for fuel in [0, 7, 43] do
    let pending ← entry.audit [scalar 7] fuel
    let resumed ← get "native guarded resume" (pending.resume 300000)
    require ((← nativeObservation resumed) == (← nativeObservation complete))
      "guarded resume changed the failure or actual store prefix"
    let pending ← entry.invoke [scalar 7] {executionOptions with executionFuel := fuel}
    match pending.outcome with
    | .outOfFuel checkpoint =>
      match ← checkpoint.resume 300000 1024 with
      | .failed resumedToken session =>
        let diagnostic ← get "resumed guarded diagnostic" (session.diagnostic entry.key resumedToken)
        require (resumedToken == token && decide (diagnostic = some expected))
          "public guarded resume changed the diagnostic"
      | _ => throw (IO.userError "public guarded resume lost the failure")
    | _ => throw (IO.userError "small guarded budget did not suspend")

open Tests.SourceCompilerFeatureSupport in
private def cells (values : List (Option Nat)) : List (TypeSystem.Ty × Option SourceCoreExecution.Value) :=
  values.map fun value => (.word, value.map scalar)

open Tests.SourceCompilerFeatureSupport in
def run : IO Unit := do
  let program ← get "reachable imperative fixtures" (checkProgram workspace)
  for (name, expectedCells) in [
      ("equalLoops", [some 7, some 7, some 1, some 0, some 0, some 1, some 7, some 7, some 1, some 1, some 1]),
      ("builtinEqual", [some 7, some 7]),
      ("returnSkipsPost", [some 7, some 7, some 0, some 7, some 7])] do
    let entry ← compileNamed program name
    let source ← sourceFor entry name
    let table ← get "equal statement/loop table" (SourceCoreAssignmentFaultSites.prepare source Core.wordModulus)
    require (table.sites.isEmpty && table.diagnostic? Word.zero == none)
      "ordinary equal introduced an unreachable operand token"
    let expected : SourceCoreExecution.Value := if name == "builtinEqual" then .integer 7 else scalar 7
    require ((← entry.run [scalar 7]) == expected) "equal loop control or scope changed"
    entry.checkCells [scalar 7] (cells expectedCells)
    let complete ← entry.audit [scalar 7]
    for fuel in [0,7,43] do
      entry.checkResume [scalar 7] expected fuel
      let pending ← entry.audit [scalar 7] fuel
      let resumed ← get "native equal loop resume" (pending.resume 300000)
      require ((← nativeObservation complete) == (← nativeObservation resumed))
        "equal resume changed the complete native store"
  for (name, expectedCells) in [
      ("bodyRhsFault", [some 7, some 7, some 0, some 7, some 7, some 7, some 7, none]),
      ("postRhsFault", [some 7, some 7, some 0, some 7, some 7, none, some 7, some 7, none])] do
    let entry ← compileNamed program name
    let source ← sourceFor entry name
    let table ← get "RHS-failed equal table" (SourceCoreAssignmentFaultSites.prepare source Core.wordModulus)
    require table.sites.isEmpty "RHS failure introduced an equal operand token"
    let badSource ← sourceFor entry "bad"
    let (node, binder) ← match badSource.nodes.findSome? fun
        | .expression node => match node.form with | .reference "gap" (.local binder) => some (node,binder) | _ => none
        | _ => none with
      | some selected => pure selected | none => throw (IO.userError "callee failure occurrence missing")
    failure entry {error := .uninitializedLocal binder, site := .occurrence node.id.occurrence, span := some node.span}
      (cells expectedCells)
  let entry ← compileNamed program "bodyCompound"
  let source ← sourceFor entry "bodyCompound"
  let table ← get "compound body table" (SourceCoreAssignmentFaultSites.prepare source 100)
  let node ← match source.nodes.findSome? fun
      | .statement node => match node.form with | .assignValue _ .add _ => some node | _ => none
      | _ => none with
    | some selected => pure selected | none => throw (IO.userError "compound body occurrence missing")
  require (table.length == 1 && table.sites.all fun site => decide
    (site.site = .occurrence node.id.occurrence ∧ site.span = node.span ∧ site.rhsType = .word ∧ site.kind = .value .add))
    "compound body lost exact raw fault metadata"
  failure entry {
    error := .invalidAssignmentOperands .add none (some .word),
    site := .occurrence node.id.occurrence, span := some node.span}
    (cells [some 7, none, some 1, some 1, some 1, some 7, some 7])
  IO.println "reachable imperative/for diagnostics: same grammar, empty equal table, concrete builtin/named children, exact effects/faults and resume GREEN"

end Tests.SourceCoreImperativeForReachableDiagnostics
end

section
-- leanmerge: from Solcore.Test.SourceCoreImperativeNativePolicyTyping
/-! A concrete typed callback profile exercises the actual statement/header
compiler without assuming the whole body's native type. The profile covers
Word/Bool constants and ordinary Word cells. It claims native typing only.
Public fixtures separately retain real callback execution and resumption. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 65536
namespace Tests.SourceCoreImperativeNativePolicyTyping
open Solcore Core Frontend SourceInference SourceSemantics.CoreLowering
open ImperativeNativePolicyTyping

private def expressions : SourceCoreLoops.ExpressionLowerer := fun _ source _ id _ =>
  match source.lookupExpression? id with
  | none => .error (.traversalExhausted (.occurrence id.occurrence))
  | some node => match node.type with
    | .word => .ok ⟨.word, LanguageResult.success (.word (Word.ofNatModulo 7))⟩
    | .bool => .ok ⟨.bool, LanguageResult.success (.bool false)⟩
    | _ => .error (.traversalExhausted (.occurrence id.occurrence))

private def policy : SourceCoreLoops.Policy := {
  lowerExpression := expressions
  lowerBinder := fun _ _ _ => .ok .word
  lowerAssignment := fun source _ _ _ => .error (.traversalExhausted (.declaration source.owner)) }

/-- Native laws for real callbacks, including both actual default allocation
wrappers. Unsupported assignment/match callbacks cannot manufacture code. -/
theorem callback_laws (definitions : DataEnvironment) (administrative : Core.Context) :
    PolicyLaws definitions administrative (fun _ _ => True) policy := by
  constructor
  · intro fuel source scope id reasonAt lowered _ accepted
    change expressions fuel source scope id reasonAt = .ok lowered at accepted
    unfold expressions at accepted
    cases found : source.lookupExpression? id with
    | none => simp [found] at accepted
    | some node =>
      simp only [found] at accepted
      cases typeEq : node.type <;> simp only [typeEq] at accepted <;> try cases accepted
      rename_i constructor
      cases constructor with
      | declaration id => cases accepted
      | builtin builtin =>
        cases builtin <;> cases accepted
        all_goals exact LanguageResult.success_hasType (by constructor)
  · intro source scope binder type _ accepted
    cases accepted
    exact ⟨.word, True.intro⟩
  · intro source scope binder payload output body code _ payloadWF _ bodyTyped accepted
    change Except.ok (LocalSequence.letUninitialized payload body) = Except.ok code at accepted
    cases accepted
    exact LocalSequence.letUninitialized_hasType payloadWF
      (by simpa [context, SourceCoreLocalCell.coreContext, OptionalCell.referenceType] using bodyTyped)
  · intro source scope binder payload output initializer body code _ _ outputWF initialTyped bodyTyped accepted
    change Except.ok (LocalSequence.letInitialized output payload initializer body) = Except.ok code at accepted
    cases accepted
    exact LocalSequence.letInitialized_hasType outputWF initialTyped
      (by simpa [context, SourceCoreLocalCell.coreContext, OptionalCell.referenceType] using bodyTyped)
  · intro source scope binder payload output initializer body code _ payloadWF outputWF initialTyped bodyTyped accepted
    exact CaptureCopyTyping.letInitializedSnapshot_none_hasType payloadWF outputWF initialTyped bodyTyped accepted
  · intro fuel source scope site assignment operator rhs output body reasonAt code _ _ _ accepted
    cases operator <;> simp [SourceCoreLoops.assignValue, policy, bind, Except.bind] at accepted
  · intro callback source scope site assignment output body code selected
    cases selected
  · intro callback fuel source scope site assignment output body reasonAt code selected
    cases selected
  · intro callback flow fuel source scope id resolution type reasonAt selfReason code selected
    cases selected

private def moduleId : Workspace.ModuleId := ⟨.main, ⟨[⟨"imperative_native", by decide⟩], by decide⟩⟩
private def owner : Resolved.DeclarationId := ⟨moduleId, 0⟩
private def span : Solcore.Syntax.SourceSpan := ⟨⟨.main, "imperative_native.solc"⟩, 0, 1⟩
private def expression (index : Nat) : ExpressionId := ⟨⟨owner, index⟩⟩
private def statement (index : Nat) : StatementId := ⟨⟨owner, index + 2⟩⟩
private def binder (index : Nat) : TypedBinder := ⟨⟨owner, index⟩, "value", .mono .word, [], false, none⟩
private def wordNode : ExpressionNode := { id := expression 0, span, type := .word, form := .literal (.decimal "7") }
private def boolNode : ExpressionNode := { id := expression 1, span, type := .bool, form := .reference "false" (.builtinBoolean false) }
private def absent : StatementNode := ⟨statement 0, span, .unit, .letDecl (binder 0) none⟩
private def present : StatementNode := ⟨statement 1, span, .unit, .letDecl (binder 1) (some (expression 0))⟩
private def conditional : StatementNode := ⟨statement 2, span, .unit, .ifThen (expression 1) [statement 6] (some [])⟩
private def whileNode : StatementNode := ⟨statement 3, span, .unit, .whileLoop (expression 1) [statement 7]⟩
private def forNode : StatementNode := ⟨statement 4, span, .unit,
  .forLoop [.letDecl (binder 2) (some (expression 0))] (expression 1) [.expression (expression 0)] [statement 7]⟩
private def returned : StatementNode := ⟨statement 5, span, .word, .returnStmt (some (expression 0))⟩
private def breaking : StatementNode := ⟨statement 6, span, .unit, .breakStmt⟩
private def continuing : StatementNode := ⟨statement 7, span, .unit, .continueStmt⟩
private def statements : List StatementId := [statement 0, statement 1, statement 2, statement 3, statement 4, statement 5]
private def source : TypedSource := {
  owner, inputs := [], roots := statements.map (.statement ·)
  nodes := [.expression wordNode, .expression boolNode, .statement absent, .statement present,
    .statement conditional, .statement whileNode, .statement forNode, .statement returned,
    .statement breaking, .statement continuing] }
private def reasonAt : ExpressionId → Word := fun _ => Word.ofNatModulo 29
private def action := SourceCoreLoops.lowerStatementsWithPolicy policy 32 source [] statements .word reasonAt
  (Word.ofNatModulo 31) (Word.ofNatModulo 37)

/-- All allocated scopes, loop children and finish are derived from the actual
accepted compiler action under arbitrary hidden administrative types. -/
theorem accepted_fixture {code : Expr} (administrative : Core.Context)
    (accepted : action = .ok code) :
    HasType administrative code (LanguageResult.resultType .word) [] := by
  simpa [context, SourceCoreLocalCell.coreContext] using
    (body_native (callback_laws [] administrative) True.intro Ty.WellFormed.word accepted)

/-- The interface rejects a callback that reports Word while emitting Unit.
Successful result annotations alone do not establish a native type. -/
theorem wrong_callback_rejected :
    ¬ PolicyLaws [] [] (fun _ _ => True)
      {policy with lowerExpression := fun _ _ _ _ _ => .ok ⟨.word, .unit⟩} := by
  intro laws
  have typed := laws.expression 0 source [] (expression 0) reasonAt ⟨.word, .unit⟩ True.intro rfl
  cases typed

private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content :=
    "function make(seed: Word) returns (function() returns (Word)) { return lam() -> Word { let value: Word = seed; for (let i: Word = 0; i < 3; i += 1) { value += 1; } while (value < 6) { value += 1; } return value; }; }"}] }

def run : IO Unit := do
  let code ← SourceCompilerFeatureSupport.get "imperative native compiler fixture" action
  let expected := LanguageResult.resultType .word
  for hidden in [[], [.integer, .function .unit .word]] do
    SourceCompilerFeatureSupport.require (Core.infer? hidden code [] == some expected)
      "imperative traversal lost its native type under hidden slots"
  let initial := State.initial code
  let final ← match Core.runStateful 100000 initial with
    | .done value store => pure (value, store)
    | _ => throw (IO.userError "typed imperative fixture did not complete")
  SourceCompilerFeatureSupport.require (final.1 == .inRight .word (.word (Word.ofNatModulo 7)))
    "imperative native fixture returned the wrong result"
  for spent in [0, 13, 67] do
    let resumed := match Core.runStateful spent initial with
      | .outOfFuel checkpoint => Core.runStateful 100000 checkpoint
      | done => done
    match resumed with
    | .done value store =>
      SourceCompilerFeatureSupport.require (value == final.1 && reprStr store == reprStr final.2)
        "imperative native resumption changed its exact result or store"
    | _ => throw (IO.userError "imperative native resumption did not complete")
  let checked ← SourceCompilerFeatureSupport.get "imperative lambda checker" (checkProgram workspace)
  let entry ← SourceCompilerFeatureSupport.compileNamed checked "make"
  let created ← entry.invoke [.word (Word.ofNatModulo 2)]
  let completed ← match created.outcome with
    | .succeeded completion => pure completion
    | _ => throw (IO.userError "imperative lambda creation failed")
  let handle ← match completed.value with
    | .function handle => pure handle
    | _ => throw (IO.userError "imperative lambda handle absent")
  let invoked ← SourceCompilerFeatureSupport.get "imperative lambda invocation"
    (← completed.session.invokePacked handle .unit SourceCompilerFeatureSupport.executionOptions)
  match invoked with
  | .succeeded completion =>
    SourceCompilerFeatureSupport.require (completion.value == .word (Word.ofNatModulo 6))
      "real imperative lambda capture/body changed"
  | _ => throw (IO.userError "real imperative lambda body failed")
  IO.println "imperative native policy: actual traversal, typed callbacks, hidden slots, exact store/resume and captured lambda GREEN"

end Tests.SourceCoreImperativeNativePolicyTyping
end

section
-- leanmerge: from Solcore.Test.SourceCoreMatchReachableDiagnostics
/-! The single match traversal preserves the selected diagnostic policy through
ordered child requests, header/post receipts and the actual function finish.
Concrete builtin Trees discharge child semantics. Equal has no operand token;
raw diagnostics interpretation and source/native static receipts remain explicit.
Named catalog profiles and preparation-to-whole-Tree laws are separate boundaries. -/
#check_failure Solcore.Frontend.SourceTypedRuntime.run
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 65536
namespace Tests.SourceCoreMatchReachableDiagnostics
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open GeneralHeap ReadOnly CompatiblePayload CoreProof
section FixedFactory
open BuiltinImperativeMatch
section Certificates
variable {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {values : ValuesContext} {source : TypedSource}
  {readFuel : Nat} {solved : List SolvedRequirement}
  {reasonAt : ExpressionId → Word} {definitions : DataEnvironment} {administrative : Core.Context}
  {policy : SourceCoreLoops.Policy} {parentSite : SourceCoreElaboration.ErrorSite}
  {invalidProjection : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Word}
  {invalidOperand : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Solcore.Syntax.ValueAssignOp → Word}
  {invalidUnary : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Word}
  {missingDefault : SourceCoreElaboration.ErrorSite → Resolved.LocalId → TypeSystem.Ty → Word}

  {program : CheckedProgram} {representation : SourceCoreGeneralFunctions.Representation}
  {signatures : ProgramSignatures} {locals : SourceCoreLocalPolymorphism.Catalog}
  {parents : List SourceCoreLocalEvidence.Prepared} {assignmentsTable : SourceCoreAssignmentFaultSites.Table}
  {diagnostics : SourceCoreDataPlaceFaultSites.Program} {compilation : SourceCoreFunctions.Context}
  {native : SourceCoreGeneralFunctions.CallableContext} {parent : Option SourceCoreLocalEvidence.Prepared}
  {skipInitializer : Option ExpressionId}

theorem accepted_fixed_factory
    (fixedPolicy : policy = SourceCoreCompatibleDataMatches.loopPolicy values compilation.solvedRequirements
      assignmentsTable diagnostics compilation.owner policy.lowerExpression
      (some (SourceCoreCallableIndexedAllocationFrames.allocator frame globals (layouts.allocatorAt owner active onError)))
      (some definitions))
    (hidden : GenericImperativeMatch.MatchHiddenFresh source)
    (assignments : CompatibleAssignmentStatements.AssignmentPolicy policy values invalidProjection invalidOperand missingDefault)
    (unaryPolicy : CompatibleBitNotStatements.Policy policy values invalidProjection invalidUnary missingDefault)
    (unique : NodeOccurrencesUnique source)
    (ordinary : CompatibleExpressionBuiltins.Ordinary source locals compilation.owner)
    (expressionPolicy : policy.lowerExpression = SourceCoreGeneralFunctions.lowerContextualExpression
      program representation signatures locals parents assignmentsTable diagnostics compilation (some native) parent skipInitializer)
    (expressionRead : representation.expressions.readExpression = SourceCoreCompatibleDataExpressions.readExpression values.checked)
    (lowerRead : representation.expressions.lowerRead = SourceCoreCompatibleDataExpressions.lowerRead readFuel values)
    (leafPolicy : representation.expressions.leafLowerer = SourceCoreCompatibleDataExpressions.leafLowerer values)
    (nativeTyping : ∀ sourceContext scope fuel id lowered,
      sourceContext.typeVariables = [] → sourceContext.residualTypeVariables = false →
      sourceContext.signatures = values.checked.signatures →
      CompatibleExpressionReads.ScopeDeclarations source scope sourceContext →
      CompatibleExpressionBuiltins.Syntax source id → ∀ node,
      source.lookupExpression? id = some node → ExpressionHasType source sourceContext id node.type →
      policy.lowerExpression fuel source scope id reasonAt = .ok lowered →
      HasType (SourceCoreLocalCell.coreContext scope ++ administrative) lowered.expression
        (LanguageResult.resultType lowered.type) definitions)
    {context : SourceSemantics.Context} {scope : Scope} {statements : List StatementId} {expected : TypeSystem.Ty}
    (syntaxTree : Syntax source context (.statements true statements) expected)
    (closed : context.typeVariables = []) (residual : context.residualTypeVariables = false)
    (sourceSignatures : context.signatures = values.checked.signatures)
    (declarations : CompatibleExpressionReads.ScopeDeclarations source scope context)
    {fuel : Nat} {type nativeType : Ty} {code : Expr} {fellThrough escaped : Word}
    (projection : values.checked.catalog.project expected = .ok type)
    (accepted : SourceCoreLoops.lowerStatementsWithPolicy policy fuel source scope statements type reasonAt fellThrough escaped = .ok code)
    (nativeTyped : HasType (SourceCoreLocalCell.coreContext scope ++ administrative) code nativeType definitions) :
    ∃ flow,
      SourceCoreLoops.lowerFlowStatementsWithPolicy policy fuel source scope statements type reasonAt true escaped = .ok flow ∧
      ∃ _extracted : ExtractionFor .reachable layouts owner active frame globals onError readFuel values source compilation.solvedRequirements reasonAt definitions administrative
        context scope (.statements true statements) expected type flow,
      code = LocalControl.finish type (LocalLoop.toControl type flow escaped)
        (if type = .unit then LanguageResult.success .unit else LanguageResult.failure type (.word fellThrough)) ∧
      ∀ registry faults, _extracted.diagnostics registry faults → ∀ evidence,
        CompatibleExpressionLiterals.ContextValid compilation.solvedRequirements context evidence →
        GenericImperativeMatch.Tree.ReachableReady registry faults _extracted.tree := by
  obtain ⟨flow, generated, extracted, same⟩ := extraction_of_fixed_contextual_body_for .reachable (fixedPolicy := fixedPolicy) (hidden := hidden) (assignments := assignments) (unaryPolicy := unaryPolicy) (unique := unique) (ordinary := ordinary) (expressionPolicy := expressionPolicy) (expressionRead := expressionRead) (lowerRead := lowerRead) (leafPolicy := leafPolicy) (nativeTyping := nativeTyping) (context := context) (scope := scope) (statements := statements) (expected := expected) (syntaxTree := syntaxTree) (closed := closed) (residual := residual) (sourceSignatures := sourceSignatures) (declarations := declarations) (fuel := fuel) (type := type) (nativeType := nativeType) (code := code) (fellThrough := fellThrough) (escaped := escaped) (projection := projection) (accepted := accepted) (nativeTyped := nativeTyped)
  exact ⟨flow, generated, extracted, same, fun registry faults interpreted evidence valid =>
    extracted.ready interpreted valid sourceSignatures⟩
end Certificates
end FixedFactory
section Body
open BuiltinImperativeMatchBody
section CompilerConsumers
variable {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frameLayout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {readFuel : Nat} {values : SourceCoreCompatibleValues.Context}
  {function : Dynamic.Closure} {context : SourceSemantics.Context} {solved : List SolvedRequirement}
  {reasonAt : ExpressionId → Word} {scope : SourceCoreLocalCell.Scope} {type : Ty}
  {administrative : Core.Context}
  {policy : SourceCoreLoops.Policy} {fuel : Nat} {fellThrough escaped : Word} {code : Expr}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient)
  {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends values.registry registry)
  (definitions : layouts.definitions = ambient.definitions)
  (registered : frameLayout.Registered ambient.definitions)
  (catalogValid : SignatureCatalogWellFormed values.checked.signatures)
  (program : SourceSemantics.Program)
  (contextValid : CompatibleExpressionLiterals.ContextValid solved context function.evidence)
  (unique : NodeOccurrencesUnique function.source) {faults : FunctionCalls.FaultRep}
  (escapedFault : faults .controlEscapedFunction escaped)
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))
  (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((reasonAt id).add tag))

  {identities : Dynamic.Value → Word → Prop}
  (faithful : DataEquality.IdentityFaithful identities)
  (functionLeaves : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)
  (functionTypes : FunctionRuntimeViews functions)

include definitions registered catalogValid escapedFault extension faithful functionLeaves functionTypes contextValid unique uninitialized missing in
theorem actual_compiler_body_preserves
    (accepted : SourceCoreLoops.lowerStatementsWithPolicy policy fuel function.source scope
      function.body type reasonAt fellThrough escaped = .ok code)
    (projection : values.checked.catalog.project function.resultType = .ok type)
    {flow : Expr}
    (generated : SourceCoreLoops.lowerFlowStatementsWithPolicy policy fuel function.source scope
      function.body type reasonAt true escaped = .ok flow)
    (extracted : BuiltinImperativeMatch.ExtractionFor .reachable layouts owner active frameLayout globals onError readFuel
      values function.source solved reasonAt ambient.definitions administrative
      context scope (.statements true function.body) function.resultType type flow)
    (interpreted : extracted.diagnostics registry faults)
    (signatures : context.signatures = values.checked.signatures)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {outcome : Dynamic.ExpressionOutcome}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    {contextLocation : Location} {native : SourceCoreCallableIndexedFrames.Frame}
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frameLayout.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frameLayout native))
    (unmapped : contextLocation ∉ mapping)
    (trace : FunctionCallBody.Trace program function context environment before outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (code.rename ξ) value finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld function.resultType type faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      TypedMixedNamedBody.ReachedExit values.checked ambient.definitions finalMap finalWorld administrative program function
        context scope environment before after outcome := by
  let certificate := of_extracted accepted projection generated extracted.tree
  exact certificate.preserves_reachable functions extension definitions registered catalogValid program
    contextValid unique escapedFault uninitialized missing faithful functionLeaves functionTypes
    (extracted.ready interpreted contextValid signatures) environments heaps locals agrees actualTyped reference read unmapped trace

include definitions registered catalogValid escapedFault extension faithful functionLeaves functionTypes contextValid unique uninitialized missing in
theorem actual_compiler_body_reflects
    (accepted : SourceCoreLoops.lowerStatementsWithPolicy policy fuel function.source scope
      function.body type reasonAt fellThrough escaped = .ok code)
    (projection : values.checked.catalog.project function.resultType = .ok type)
    {flow : Expr}
    (generated : SourceCoreLoops.lowerFlowStatementsWithPolicy policy fuel function.source scope
      function.body type reasonAt true escaped = .ok flow)
    (extracted : BuiltinImperativeMatch.ExtractionFor .reachable layouts owner active frameLayout globals onError readFuel
      values function.source solved reasonAt ambient.definitions administrative
      context scope (.statements true function.body) function.resultType type flow)
    (interpreted : extracted.diagnostics registry faults)
    (signatures : context.signatures = values.checked.signatures)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
    {store finalStore : Store} {ξ : Renaming} {value : Value}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    {contextLocation : Location} {native : SourceCoreCallableIndexedFrames.Frame}
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frameLayout.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frameLayout native))
    (unmapped : contextLocation ∉ mapping)
    (evaluated : Evaluates actual store (code.rename ξ) value finalStore) :
    ∃ outcome after finalMap finalWorld,
      FunctionCallBody.Trace program function context environment before outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld function.resultType type faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      TypedMixedNamedBody.ReachedExit values.checked ambient.definitions finalMap finalWorld administrative program function
        context scope environment before after outcome := by
  let certificate := of_extracted accepted projection generated extracted.tree
  exact certificate.reflects_reachable functions extension definitions registered catalogValid program
    contextValid unique escapedFault uninitialized missing faithful functionLeaves functionTypes
    (extracted.ready interpreted contextValid signatures) environments heaps locals agrees actualTyped reference read unmapped evaluated
end CompilerConsumers
end Body

section Receipt
variable {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {values : TypedLexicalWhile.ValuesContext} {source : TypedSource} {context : SourceSemantics.Context}
  {expressionSyntax : ExpressionId → Prop}
  {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {definitions : DataEnvironment} {administrative : Core.Context} {scope : TypedLexicalWhile.Scope} {type : Ty}
  {assignment : AssignmentResolution} {rhs : ExpressionId}
  (head : GenericAssignmentStatements.Head values source context (certificates context) scope administrative definitions assignment .equal rhs)
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  (missing : ∀ {root resolved reason token count},
    CompatibleMixedRoute.FaultToken values.checked registry root head.prepared.steps resolved reason token count → faults reason token)
  (uninitialized : ∀ location, faults (.uninitializedLocation location) head.prepared.invalidProjection)

include missing uninitialized in
/-- Equal introduces no operand-token law at a statement position. -/
theorem equal_statement_receipt {id : StatementId} {node : StatementNode} {mode : Bool}
    {statements : List StatementId} {expected : TypeSystem.Ty} {code : Expr}
    (found : source.lookupStatement? id = some node) (form : node.form = .assignValue assignment .equal rhs)
    (tail : GenericImperativeMatch.Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
      context scope (.statements mode statements) expected type code)
    (errors : GenericImperativeMatch.Tree.ReachableErrors registry faults tail) :
    GenericImperativeMatch.Tree.ReachableErrors registry faults (.assign found form head tail) :=
  .assign (found := found) (form := form) errors
    (GenericAssignmentStatements.Head.ReachableErrors.equal missing uninitialized)

include missing uninitialized in
/-- The initializer position uses exactly the same policy and static Tree. -/
theorem equal_initializer_receipt {items post : List ForItemForm} {condition : ExpressionId}
    {statements : List StatementId} {expected : TypeSystem.Ty} {code : Expr}
    (tail : GenericImperativeMatch.Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
      context scope (.initializers items condition post statements) expected type code)
    (errors : GenericImperativeMatch.Tree.ReachableErrors registry faults tail) :
    GenericImperativeMatch.Tree.ReachableErrors registry faults (.initializerAssign head tail) :=
  .initializerAssign errors (GenericAssignmentStatements.Head.ReachableErrors.equal missing uninitialized)

/-- The reachable receipt cannot be strengthened to the old operand law for
an empty diagnostic interpretation. -/
theorem equal_strict_impossible (noOperand : ∀ token, ¬ faults (.invalidAssignmentOperands .equal) token) :
    ¬ head.Errors registry faults := by
  intro errors
  exact noOperand _ errors.operands


include missing uninitialized in
theorem equal_assignment_extraction
    {id : StatementId} {node : StatementNode} {mode : Bool}
    {statements : List StatementId} {expected : TypeSystem.Ty} {code : Expr}
    {solved : List SolvedRequirement}
    (found : source.lookupStatement? id = some node) (form : node.form = .assignValue assignment .equal rhs)
    (tail : GenericImperativeMatch.ExtractionFor .reachable layouts owner active frame globals onError values source
      expressionSyntax certificates definitions administrative solved context scope (.statements mode statements) expected type code)
    (interpreted : tail.diagnostics registry faults) :
    (GenericImperativeMatch.ExtractionFor.assign found form head tail).diagnostics registry faults :=
  ⟨interpreted, GenericAssignmentStatements.Head.ReachableErrors.equal missing uninitialized⟩

end Receipt

private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := []
  mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "enum Choice { Left(Word), Right(Word) }",
    "function equalMatch(seed: Word) returns (integer) { let result = 0; for (let i = 0; i < 2; i = i + 1) { match (Choice.Left(i)) { case .Left(0) { result = seed; continue; } case .Left(x) { result = result + x; } case .Right(y) {} default {} } } return wordToInteger(result); }",
    "function sharedArms(seed: Word) returns (integer) { match (Choice.Left(seed)) { case .Left(x) {} case .Right(y) {} default {} } return wordToInteger(seed); }",
    "function earlyReturn(seed: Word) returns (integer) { let result = 0; let gap: Word; for (let i = 0; true; result = gap) { match (seed) { case x { result = x; return wordToInteger(result); } default {} } } return 99; }",
    "function rhsFault(seed: Word) returns (integer) { let root = 1; let seen: mapping(Bool => Word); let gap: Word; match (seed) { case x { root = seen[false] + gap; root = 99; } default {} } return wordToInteger(root); }",
    "function compoundFault(seed: Word) returns (integer) { let root: Word; let seen: mapping(Bool => Word); match (seed) { case x { root += seen[false] + x; root = 99; } default {} } return wordToInteger(root); }"
  ]}]
}

open Tests.SourceCompilerFeatureSupport in
private def sourceFor (entry : Entry) : IO TypedSource := do
  let exact ← get "actual source specialization" (SourceCompilationPlan.exactSpecialization entry.cached.validationPlan entry.key)
  pure exact.function.typedBody

open Tests.SourceCompilerFeatureSupport in
private def stable (entry : Entry) (args : List SourceCoreExecution.Value) : IO Unit := do
  let complete ← entry.audit args
  let invocation ← entry.invoke args
  for fuel in [0, 7, 43] do
    let started ← entry.audit args fuel
    let resumed ← get "native match resume" (started.resume 300000)
    require ((← nativeObservation complete) == (← nativeObservation resumed))
      "match resume changed its exact native result/store"
    let pending ← entry.invoke args {executionOptions with executionFuel := fuel}
    let finished ← match pending.outcome with
      | .outOfFuel checkpoint => checkpoint.resume 300000 2048
      | done => pure done
    match invocation.outcome, finished with
    | .succeeded expected, .succeeded actual => require (actual.value == expected.value) "match resume changed value"
    | .failed expected _, .failed actual session =>
      require (actual == expected) "match resume changed token"
      let diagnostic ← get "resumed match diagnostic" (session.diagnostic entry.key actual)
      require (decide (diagnostic = (← invocation.diagnostic expected))) "match resume changed diagnostic"
    | _, _ => throw (IO.userError "match resume changed terminal status")

open Tests.SourceCompilerFeatureSupport in
private def failure (entry : Entry) (expected : SourceCoreFaultSites.Diagnostic)
    (expectedCells : List (TypeSystem.Ty × Option SourceCoreExecution.Value)) : IO Unit := do
  let actual ← entry.invoke [scalar 7]
  match actual.outcome with
  | .failed token _ =>
    require (decide ((← actual.diagnostic token) = some expected)) "actual match failure lost exact source diagnostic"
  | _ => throw (IO.userError "match failure continued")
  entry.checkCells [scalar 7] expectedCells
  stable entry [scalar 7]

open Tests.SourceCompilerFeatureSupport in
def run : IO Unit := do
  let program ← get "match reachable fixtures" (checkProgram workspace)
  for (name, expected) in [("equalMatch", 8), ("sharedArms", 7), ("earlyReturn", 7)] do
    let entry ← compileNamed program name
    let source ← sourceFor entry
    let table ← get "actual equal match table" (SourceCoreAssignmentFaultSites.prepare source Core.wordModulus)
    require (table.sites.isEmpty && table.diagnostic? Word.zero == none)
      "equal match/header/post introduced an unreachable operand token"
    require ((← entry.run [scalar 7]) == .integer expected) "match control/binding/assignment order changed"
    stable entry [scalar 7]
  let rhs ← compileNamed program "rhsFault"
  let source ← sourceFor rhs
  let table ← get "actual RHS-failed equal table" (SourceCoreAssignmentFaultSites.prepare source Core.wordModulus)
  require table.sites.isEmpty "RHS failure added an equal operand token"
  let (node, binder) ← match source.nodes.findSome? fun
      | .expression node => match node.form with | .reference "gap" (.local binder) => some (node,binder) | _ => none
      | _ => none with
    | some pair => pure pair | none => throw (IO.userError "RHS missing read absent")
  failure rhs {error := .uninitializedLocal binder, site := .occurrence node.id.occurrence, span := some node.span}
    [(.word, some (scalar 7)), (.word, some (scalar 1)), (.mapping .bool .word, some (.mapping .bool .word [])),
      (.word, none), (.word, some (scalar 7)), (.word, some (scalar 7))]
  let compound ← compileNamed program "compoundFault"
  let source ← sourceFor compound
  let table ← get "actual compound match table" (SourceCoreAssignmentFaultSites.prepare source 100)
  let node ← match source.nodes.findSome? fun
      | .statement node => match node.form with | .assignValue _ .add _ => some node | _ => none
      | _ => none with
    | some node => pure node | none => throw (IO.userError "compound site absent")
  require (table.length == 1 && table.sites.all fun site => decide
    (site.site = .occurrence node.id.occurrence ∧ site.span = node.span ∧ site.rhsType = .word ∧ site.kind = .value .add))
    "compound match diagnostic lost its first complete raw metadata"
  failure compound {
    error := .invalidAssignmentOperands .add none (some .word),
    site := .occurrence node.id.occurrence, span := some node.span}
    [(.word, some (scalar 7)), (.word, none), (.mapping .bool .word, some (.mapping .bool .word [])),
      (.word, some (scalar 7)), (.word, some (scalar 7))]
  IO.println "reachable match: same-policy extraction/Ready/body finish, empty equal tables, scoped branches, for/continue, faults/effects and resume GREEN"

end Tests.SourceCoreMatchReachableDiagnostics
end

section
-- leanmerge: from Solcore.Test.SourceCorePreparedForDiagnostics
/-! Actual prepared operand laws follow the existing for traversal into named
body and recursive catalog receipts. Source syntax/typing, child certificates,
native typing and non-operand fault interpretation remain explicit. No match
Tree is cast into the for grammar and no recursive callee meaning is assumed. -/
#check_failure Solcore.Frontend.SourceTypedRuntime.run
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 65536
namespace Tests.SourceCorePreparedForDiagnostics
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open CallableAncestryPairedLookup CompatiblePayload GenericImperativeFor
section Named
variable {checked : Checked} {base : Base checked}
  {prepared : SourceCoreCallableIndexedAncestry.Prepared base} {values : ValuesContext}
  {ambient : AmbientDefinitions values.checked.catalog.definitions} {program : SourceSemantics.Program}
  {bodies : NamedCallExpressions.Bodies prepared values ambient.definitions program}
  {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {compilation : SourceCoreFunctions.Context} {expressionFuel : Nat}
  {source : TypedSource} {expressionSyntax : ExpressionId → Prop} {solved : List SolvedRequirement}
  {reasonAt : ExpressionId → Word} {administrative : Core.Context} {policy : SourceCoreLoops.Policy}
theorem prepared_named_body {first : Nat} {table : SourceCoreAssignmentFaultSites.Table}
    (tablePrepared : SourceCoreAssignmentFaultSites.prepare source first = .ok table)
    (operandsTyped : AssignmentDiagnosticOrigins.OperandsTyped source)
    {ledger : List SolvedRequirement} {policyOwner : SourceSpecialization.SpecializationKey}
    {diagnostics : SourceCoreDataPlaceFaultSites.Program}
    (fixedPolicy : policy = SourceCoreCompatibleDataMatches.loopPolicy values ledger table diagnostics policyOwner policy.lowerExpression
      (some (SourceCoreCallableIndexedAllocationFrames.allocator frame globals (layouts.allocatorAt owner active onError)))
      (some ambient.definitions))
    (expressions : ∀ sourceContext, sourceContext.typeVariables = [] → sourceContext.residualTypeVariables = false →
      sourceContext.signatures = values.checked.signatures →
      ∀ {scope fuel id node lowered}, CompatibleExpressionReads.ScopeDeclarations source scope sourceContext → expressionSyntax id →
      source.lookupExpression? id = some node → ExpressionHasType source sourceContext id node.type →
      policy.lowerExpression fuel source scope id reasonAt = .ok lowered →
      (fun context => NamedCallExpressions.Tree bodies compilation expressionFuel source context solved reasonAt) sourceContext scope id lowered)
    (unique : NodeOccurrencesUnique source)
    (assignmentExpressions : ∀ sourceContext scope fuel id lowered,
      sourceContext.typeVariables = [] → sourceContext.residualTypeVariables = false →
      sourceContext.signatures = values.checked.signatures →
      CompatibleExpressionReads.ScopeDeclarations source scope sourceContext →
      expressionSyntax id → ∀ node, source.lookupExpression? id = some node →
      ExpressionHasType source sourceContext id node.type →
      policy.lowerExpression fuel source scope id reasonAt = .ok lowered →
        (fun context => NamedCallExpressions.Tree bodies compilation expressionFuel source context solved reasonAt) sourceContext scope id lowered ∧
        HasType (SourceCoreLocalCell.coreContext scope ++ administrative) lowered.expression
          (LanguageResult.resultType lowered.type) ambient.definitions)
    {context : SourceSemantics.Context} {scope : Scope} {statements : List StatementId} {expected : TypeSystem.Ty}
    (syntaxTree : Syntax source expressionSyntax context (.statements true statements) expected)
    (closed : context.typeVariables = []) (residual : context.residualTypeVariables = false)
    (sourceSignatures : context.signatures = values.checked.signatures)
    (declarations : CompatibleExpressionReads.ScopeDeclarations source scope context)
    {fuel : Nat} {type nativeType : Ty} {code : Expr} {fellThrough escaped : Word}
    (projection : values.checked.catalog.project expected = .ok type)
    (accepted : SourceCoreLoops.lowerStatementsWithPolicy policy fuel source scope statements type reasonAt fellThrough escaped = .ok code)
    (nativeTyped : HasType (SourceCoreLocalCell.coreContext scope ++ administrative) code nativeType ambient.definitions) :
    ∃ flow,
      SourceCoreLoops.lowerFlowStatementsWithPolicy policy fuel source scope statements type reasonAt true escaped = .ok flow ∧
      ∃ _extracted : DiagnosticExtraction .reachable layouts owner active frame globals onError values source expressionSyntax (fun context => NamedCallExpressions.Tree bodies compilation expressionFuel source context solved reasonAt) ambient.definitions administrative
        context scope (.statements true statements) expected type flow,
      code = LocalControl.finish type (LocalLoop.toControl type flow escaped)
        (if type = .unit then LanguageResult.success .unit else LanguageResult.failure type (.word fellThrough)) ∧
      ∀ registry faults, _extracted.diagnostics registry faults →
        Nonempty (NamedForFunctionBody.CertificateFor .reachable bodies layouts owner active frame globals onError compilation expressionFuel
          source expressionSyntax context solved reasonAt administrative registry faults scope statements expected type policy fuel fellThrough escaped code) := by
  obtain ⟨flow, generated, extracted, same⟩ := extraction_of_prepared_policy_body tablePrepared operandsTyped fixedPolicy expressions unique assignmentExpressions syntaxTree closed residual sourceSignatures declarations projection accepted nativeTyped
  exact ⟨flow, generated, extracted, same, fun registry faults interpreted =>
    ⟨extracted.named_body accepted projection generated interpreted⟩⟩
end Named

section Catalog
variable {checked : Checked} {base : Base checked}
  {prepared : SourceCoreCallableIndexedAncestry.Prepared base} {values : ValuesContext}
  {ambient : AmbientDefinitions values.checked.catalog.definitions} {program : SourceSemantics.Program}
  {headers : RecursiveNamedCatalog.Inventory prepared values ambient.definitions program}
  {header : RecursiveNamedCatalog.Header prepared values ambient.definitions program}
  {compilation : SourceCoreFunctions.Context} {expressionFuel : Nat}
  {expressionSyntax : ExpressionId → Prop} {administrative : Core.Context}
theorem prepared_catalog_profile {first : Nat} {table : SourceCoreAssignmentFaultSites.Table}
    (initialValid : CompatibleExpressionLiterals.ContextValid header.solved header.context header.function.evidence)
    (tablePrepared : SourceCoreAssignmentFaultSites.prepare header.function.source first = .ok table)
    (operandsTyped : AssignmentDiagnosticOrigins.OperandsTyped header.function.source)
    {ledger : List SolvedRequirement} {policyOwner : SourceSpecialization.SpecializationKey}
    {diagnostics : SourceCoreDataPlaceFaultSites.Program}
    (fixedPolicy : header.policy = SourceCoreCompatibleDataMatches.loopPolicy values ledger table diagnostics policyOwner header.policy.lowerExpression
      (some (SourceCoreCallableIndexedAllocationFrames.allocator prepared.layout.frame header.globals (header.layouts.allocatorAt header.owner header.active header.onError)))
      (some ambient.definitions))
    (expressions : ∀ sourceContext, sourceContext.typeVariables = [] → sourceContext.residualTypeVariables = false →
      sourceContext.signatures = values.checked.signatures →
      ∀ {scope fuel id node lowered}, CompatibleExpressionReads.ScopeDeclarations header.function.source scope sourceContext → expressionSyntax id →
      header.function.source.lookupExpression? id = some node → ExpressionHasType header.function.source sourceContext id node.type →
      header.policy.lowerExpression fuel header.function.source scope id header.reasonAt = .ok lowered →
      (fun context => RecursiveNamedCatalog.Expressions headers compilation expressionFuel header.function.source context header.solved header.reasonAt) sourceContext scope id lowered)
    (unique : NodeOccurrencesUnique header.function.source)
    (assignmentExpressions : ∀ sourceContext scope fuel id lowered,
      sourceContext.typeVariables = [] → sourceContext.residualTypeVariables = false →
      sourceContext.signatures = values.checked.signatures →
      CompatibleExpressionReads.ScopeDeclarations header.function.source scope sourceContext →
      expressionSyntax id → ∀ node, header.function.source.lookupExpression? id = some node →
      ExpressionHasType header.function.source sourceContext id node.type →
      header.policy.lowerExpression fuel header.function.source scope id header.reasonAt = .ok lowered →
        (fun context => RecursiveNamedCatalog.Expressions headers compilation expressionFuel header.function.source context header.solved header.reasonAt) sourceContext scope id lowered ∧
        HasType (SourceCoreLocalCell.coreContext scope ++ administrative) lowered.expression
          (LanguageResult.resultType lowered.type) ambient.definitions)
    (syntaxTree : Syntax header.function.source expressionSyntax header.context (.statements true header.function.body) header.function.resultType)
    (closed : header.context.typeVariables = []) (residual : header.context.residualTypeVariables = false)
    (sourceSignatures : header.context.signatures = values.checked.signatures)
    (declarations : CompatibleExpressionReads.ScopeDeclarations header.function.source (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) header.context)
    {nativeType : Ty}
    (projection : values.checked.catalog.project header.function.resultType = .ok header.output)
    (accepted : SourceCoreLoops.lowerStatementsWithPolicy header.policy header.fuel header.function.source (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) header.function.body header.output header.reasonAt header.fellThrough header.escaped = .ok header.body)
    (nativeTyped : HasType (SourceCoreLocalCell.coreContext (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) ++ administrative) header.body nativeType ambient.definitions) :
    ∃ flow,
      SourceCoreLoops.lowerFlowStatementsWithPolicy header.policy header.fuel header.function.source (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) header.function.body header.output header.reasonAt true header.escaped = .ok flow ∧
      ∃ _extracted : DiagnosticExtraction .reachable header.layouts header.owner header.active prepared.layout.frame header.globals header.onError values header.function.source expressionSyntax (fun context => RecursiveNamedCatalog.Expressions headers compilation expressionFuel header.function.source context header.solved header.reasonAt) ambient.definitions administrative
        header.context (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) (.statements true header.function.body) header.function.resultType header.output flow,
      header.body = LocalControl.finish header.output (LocalLoop.toControl header.output flow header.escaped)
        (if header.output = .unit then LanguageResult.success .unit else LanguageResult.failure header.output (.word header.fellThrough)) ∧
      ∀ registry faults, _extracted.diagnostics registry faults →
        Nonempty (RecursiveNamedCatalog.ProfileFor .reachable headers header compilation expressionFuel expressionSyntax administrative registry faults) := by
  obtain ⟨flow, generated, extracted, same⟩ := extraction_of_prepared_policy_body tablePrepared operandsTyped fixedPolicy expressions unique assignmentExpressions syntaxTree closed residual sourceSignatures declarations projection accepted nativeTyped
  exact ⟨flow, generated, extracted, same, fun registry faults interpreted =>
    ⟨extracted.catalog_profile initialValid accepted projection generated interpreted⟩⟩
end Catalog

open NamedForFunctionBody GeneralHeap ReadOnly CoreProof
section CompilerConsumers
variable {checked : Checked} {base : Base checked}
  {prepared : SourceCoreCallableIndexedAncestry.Prepared base}
  {values : SourceCoreCompatibleValues.Context}
  {ambient : AmbientDefinitions values.checked.catalog.definitions} {program : SourceSemantics.Program}
  {bodies : NamedCallExpressions.Bodies prepared values ambient.definitions program}
  {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frameLayout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {compilation : SourceCoreFunctions.Context} {expressionFuel : Nat}
  {function : Dynamic.Closure} {expressionSyntax : ExpressionId → Prop} {context : SourceSemantics.Context} {solved : List SolvedRequirement}
  {reasonAt : ExpressionId → Word} {scope : SourceCoreLocalCell.Scope} {type : Ty}
  {administrative : Core.Context}
  {policy : SourceCoreLoops.Policy} {fuel : Nat} {fellThrough escaped : Word} {code : Expr}
  (functions : FunctionModel values.checked.catalog ambient)
  {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends values.registry registry)
  (definitions : layouts.definitions = ambient.definitions)
  (registered : frameLayout.Registered ambient.definitions)
  (contextValid : CompatibleExpressionLiterals.ContextValid solved context function.evidence)
  (unique : NodeOccurrencesUnique function.source)
  (owners : (program.functions.map (fun definition => definition.body.owner)).Nodup) {faults : FunctionCalls.FaultRep}
  (escapedFault : faults .controlEscapedFunction escaped)
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))
  (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((reasonAt id).add tag))

  (bodyUninitialized : ∀ body, body ∈ bodies → ∀ id location,
    faults (.uninitializedLocation location) (body.reasonAt id))
  (bodyMissing : ∀ body, body ∈ bodies → ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((body.reasonAt id).add tag))
  {identities : Dynamic.Value → Word → Prop}
  (faithful : DataEquality.IdentityFaithful identities)
  (functionLeaves : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)
  (functionTypes : FunctionRuntimeViews functions)

include definitions registered escapedFault extension faithful functionLeaves functionTypes contextValid unique owners uninitialized missing bodyUninitialized bodyMissing in
theorem extracted_named_finite_iff
    (accepted : SourceCoreLoops.lowerStatementsWithPolicy policy fuel function.source scope
      function.body type reasonAt fellThrough escaped = .ok code)
    (projection : values.checked.catalog.project function.resultType = .ok type)
    {flow : Expr}
    (generated : SourceCoreLoops.lowerFlowStatementsWithPolicy policy fuel function.source scope
      function.body type reasonAt true escaped = .ok flow)
    (extracted : GenericImperativeFor.DiagnosticExtraction .reachable layouts owner active frameLayout globals onError values
      function.source expressionSyntax
      (fun nextContext => NamedCallExpressions.Tree bodies compilation expressionFuel function.source nextContext solved reasonAt)
      ambient.definitions administrative context scope (.statements true function.body) function.resultType type flow)
    (interpreted : extracted.diagnostics registry faults)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
    {store : Store} {ξ : Renaming}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    {contextLocation : Location} {native : SourceCoreCallableIndexedFrames.Frame}
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frameLayout.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frameLayout native))
    (unmapped : contextLocation ∉ mapping)
    (installed : NamedCallExpressions.Entry functions registry bodies compilation.administrativePrefix
      scope mapping world before store canonical)
:
    (∃ runtimeFuel value finalStore,
      Core.runStateful runtimeFuel (.initial (code.rename ξ) actual store) =
        .done value finalStore) ↔
    (∃ outcome after,
      FunctionCallBody.Trace program function context environment before outcome after) := by
  let certificate := extracted.named_body accepted projection generated interpreted
  exact certificate.finite_iff functions extension definitions registered
    contextValid unique owners escapedFault uninitialized missing bodyUninitialized bodyMissing faithful functionLeaves functionTypes
    environments heaps locals agrees actualTyped reference read unmapped installed
end CompilerConsumers

private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := []
  mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "function compound(seed: Word) returns (Word) { let result = seed; for (result += 1, result += 2; result < 9; result += 1) { if (result == 6) { continue; } if (result == 7) { break; } } return result; }",
    "function next(value: Word) returns (Word) { return value + 1; }",
    "function less(value: Word, bound: Word) returns (Bool) { return value < bound; }",
    "function bad() returns (Word) { let absent: Word; return absent; }",
    "function equalBody(seed: Word) returns (Word) { let result = seed; for (result = next(seed); less(result, 5); result = next(result)) { let inner = 0; while (less(inner, 2)) { inner = next(inner); } if (result == 3) { continue; } if (result == 4) { break; } } return result; }",
    "function unitBody(seed: Word) { let result = seed; for (result = next(seed); less(result, 3); result = next(result)) { } }",
    "function initialFault(seed: Word) returns (Word) { let result = seed; for (result = bad(); false; result = next(result)) { result = next(result); } return result; }",
    "function postFault(seed: Word) returns (Word) { let result = seed; for (result = next(seed); true; result = bad()) { result = next(result); } return result; }",
    "function bodyFault(seed: Word) returns (Word) { let result = seed; let seen: mapping(Bool => Word); for (result = next(seed); true; result = next(result)) { seen[false] = next(result); result = bad(); } return result; }",
    "function self(n: Word) returns (Word) { let result = 1; for (let i = 0; i < n; i = next(i)) { result = result + self(n - 1); } return result; }"
  ]}]
}
open Tests.SourceCompilerFeatureSupport in
private def verify_resume (entry : Entry) : IO Unit := do
  let baseline ← entry.audit [scalar 1]
  let invocation ← entry.invoke [scalar 1]
  for fuel in [0, 7, 43, 199] do
    let suspended ← entry.audit [scalar 1] fuel
    let resumed ← get "reachable body native resume" (suspended.resume 300000)
    require ((← nativeObservation resumed) == (← nativeObservation baseline))
      "reachable body resume changed native result/store"
    let pending ← entry.invoke [scalar 1] {executionOptions with executionFuel := fuel}
    let terminal ← match pending.outcome with
      | .outOfFuel checkpoint => checkpoint.resume 300000 2048
      | done => pure done
    match invocation.outcome, terminal with
    | .succeeded expected, .succeeded actual =>
      require (actual.value == expected.value) "reachable body resume changed result"
    | .failed expected _, .failed actual session =>
      require (actual == expected) "reachable body resume changed fault token"
      require (decide ((← get "resumed diagnostic" (session.diagnostic entry.key actual)) = (← invocation.diagnostic expected)))
        "reachable body resume changed exact diagnostic"
    | _, _ => throw (IO.userError "reachable body resume changed completion")

open Tests.SourceCompilerFeatureSupport in
def run : IO Unit := do
  let checked ← get "reachable named body checker" (checkProgram workspace)
  let compound ← compileNamed checked "compound"
  let source := (← get "compound actual source" (SourceCompilationPlan.exactSpecialization compound.cached.validationPlan compound.key)).function.typedBody
  let table ← get "compound actual prepare" (SourceCoreAssignmentFaultSites.prepare source 100)
  let node ← match source.nodes.findSome? fun
      | .statement node => match node.form with | .forLoop _ _ _ _ => some node | _ => none
      | _ => none with
    | some node => pure node
    | none => throw (IO.userError "compound parent for absent")
  require (table.sites.length == 1 && table.sites.all fun site => decide
    (site.site = .occurrence node.id.occurrence ∧ site.span = node.span ∧ site.kind = .value .add ∧ site.rhsType = .word))
    "parent initializer/post duplicate did not preserve first diagnostic metadata"
  require ((← compound.run [scalar 1]) == scalar 7) "compound parent loop changed"
  verify_resume compound
  for name in ["equalBody", "unitBody", "initialFault", "postFault", "bodyFault", "self"] do
    let entry ← compileNamed checked name
    let item ← get "reachable named source" (SourceCompilationPlan.exactSpecialization entry.cached.validationPlan entry.key)
    let table ← get "equal-only body table" (SourceCoreAssignmentFaultSites.prepare item.function.typedBody Core.wordModulus)
    require table.sites.isEmpty "equal-only named body requested an unreachable operand token"
    require (table.diagnostic? Word.zero == none) "empty named body table decoded a token"
    verify_resume entry
    let result ← entry.invoke [scalar 1]
    match name, result.outcome with
    | "equalBody", .succeeded completed => require (completed.value == scalar 4) "nested named loop result changed"
    | "unitBody", .succeeded completed => require (completed.value == .unit) "named Unit finish changed"
    | "self", .succeeded completed => require (completed.value == scalar 2) "recursive runtime smoke result changed"
    | _, .failed token _ =>
      require (← result.diagnostic token).isSome "named RHS fault lost its diagnostic"
      let audited ← entry.audit [scalar 1]
      let heap := (sourceState audited).heap
      let expected := if name == "initialFault" then 1 else if name == "postFault" then 3 else 2
      let raw ← get "reachable body expected write" (rawData 128 (scalar expected))
      require (reprStr heap[1]? == reprStr (some (SourceTypedRuntime.Cell.mk .word (some raw))))
        "initializer/body/post fault changed prior writes"
      if name == "bodyFault" then
        let rawMapping ← get "reachable body expected mapping write" (rawData 128
          (.mapping .bool .word [(.bool false, scalar 3)]))
        require (reprStr heap[2]? == reprStr (some (SourceTypedRuntime.Cell.mk (.mapping .bool .word) (some rawMapping))))
          "named RHS fault discarded a completed mapping write"
    | _, _ => throw (IO.userError "unexpected reachable named body completion")
  IO.println "prepared for diagnostics: actual parent origins, same for grammar to named/static catalog receipts, empty equal table, named faults/writes/resume GREEN"
end Tests.SourceCorePreparedForDiagnostics
end

section
-- leanmerge: from Solcore.Test.SourceCorePreparedMatchDiagnostics
/-! Actual prepared diagnostics across statement, initializer and post origins.
The public compiler consumer retains native/source static inputs and residual
fault interpretation; operand laws and the match ledger are constructed here. -/
#check_failure Solcore.Frontend.SourceTypedRuntime.run
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 65536
namespace Tests.SourceCorePreparedMatchDiagnostics
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
section FixedFactory
open BuiltinImperativeMatch
section Certificates
variable {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {values : ValuesContext} {source : TypedSource}
  {readFuel : Nat} {solved : List SolvedRequirement}
  {reasonAt : ExpressionId → Word} {definitions : DataEnvironment} {administrative : Core.Context}
  {policy : SourceCoreLoops.Policy} {parentSite : SourceCoreElaboration.ErrorSite}
  {invalidProjection : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Word}
  {invalidOperand : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Solcore.Syntax.ValueAssignOp → Word}
  {invalidUnary : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Word}
  {missingDefault : SourceCoreElaboration.ErrorSite → Resolved.LocalId → TypeSystem.Ty → Word}

  {program : CheckedProgram} {representation : SourceCoreGeneralFunctions.Representation}
  {signatures : ProgramSignatures} {locals : SourceCoreLocalPolymorphism.Catalog}
  {parents : List SourceCoreLocalEvidence.Prepared} {assignmentsTable : SourceCoreAssignmentFaultSites.Table}
  {diagnostics : SourceCoreDataPlaceFaultSites.Program} {compilation : SourceCoreFunctions.Context}
  {native : SourceCoreGeneralFunctions.CallableContext} {parent : Option SourceCoreLocalEvidence.Prepared}
  {skipInitializer : Option ExpressionId}

theorem accepted_prepared_factory {first : Nat}
    (prepared : SourceCoreAssignmentFaultSites.prepare source first = .ok assignmentsTable)
    (operandTyping : AssignmentDiagnosticOrigins.OperandsTyped source)
    (fixedPolicy : policy = SourceCoreCompatibleDataMatches.loopPolicy values compilation.solvedRequirements
      assignmentsTable diagnostics compilation.owner policy.lowerExpression
      (some (SourceCoreCallableIndexedAllocationFrames.allocator frame globals (layouts.allocatorAt owner active onError)))
      (some definitions))
    (hidden : GenericImperativeMatch.MatchHiddenFresh source)
    (unique : NodeOccurrencesUnique source)
    (ordinary : CompatibleExpressionBuiltins.Ordinary source locals compilation.owner)
    (expressionPolicy : policy.lowerExpression = SourceCoreGeneralFunctions.lowerContextualExpression
      program representation signatures locals parents assignmentsTable diagnostics compilation (some native) parent skipInitializer)
    (expressionRead : representation.expressions.readExpression = SourceCoreCompatibleDataExpressions.readExpression values.checked)
    (lowerRead : representation.expressions.lowerRead = SourceCoreCompatibleDataExpressions.lowerRead readFuel values)
    (leafPolicy : representation.expressions.leafLowerer = SourceCoreCompatibleDataExpressions.leafLowerer values)
    (nativeTyping : ∀ sourceContext scope fuel id lowered,
      sourceContext.typeVariables = [] → sourceContext.residualTypeVariables = false →
      sourceContext.signatures = values.checked.signatures →
      CompatibleExpressionReads.ScopeDeclarations source scope sourceContext →
      CompatibleExpressionBuiltins.Syntax source id → ∀ node,
      source.lookupExpression? id = some node → ExpressionHasType source sourceContext id node.type →
      policy.lowerExpression fuel source scope id reasonAt = .ok lowered →
      HasType (SourceCoreLocalCell.coreContext scope ++ administrative) lowered.expression
        (LanguageResult.resultType lowered.type) definitions)
    {context : SourceSemantics.Context} {scope : Scope} {statements : List StatementId} {expected : TypeSystem.Ty}
    (syntaxTree : Syntax source context (.statements true statements) expected)
    (closed : context.typeVariables = []) (residual : context.residualTypeVariables = false)
    (sourceSignatures : context.signatures = values.checked.signatures)
    (declarations : CompatibleExpressionReads.ScopeDeclarations source scope context)
    {fuel : Nat} {type nativeType : Ty} {code : Expr} {fellThrough escaped : Word}
    (projection : values.checked.catalog.project expected = .ok type)
    (accepted : SourceCoreLoops.lowerStatementsWithPolicy policy fuel source scope statements type reasonAt fellThrough escaped = .ok code)
    (nativeTyped : HasType (SourceCoreLocalCell.coreContext scope ++ administrative) code nativeType definitions) :
    ∃ flow,
      SourceCoreLoops.lowerFlowStatementsWithPolicy policy fuel source scope statements type reasonAt true escaped = .ok flow ∧
      ∃ _extracted : ExtractionFor .reachable layouts owner active frame globals onError readFuel values source compilation.solvedRequirements reasonAt definitions administrative
        context scope (.statements true statements) expected type flow,
      code = LocalControl.finish type (LocalLoop.toControl type flow escaped)
        (if type = .unit then LanguageResult.success .unit else LanguageResult.failure type (.word fellThrough)) ∧
      ∀ registry faults, _extracted.diagnostics registry faults → ∀ evidence,
        CompatibleExpressionLiterals.ContextValid compilation.solvedRequirements context evidence →
        GenericImperativeMatch.Tree.ReachableReady registry faults _extracted.tree := by
  obtain ⟨flow, generated, extracted, same⟩ := extraction_of_prepared_contextual_body prepared operandTyping (fixedPolicy := fixedPolicy) (hidden := hidden) (unique := unique) (ordinary := ordinary) (expressionPolicy := expressionPolicy) (expressionRead := expressionRead) (lowerRead := lowerRead) (leafPolicy := leafPolicy) (nativeTyping := nativeTyping) (context := context) (scope := scope) (statements := statements) (expected := expected) (syntaxTree := syntaxTree) (closed := closed) (residual := residual) (sourceSignatures := sourceSignatures) (declarations := declarations) (fuel := fuel) (type := type) (nativeType := nativeType) (code := code) (fellThrough := fellThrough) (escaped := escaped) (projection := projection) (accepted := accepted) (nativeTyped := nativeTyped)
  exact ⟨flow, generated, extracted, same, fun registry faults interpreted evidence valid =>
    extracted.ready interpreted valid sourceSignatures⟩
end Certificates
end FixedFactory
section Origins
open AssignmentDiagnosticOrigins
variable {source : TypedSource} {context : SourceSemantics.Context}
  {assignment : AssignmentResolution} {operator : Solcore.Syntax.ValueAssignOp} {rhs : ExpressionId}

theorem compound_raw_word (different : operator ≠ .equal)
    (typed : SourceAssignmentHasType source context assignment operator rhs) : assignment.target.type = .word := by
  cases typed with
  | equal => exact (different rfl).elim
  | wordCompound _ target _ _ => cases target with | intro _ _ same => exact same

/-- A normalized alias cannot silently satisfy the actual table guard. -/
theorem comptime_word_not_compound (different : operator ≠ .equal)
    (raw : assignment.target.type = .comptime .word) :
    ¬ SourceAssignmentHasType source context assignment operator rhs := by
  intro typed
  have same := compound_raw_word different typed
  rw [raw] at same
  cases same

theorem initializer_suffix_origin {id : StatementId} {node : StatementNode}
    {beforeItems rest post : List ForItemForm} {condition : ExpressionId} {body : List StatementId}
    (found : source.lookupStatement? id = some node)
    (form : node.form = .forLoop (beforeItems ++ .assignValue assignment operator rhs :: rest) condition post body) :
    Occurs source (.occurrence id.occurrence) assignment operator rhs := by
  have origin : ForOriginFor true source (.occurrence id.occurrence)
      (.assignValue assignment operator rhs :: rest) condition post body :=
    ⟨id, node, _, found, form, rfl, beforeItems, rfl⟩
  exact origin.header.operand

theorem post_suffix_origin {id : StatementId} {node : StatementNode}
    {beforeItems rest initial : List ForItemForm} {condition : ExpressionId} {body : List StatementId}
    (found : source.lookupStatement? id = some node)
    (form : node.form = .forLoop initial condition (beforeItems ++ .assignValue assignment operator rhs :: rest) body) :
    Occurs source (.occurrence id.occurrence) assignment operator rhs := by
  have origin : HeaderOriginFor true source (.occurrence id.occurrence)
      (.assignValue assignment operator rhs :: rest) :=
    .inr ⟨id, node, initial, condition, _, body, found, form, rfl, beforeItems, rfl⟩
  exact origin.operand

/-- The concrete prepared factory consumes only the remaining local laws. -/
theorem prepared_head_errors
    {values : SourceCoreCompatibleValues.Context} {certificate : GenericExpressionMeaning.Certificate}
    {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context} {definitions : DataEnvironment}
    (head : GenericAssignmentStatements.Head values source context certificate scope administrative definitions assignment operator rhs)
    {site : Site} {first : Nat} {table : SourceCoreAssignmentFaultSites.Table}
    {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
    (origin : Occurs source site assignment operator rhs)
    (typed : OperandsTyped source) (prepared : SourceCoreAssignmentFaultSites.prepare source first = .ok table)
    (sameToken : head.invalid = GenericAssignmentDiagnostics.token table site assignment.target.root operator)
    (remaining : Residual head table registry faults) :
    head.ReachableErrors registry faults :=
  (Factory.prepared typed prepared).materialize head site origin sameToken registry faults remaining

end Origins

private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := []
  mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "function headers(seed: Word) returns (Word) { let out = seed; for (out += 1, out += 2; out < 9; out += 1) { match (out) { case 6 { continue; } default { if (out == 7) { break; } } } } return out; }",
    "function equalHeaders(seed: Word) returns (Word) { let out = seed; for (out = seed; out < seed + 2; out = out + 1) { match(out) { case x {} default {} } } return out; }",
    "function initialFault(seed: Word) returns (Word) { let root: Word; let seen: mapping(Bool => Word); for (root += seen[false]; false; root += seed) {} return root; }",
    "function postFault(seed: Word) returns (Word) { let root: Word; let seen: mapping(Bool => Word); for (let i = 0; i < 1; root += seen[false]) { match (seed) { case x {} default {} } } return root; }"
  ]}]
}

open Tests.SourceCompilerFeatureSupport in
private def sourceFor (entry : Entry) : IO TypedSource := do
  pure (← get "actual source" (SourceCompilationPlan.exactSpecialization entry.cached.validationPlan entry.key)).function.typedBody

open Tests.SourceCompilerFeatureSupport in
private def stable (entry : Entry) : IO Unit := do
  let complete ← entry.audit [scalar 1]
  let invocation ← entry.invoke [scalar 1]
  for fuel in [0, 7, 43] do
    let started ← entry.audit [scalar 1] fuel
    let resumed ← get "native prepared-match resume" (started.resume 300000)
    require ((← nativeObservation complete) == (← nativeObservation resumed))
      "prepared-match resume changed exact native result/store"
    let pending ← entry.invoke [scalar 1] {executionOptions with executionFuel := fuel}
    let terminal ← match pending.outcome with
      | .outOfFuel checkpoint => checkpoint.resume 300000 2048
      | done => pure done
    match invocation.outcome, terminal with
    | .succeeded expected, .succeeded actual => require (actual.value == expected.value) "prepared resume changed value"
    | .failed expected _, .failed actual session =>
      require (actual == expected) "prepared resume changed token"
      require (decide ((← get "resumed diagnostic" (session.diagnostic entry.key actual)) = (← invocation.diagnostic expected)))
        "prepared resume changed diagnostic"
    | _, _ => throw (IO.userError "prepared resume changed completion status")

open Tests.SourceCompilerFeatureSupport in
def run : IO Unit := do
  let program ← get "prepared-match fixtures" (checkProgram workspace)
  for (name, expected) in [("headers", 7), ("equalHeaders", 3)] do
    let entry ← compileNamed program name
    let source ← sourceFor entry
    let table ← get "actual operand prepare" (SourceCoreAssignmentFaultSites.prepare source 100)
    if name == "equalHeaders" then
      require table.sites.isEmpty "equal header/post allocated an unreachable operand token"
    else
      let node ← match source.nodes.findSome? fun
          | .statement node => match node.form with | .forLoop _ _ _ _ => some node | _ => none
          | _ => none with
        | some node => pure node | none => throw (IO.userError "parent for statement absent")
      require (table.sites.length == 1 && table.sites.all fun site => decide
        (site.site = .occurrence node.id.occurrence ∧ site.span = node.span ∧ site.kind = .value .add ∧ site.rhsType = .word))
        "initializer/post duplicate did not retain the same parent diagnostic"
    require ((← entry.run [scalar 1]) == scalar expected) "prepared for/match control changed"
    stable entry
  for name in ["initialFault", "postFault"] do
    let entry ← compileNamed program name
    let source ← sourceFor entry
    let table ← get "actual fault table" (SourceCoreAssignmentFaultSites.prepare source 100)
    let node ← match source.nodes.findSome? fun
        | .statement node => match node.form with | .forLoop _ _ _ _ => some node | _ => none
        | _ => none with
      | some node => pure node | none => throw (IO.userError "fault parent for absent")
    require (table.sites.length == 1 && table.sites.all fun site => decide
      (site.site = .occurrence node.id.occurrence ∧ site.kind = .value .add ∧ site.rhsType = .word))
      "fault diagnostic lost the authentic parent site"
    let result ← entry.invoke [scalar 1]
    match result.outcome with
    | .failed reason _ =>
      require (decide ((← result.diagnostic reason) = some {
        error := .invalidAssignmentOperands .add none (some .word),
        site := .occurrence node.id.occurrence, span := some node.span}))
        "header operand failure lost exact source diagnostic"
    | _ => throw (IO.userError "header operand failure did not stop")
    if name == "initialFault" then
      entry.checkCells [scalar 1] [(.word, some (scalar 1)), (.word, none),
        (.mapping .bool .word, some (.mapping .bool .word []))]
    stable entry
  IO.println "prepared match diagnostics: actual parent/suffix, header/post dedup, raw source typing, empty equal table, effects and resume GREEN"

end Tests.SourceCorePreparedMatchDiagnostics
end

section
-- leanmerge: from Solcore.Test.SourceCoreReachableImperativeForStatements
/-! The existing imperative Tree keeps terminal block/if children in the same
recursive positions as ordinary statements, for initializers and loop bodies.
Their suffix remains the exact originally issued code. Static stopping evidence
and the original source/native trace show that this suffix is not executed;
reachable nil is still Unit-only. The concrete final consumers close expression
and callee laws without adding runtime laws to static receipts. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 65536
namespace Tests.SourceCoreReachableImperativeForStatements
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open GeneralHeap ReadOnly CompatiblePayload CoreProof CallableAncestryPairedLookup
open CallableIndexedHistory SourceCoreCallableIndexedFrames RecursiveNamedCatalog
#check_failure SourceTypedRuntime.run
section Syntax
variable {source : TypedSource} {context : SourceSemantics.Context} {expressionSyntax : ExpressionId → Prop}
  {mode : Bool} {id : StatementId} {node : StatementNode} {rest left right : List StatementId}
  {expected : TypeSystem.Ty} {condition : ExpressionId} {conditionNode : ExpressionNode}

theorem actual_nonunit_block_syntax
    (unique : NodeOccurrencesUnique source) (found : source.lookupStatement? id = some node)
    (form : node.form = .block left) (annotation : node.type = expected)
    (inner : GenericImperativeFor.Syntax source expressionSyntax context (.statements false left) expected)
    (stops : GenericLexicalStatements.Stopped source left) :
    GenericImperativeFor.Syntax source expressionSyntax context (.statements mode (id :: rest)) expected :=
  .terminalBlock unique found form annotation inner stops

theorem actual_nonunit_if_syntax
    (unique : NodeOccurrencesUnique source) (found : source.lookupStatement? id = some node)
    (form : node.form = .ifThen condition left (some right)) (annotation : node.type = expected)
    (conditionFound : source.lookupExpression? condition = some conditionNode)
    (conditionType : conditionNode.type = .bool)
    (typed : ExpressionHasType source context condition conditionNode.type)
    (conditionSyntax : expressionSyntax condition)
    (thenSyntax : GenericImperativeFor.Syntax source expressionSyntax context (.statements false left) expected)
    (elseSyntax : GenericImperativeFor.Syntax source expressionSyntax context (.statements false right) expected)
    (thenStops : GenericLexicalStatements.Stopped source left)
    (elseStops : GenericLexicalStatements.Stopped source right) :
    GenericImperativeFor.Syntax source expressionSyntax context (.statements mode (id :: rest)) expected :=
  .terminalIf unique found form annotation conditionFound conditionType typed conditionSyntax thenSyntax elseSyntax thenStops elseStops

/-- Reachable nil remains restricted; terminality cannot authenticate an empty list. -/
theorem reachable_nil_nonunit (nonunit : expected ≠ .unit) :
    ¬ GenericImperativeFor.Syntax source expressionSyntax context (.statements true []) expected := by
  intro tree
  cases tree with
  | body lexical => cases lexical with
    | nil allowed => rcases allowed with impossible | unit; cases impossible; exact nonunit unit

theorem no_empty_stopped : ¬ GenericLexicalStatements.Stopped source [] := by
  rintro ⟨origin, summary, identity, stops⟩
  exact stops.nonempty rfl

/-- Source transport preserves the actual issuing source and callback equation.
It does not assume an arbitrary source-dependent policy accepts the view. -/
theorem original_suffix_transport {origin : TypedSource} {scope : SourceCoreLocalCell.Scope} {type : Ty} {code : Expr}
    (identity : GenericLexicalStatements.StatementSourceIdentity origin source)
    (issued : GenericLexicalStatements.IssuedSuffix origin scope mode rest type code) :
    GenericLexicalStatements.IssuedSuffix source scope mode rest type code :=
  issued.transport identity
end Syntax


section Extraction
open GenericImperativeFor
variable {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {values : SourceCoreCompatibleValues.Context} {source : TypedSource} {expressionSyntax : ExpressionId → Prop}
  {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {reasonAt : ExpressionId → Word} {policy : SourceCoreLoops.Policy}
  {administrative : Core.Context} {definitions : DataEnvironment}
  {invalidProjection : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Word}
  {invalidOperand : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Solcore.Syntax.ValueAssignOp → Word}
  {invalidUnary : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Word}
  {missingDefault : SourceCoreElaboration.ErrorSite → Resolved.LocalId → TypeSystem.Ty → Word}
theorem accepted_terminal_block (residualMode : Bool)
    (readPolicy : policy.readStatement = SourceCoreCompatibleDataExpressions.readStatement values.checked)
    (binderPolicy : ∀ scope binder, binder.scheme.quantified = [] →
      policy.lowerBinder source scope binder = SourceCoreCompatibleDataExpressions.lowerBinder values.checked source scope binder)
    (allocationPolicy : policy.sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator frame globals
      (layouts.allocatorAt owner active onError)))
    (expressions : ∀ sourceContext, sourceContext.typeVariables = [] → sourceContext.residualTypeVariables = residualMode →
      sourceContext.signatures = values.checked.signatures →
      ∀ {scope fuel id node lowered}, CompatibleExpressionReads.ScopeDeclarations source scope sourceContext → expressionSyntax id →
      source.lookupExpression? id = some node → ExpressionHasType source sourceContext id node.type →
      policy.lowerExpression fuel source scope id reasonAt = .ok lowered →
      certificates sourceContext scope id lowered)
    (assignments : CompatibleAssignmentStatements.AssignmentPolicy policy values invalidProjection invalidOperand missingDefault)
    (unaryPolicy : CompatibleBitNotStatements.Policy policy values invalidProjection invalidUnary missingDefault)
    (unique : NodeOccurrencesUnique source)
    (assignmentExpressions : ∀ sourceContext scope fuel id lowered,
      sourceContext.typeVariables = [] → sourceContext.residualTypeVariables = residualMode →
      sourceContext.signatures = values.checked.signatures →
      CompatibleExpressionReads.ScopeDeclarations source scope sourceContext →
      expressionSyntax id → ∀ node, source.lookupExpression? id = some node →
      ExpressionHasType source sourceContext id node.type →
      policy.lowerExpression fuel source scope id reasonAt = .ok lowered →
        certificates sourceContext scope id lowered ∧
        HasType (SourceCoreLocalCell.coreContext scope ++ administrative) lowered.expression
          (LanguageResult.resultType lowered.type) definitions)
    {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope} {mode : Bool} {id : StatementId}
    {node : StatementNode} {statements rest : List StatementId} {expected : TypeSystem.Ty}
    (exactUnique : NodeOccurrencesUnique source)
    (found : source.lookupStatement? id = some node) (form : node.form = .block statements)
    (annotation : node.type = expected)
    (inner : Syntax source expressionSyntax context (.statements false statements) expected)
    (stops : GenericLexicalStatements.Stopped source statements)
    (closed : context.typeVariables = []) (residual : context.residualTypeVariables = residualMode)
    (sourceSignatures : context.signatures = values.checked.signatures)
    (declarations : CompatibleExpressionReads.ScopeDeclarations source scope context)
    {fuel : Nat} {type : Ty} {code : Expr} {selfReason : Word} {nativeType : Ty}
    (projection : values.checked.catalog.project expected = .ok type)
    (accepted : SourceCoreLoops.lowerFlowStatementsWithPolicy policy fuel source scope (id :: rest) type reasonAt mode selfReason = .ok code)
    (nativeTyped : HasType (SourceCoreLocalCell.coreContext scope ++ administrative) code nativeType definitions) :
    Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
      context scope (.statements mode (id :: rest)) expected type code := by
  exact tree_of_typed_flow_with_residual residualMode readPolicy binderPolicy allocationPolicy expressions assignments unaryPolicy unique
    assignmentExpressions (.terminalBlock exactUnique found form annotation inner stops) closed residual sourceSignatures declarations projection accepted nativeTyped

theorem accepted_terminal_if (residualMode : Bool)
    (readPolicy : policy.readStatement = SourceCoreCompatibleDataExpressions.readStatement values.checked)
    (binderPolicy : ∀ scope binder, binder.scheme.quantified = [] →
      policy.lowerBinder source scope binder = SourceCoreCompatibleDataExpressions.lowerBinder values.checked source scope binder)
    (allocationPolicy : policy.sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator frame globals
      (layouts.allocatorAt owner active onError)))
    (expressions : ∀ sourceContext, sourceContext.typeVariables = [] → sourceContext.residualTypeVariables = residualMode →
      sourceContext.signatures = values.checked.signatures →
      ∀ {scope fuel id node lowered}, CompatibleExpressionReads.ScopeDeclarations source scope sourceContext → expressionSyntax id →
      source.lookupExpression? id = some node → ExpressionHasType source sourceContext id node.type →
      policy.lowerExpression fuel source scope id reasonAt = .ok lowered →
      certificates sourceContext scope id lowered)
    (assignments : CompatibleAssignmentStatements.AssignmentPolicy policy values invalidProjection invalidOperand missingDefault)
    (unaryPolicy : CompatibleBitNotStatements.Policy policy values invalidProjection invalidUnary missingDefault)
    (unique : NodeOccurrencesUnique source)
    (assignmentExpressions : ∀ sourceContext scope fuel id lowered,
      sourceContext.typeVariables = [] → sourceContext.residualTypeVariables = residualMode →
      sourceContext.signatures = values.checked.signatures →
      CompatibleExpressionReads.ScopeDeclarations source scope sourceContext →
      expressionSyntax id → ∀ node, source.lookupExpression? id = some node →
      ExpressionHasType source sourceContext id node.type →
      policy.lowerExpression fuel source scope id reasonAt = .ok lowered →
        certificates sourceContext scope id lowered ∧
        HasType (SourceCoreLocalCell.coreContext scope ++ administrative) lowered.expression
          (LanguageResult.resultType lowered.type) definitions)
    {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope} {mode : Bool} {id : StatementId}
    {node : StatementNode} {condition : ExpressionId} {conditionNode : ExpressionNode}
    {thenBody elseBody rest : List StatementId} {expected : TypeSystem.Ty}
    (exactUnique : NodeOccurrencesUnique source)
    (found : source.lookupStatement? id = some node) (form : node.form = .ifThen condition thenBody (some elseBody))
    (annotation : node.type = expected)
    (conditionFound : source.lookupExpression? condition = some conditionNode)
    (conditionType : conditionNode.type = .bool)
    (typed : ExpressionHasType source context condition conditionNode.type)
    (conditionSyntax : expressionSyntax condition)
    (thenSyntax : Syntax source expressionSyntax context (.statements false thenBody) expected)
    (elseSyntax : Syntax source expressionSyntax context (.statements false elseBody) expected)
    (thenStops : GenericLexicalStatements.Stopped source thenBody)
    (elseStops : GenericLexicalStatements.Stopped source elseBody)
    (closed : context.typeVariables = []) (residual : context.residualTypeVariables = residualMode)
    (sourceSignatures : context.signatures = values.checked.signatures)
    (declarations : CompatibleExpressionReads.ScopeDeclarations source scope context)
    {fuel : Nat} {type : Ty} {code : Expr} {selfReason : Word} {nativeType : Ty}
    (projection : values.checked.catalog.project expected = .ok type)
    (accepted : SourceCoreLoops.lowerFlowStatementsWithPolicy policy fuel source scope (id :: rest) type reasonAt mode selfReason = .ok code)
    (nativeTyped : HasType (SourceCoreLocalCell.coreContext scope ++ administrative) code nativeType definitions) :
    Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
      context scope (.statements mode (id :: rest)) expected type code := by
  exact tree_of_typed_flow_with_residual residualMode readPolicy binderPolicy allocationPolicy expressions assignments unaryPolicy unique
    assignmentExpressions (.terminalIf exactUnique found form annotation conditionFound conditionType typed conditionSyntax thenSyntax elseSyntax thenStops elseStops) closed residual sourceSignatures declarations projection accepted nativeTyped
end Extraction

section Concrete
variable {checked : Checked} {base : Base checked}
  {prepared : SourceCoreCallableIndexedAncestry.Prepared base} {values : ValuesContext}
  {ambient : AmbientDefinitions values.checked.catalog.definitions} {program : SourceSemantics.Program}
  {body : BuiltinNamedCalls.Body prepared values ambient.definitions program} {locations : Locations} {capturePrefix : Nat}
  {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {compilation : SourceCoreFunctions.Context} {fuel : Nat} {source : TypedSource}
  {expressionSyntax : ExpressionId → Prop} {administrative : Core.Context}
  {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word}
  (functions : FunctionModel values.checked.catalog ambient)
  (definitions : layouts.definitions = ambient.definitions) (registered : frame.Registered ambient.definitions)
  {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends values.registry registry)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)
  (runtimeViews : FunctionRuntimeViews functions) (evidence : Dynamic.EvidenceEnvironment)
  (unique : NodeOccurrencesUnique source)
  (owners : (program.functions.map (fun definition => definition.body.owner)).Nodup)
  {faults : FunctionCalls.FaultRep}
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))
  (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((reasonAt id).add tag))
  (bodyUninitialized : ∀ id location, faults (.uninitializedLocation location) (body.reasonAt id))
  (bodyMissing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((body.reasonAt id).add tag))


include definitions registered extension faithful observations runtimeViews unique owners uninitialized missing bodyUninitialized bodyMissing in
theorem concrete_preserves (budget : Nat)
    {context : SourceSemantics.Context} {scope : Scope} {mode : Bool}
    {statements : List StatementId} {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (tree : GenericImperativeFor.Tree layouts owner active frame globals onError values source expressionSyntax
      (fun context => CompatibleExpressionCalls.Tree (RecursiveNamedCatalog.Head [Header.of_body body] compilation source context)
        fuel values source context solved reasonAt) ambient.definitions administrative
      context scope (.statements mode statements) expected type code)
    (errors : GenericImperativeFor.Tree.ReachableErrors registry faults tree) :
    RecursiveNamedHeaderContracts.AtMost budget (fun size => RecursiveNamedLoopContracts.PreservesAt functions program evidence
      (entry := protectedEntry [Header.of_body body] locations capturePrefix compilation.administrativePrefix)
      (source := source) (context := context) (registry := registry) (faults := faults)
      (solved := solved) (frameLayout := frame) (globals := globals) (administrative := administrative)
      size (scope := scope) mode statements expected type code) := by
  apply RecursiveNamedImperativeFor.preservesAt_for functions definitions registered extension program evidence
    entry_transport entry_binds budget faithful observations ?_ .reachable unique tree errors
  intro context valid child within
  exact SourceCoreRecursiveNamedExpressionTreeBounds.concrete_preserves_at
    functions extension body bodyUninitialized bodyMissing faithful observations runtimeViews
    valid unique owners uninitialized missing budget child within

include definitions registered extension faithful observations runtimeViews unique uninitialized missing bodyUninitialized bodyMissing in
theorem concrete_reflects (budget : Nat)
    {context : SourceSemantics.Context} {scope : Scope} {mode : Bool}
    {statements : List StatementId} {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (tree : GenericImperativeFor.Tree layouts owner active frame globals onError values source expressionSyntax
      (fun context => CompatibleExpressionCalls.Tree (RecursiveNamedCatalog.Head [Header.of_body body] compilation source context)
        fuel values source context solved reasonAt) ambient.definitions administrative
      context scope (.statements mode statements) expected type code)
    (errors : GenericImperativeFor.Tree.ReachableErrors registry faults tree) :
    RecursiveNamedBoundedContracts.Below budget (fun size => RecursiveNamedLoopContracts.ReflectsAt functions program evidence
      (entry := protectedEntry [Header.of_body body] locations capturePrefix compilation.administrativePrefix)
      (source := source) (context := context) (registry := registry) (faults := faults)
      (solved := solved) (frameLayout := frame) (globals := globals) (administrative := administrative)
      size (scope := scope) mode statements expected type code) := by
  apply RecursiveNamedImperativeFor.reflectsAt_for functions definitions registered extension program evidence
    entry_transport entry_binds budget ?_ faithful observations .reachable runtimeViews unique tree errors
  intro context valid child smaller
  exact SourceCoreRecursiveNamedExpressionTreeBounds.concrete_reflects_at
    functions extension body bodyUninitialized bodyMissing faithful observations runtimeViews
    valid uninitialized missing budget child (Nat.le_of_lt smaller)

include definitions registered extension faithful observations runtimeViews unique owners uninitialized missing bodyUninitialized bodyMissing in
/-- The inclusive endpoint used by a source-body strong induction. No N+1
budget and no callee law at N is supplied by this consumer. -/
theorem concrete_preserves_at_top (size : Nat)
    {context : SourceSemantics.Context} {scope : Scope} {mode : Bool}
    {statements : List StatementId} {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (tree : GenericImperativeFor.Tree layouts owner active frame globals onError values source expressionSyntax
      (fun context => CompatibleExpressionCalls.Tree (RecursiveNamedCatalog.Head [Header.of_body body] compilation source context)
        fuel values source context solved reasonAt) ambient.definitions administrative
      context scope (.statements mode statements) expected type code)
    (errors : GenericImperativeFor.Tree.ReachableErrors registry faults tree) :
    RecursiveNamedLoopContracts.PreservesAt functions program evidence
      (entry := protectedEntry [Header.of_body body] locations capturePrefix compilation.administrativePrefix)
      (source := source) (context := context) (registry := registry) (faults := faults)
      (solved := solved) (frameLayout := frame) (globals := globals) (administrative := administrative)
      size (scope := scope) mode statements expected type code :=
  concrete_preserves functions definitions registered extension faithful observations runtimeViews evidence unique owners
    uninitialized missing bodyUninitialized bodyMissing size tree errors size (Nat.le_refl size)

include definitions registered extension faithful observations runtimeViews unique uninitialized missing bodyUninitialized bodyMissing in
/-- A completed native body gives its own source size, without relating source
cost to the original native budget. -/
theorem concrete_native_only (budget size : Nat) (smaller : size < budget)
    {context : SourceSemantics.Context} {scope : Scope} {mode : Bool}
    {statements : List StatementId} {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (tree : GenericImperativeFor.Tree layouts owner active frame globals onError values source expressionSyntax
      (fun context => CompatibleExpressionCalls.Tree (RecursiveNamedCatalog.Head [Header.of_body body] compilation source context)
        fuel values source context solved reasonAt) ambient.definitions administrative
      context scope (.statements mode statements) expected type code)
    (errors : GenericImperativeFor.Tree.ReachableErrors registry faults tree) :
    RecursiveNamedLoopContracts.ReflectsAt functions program evidence
      (entry := protectedEntry [Header.of_body body] locations capturePrefix compilation.administrativePrefix)
      (source := source) (context := context) (registry := registry) (faults := faults)
      (solved := solved) (frameLayout := frame) (globals := globals) (administrative := administrative)
      size (scope := scope) mode statements expected type code :=
  concrete_reflects functions definitions registered extension faithful observations runtimeViews evidence unique
    uninitialized missing bodyUninitialized bodyMissing budget tree errors size smaller
include definitions registered extension faithful observations runtimeViews unique owners uninitialized missing bodyUninitialized bodyMissing in
theorem terminal_block_preserves_at (size : Nat)
    {context : SourceSemantics.Context} {scope : Scope} {mode : Bool} {id : StatementId} {node : StatementNode}
    {rest : List StatementId} {expected : TypeSystem.Ty} {type : Ty} {suffix : Expr}
    (exactUnique : NodeOccurrencesUnique source)
    (found : source.lookupStatement? id = some node) {statements : List StatementId} {innerCode : Expr}
    (form : node.form = .block statements)
    (inner : GenericImperativeFor.Tree layouts owner active frame globals onError values source expressionSyntax
      (fun context => CompatibleExpressionCalls.Tree (RecursiveNamedCatalog.Head [Header.of_body body] compilation source context)
        fuel values source context solved reasonAt) ambient.definitions administrative context scope
      (.statements false statements) expected type innerCode)
    (stops : GenericLexicalStatements.Stopped source statements)
    (issued : GenericLexicalStatements.IssuedSuffix source scope mode rest type suffix)
    (innerErrors : GenericImperativeFor.Tree.ReachableErrors registry faults inner) :
    RecursiveNamedLoopContracts.PreservesAt functions program evidence
      (entry := protectedEntry [Header.of_body body] locations capturePrefix compilation.administrativePrefix)
      (source := source) (context := context) (registry := registry) (faults := faults)
      (solved := solved) (frameLayout := frame) (globals := globals) (administrative := administrative)
      size (scope := scope) mode (id :: rest) expected type (LocalLoop.sequence type innerCode suffix) := by
  exact concrete_preserves_at_top functions definitions registered extension faithful observations runtimeViews evidence unique owners uninitialized missing bodyUninitialized bodyMissing size
    (.terminalBlock exactUnique found form inner stops issued) (.terminalBlock (unique := exactUnique) (found := found) (form := form) (stops := stops) (issued := issued) innerErrors)

include definitions registered extension faithful observations runtimeViews unique uninitialized missing bodyUninitialized bodyMissing in
theorem terminal_block_reflects_at (budget size : Nat) (smaller : size < budget)
    {context : SourceSemantics.Context} {scope : Scope} {mode : Bool} {id : StatementId} {node : StatementNode}
    {rest : List StatementId} {expected : TypeSystem.Ty} {type : Ty} {suffix : Expr}
    (exactUnique : NodeOccurrencesUnique source)
    (found : source.lookupStatement? id = some node) {statements : List StatementId} {innerCode : Expr}
    (form : node.form = .block statements)
    (inner : GenericImperativeFor.Tree layouts owner active frame globals onError values source expressionSyntax
      (fun context => CompatibleExpressionCalls.Tree (RecursiveNamedCatalog.Head [Header.of_body body] compilation source context)
        fuel values source context solved reasonAt) ambient.definitions administrative context scope
      (.statements false statements) expected type innerCode)
    (stops : GenericLexicalStatements.Stopped source statements)
    (issued : GenericLexicalStatements.IssuedSuffix source scope mode rest type suffix)
    (innerErrors : GenericImperativeFor.Tree.ReachableErrors registry faults inner) :
    RecursiveNamedLoopContracts.ReflectsAt functions program evidence
      (entry := protectedEntry [Header.of_body body] locations capturePrefix compilation.administrativePrefix)
      (source := source) (context := context) (registry := registry) (faults := faults)
      (solved := solved) (frameLayout := frame) (globals := globals) (administrative := administrative)
      size (scope := scope) mode (id :: rest) expected type (LocalLoop.sequence type innerCode suffix) := by
  exact concrete_native_only functions definitions registered extension faithful observations runtimeViews evidence unique uninitialized missing bodyUninitialized bodyMissing budget size smaller
    (.terminalBlock exactUnique found form inner stops issued) (.terminalBlock (unique := exactUnique) (found := found) (form := form) (stops := stops) (issued := issued) innerErrors)

include definitions registered extension faithful observations runtimeViews unique owners uninitialized missing bodyUninitialized bodyMissing in
theorem terminal_if_preserves_at (size : Nat)
    {context : SourceSemantics.Context} {scope : Scope} {mode : Bool} {id : StatementId} {node : StatementNode}
    {rest : List StatementId} {expected : TypeSystem.Ty} {type : Ty} {suffix : Expr}
    (exactUnique : NodeOccurrencesUnique source)
    (found : source.lookupStatement? id = some node) {condition : ExpressionId} {conditionNode : ExpressionNode}
    {thenBody elseBody : List StatementId} {conditionCode thenCode elseCode : Expr}
    (form : node.form = .ifThen condition thenBody (some elseBody))
    (conditionFound : source.lookupExpression? condition = some conditionNode)
    (conditionType : conditionNode.type = .bool)
    (conditionTree : CompatibleExpressionCalls.Tree (RecursiveNamedCatalog.Head [Header.of_body body] compilation source context)
      fuel values source context solved reasonAt scope condition ⟨.bool, conditionCode⟩)
    (thenTree : GenericImperativeFor.Tree layouts owner active frame globals onError values source expressionSyntax
      (fun context => CompatibleExpressionCalls.Tree (RecursiveNamedCatalog.Head [Header.of_body body] compilation source context)
        fuel values source context solved reasonAt) ambient.definitions administrative context scope
      (.statements false thenBody) expected type thenCode)
    (elseTree : GenericImperativeFor.Tree layouts owner active frame globals onError values source expressionSyntax
      (fun context => CompatibleExpressionCalls.Tree (RecursiveNamedCatalog.Head [Header.of_body body] compilation source context)
        fuel values source context solved reasonAt) ambient.definitions administrative context scope
      (.statements false elseBody) expected type elseCode)
    (thenStops : GenericLexicalStatements.Stopped source thenBody)
    (elseStops : GenericLexicalStatements.Stopped source elseBody)
    (issued : GenericLexicalStatements.IssuedSuffix source scope mode rest type suffix)
    (thenErrors : GenericImperativeFor.Tree.ReachableErrors registry faults thenTree)
    (elseErrors : GenericImperativeFor.Tree.ReachableErrors registry faults elseTree) :
    RecursiveNamedLoopContracts.PreservesAt functions program evidence
      (entry := protectedEntry [Header.of_body body] locations capturePrefix compilation.administrativePrefix)
      (source := source) (context := context) (registry := registry) (faults := faults)
      (solved := solved) (frameLayout := frame) (globals := globals) (administrative := administrative)
      size (scope := scope) mode (id :: rest) expected type (LocalLoop.sequence type (LocalLoop.conditional type conditionCode thenCode elseCode) suffix) := by
  exact concrete_preserves_at_top functions definitions registered extension faithful observations runtimeViews evidence unique owners uninitialized missing bodyUninitialized bodyMissing size
    (.terminalIf exactUnique found form conditionFound conditionType conditionTree thenTree elseTree thenStops elseStops issued) (.terminalIf (unique := exactUnique) (found := found) (form := form) (conditionFound := conditionFound) (conditionType := conditionType) (conditionTree := conditionTree) (thenStops := thenStops) (elseStops := elseStops) (issued := issued) thenErrors elseErrors)

include definitions registered extension faithful observations runtimeViews unique uninitialized missing bodyUninitialized bodyMissing in
theorem terminal_if_reflects_at (budget size : Nat) (smaller : size < budget)
    {context : SourceSemantics.Context} {scope : Scope} {mode : Bool} {id : StatementId} {node : StatementNode}
    {rest : List StatementId} {expected : TypeSystem.Ty} {type : Ty} {suffix : Expr}
    (exactUnique : NodeOccurrencesUnique source)
    (found : source.lookupStatement? id = some node) {condition : ExpressionId} {conditionNode : ExpressionNode}
    {thenBody elseBody : List StatementId} {conditionCode thenCode elseCode : Expr}
    (form : node.form = .ifThen condition thenBody (some elseBody))
    (conditionFound : source.lookupExpression? condition = some conditionNode)
    (conditionType : conditionNode.type = .bool)
    (conditionTree : CompatibleExpressionCalls.Tree (RecursiveNamedCatalog.Head [Header.of_body body] compilation source context)
      fuel values source context solved reasonAt scope condition ⟨.bool, conditionCode⟩)
    (thenTree : GenericImperativeFor.Tree layouts owner active frame globals onError values source expressionSyntax
      (fun context => CompatibleExpressionCalls.Tree (RecursiveNamedCatalog.Head [Header.of_body body] compilation source context)
        fuel values source context solved reasonAt) ambient.definitions administrative context scope
      (.statements false thenBody) expected type thenCode)
    (elseTree : GenericImperativeFor.Tree layouts owner active frame globals onError values source expressionSyntax
      (fun context => CompatibleExpressionCalls.Tree (RecursiveNamedCatalog.Head [Header.of_body body] compilation source context)
        fuel values source context solved reasonAt) ambient.definitions administrative context scope
      (.statements false elseBody) expected type elseCode)
    (thenStops : GenericLexicalStatements.Stopped source thenBody)
    (elseStops : GenericLexicalStatements.Stopped source elseBody)
    (issued : GenericLexicalStatements.IssuedSuffix source scope mode rest type suffix)
    (thenErrors : GenericImperativeFor.Tree.ReachableErrors registry faults thenTree)
    (elseErrors : GenericImperativeFor.Tree.ReachableErrors registry faults elseTree) :
    RecursiveNamedLoopContracts.ReflectsAt functions program evidence
      (entry := protectedEntry [Header.of_body body] locations capturePrefix compilation.administrativePrefix)
      (source := source) (context := context) (registry := registry) (faults := faults)
      (solved := solved) (frameLayout := frame) (globals := globals) (administrative := administrative)
      size (scope := scope) mode (id :: rest) expected type (LocalLoop.sequence type (LocalLoop.conditional type conditionCode thenCode elseCode) suffix) := by
  exact concrete_native_only functions definitions registered extension faithful observations runtimeViews evidence unique uninitialized missing bodyUninitialized bodyMissing budget size smaller
    (.terminalIf exactUnique found form conditionFound conditionType conditionTree thenTree elseTree thenStops elseStops issued) (.terminalIf (unique := exactUnique) (found := found) (form := form) (conditionFound := conditionFound) (conditionType := conditionType) (conditionTree := conditionTree) (thenStops := thenStops) (elseStops := elseStops) (issued := issued) thenErrors elseErrors)

end Concrete

private def content : String := String.intercalate "\n" [
  "function both(flag: Bool) returns (Word) { if (flag) { for (let i = 0; i < 1; i += 1) {} return 7; } else { while (false) {} return 9; } }",
  "function block() returns (Word) { { for (let i = 0; i < 1; i += 1) {} return 11; } }",
  "function nested(flag: Bool) returns (Word) { let saved = 13; { if (flag) { for (; true; ) { break; } return saved; } else { while (true) { break; } return 17; } } }",
  "function inFor(flag: Bool) returns (Word) { for (; true; ) { if (flag) { return 43; } else { return 47; } let gap: Word; gap; } return 99; }",
  "function inWhile(flag: Bool) returns (Word) { while (true) { { if (flag) { return 53; } else { return 59; } } let gap: Word; gap; } return 99; }",
  "function reachable(flag: Bool) returns (Word) { if (flag) { return 19; } return 23; }",
  "function dead(flag: Bool) returns (Word) { if (flag) { for (; true; ) { break; } return 29; } else { while (false) {} return 31; } let gap: Word; gap; }",
  "function failed(flag: Bool) returns (Word) { let prior = 37; if (flag) { for (; false; ) {} let gap: Word; return gap; } else { while (false) {} return 41; } let skipped = 99; return skipped; }",
  "function unit() returns (Unit) { { for (; true; ) { break; } return; } let gap: Word; gap; }"
]
private def w (n : Nat) : SourceTypedRuntime.Value := .word (Word.ofNatModulo n)
private def get {α ε : Type} [Repr ε] := @SourceCoreUnifiedCorpusSupport.get α ε _
private def require := SourceCoreUnifiedCorpusSupport.assertTrue

private def inspect (compiled : SourceCoreUnifiedCompilation.Compiled) : IO Unit := do
  let prepared := compiled.indexed
  let diagnostics ← match prepared.base.diagnostics with
    | none => throw (IO.userError "reachable imperative integration missing diagnostics")
    | some diagnostic => pure diagnostic.program
  let diagnostics := match prepared.base.callableContext with
    | none => diagnostics
    | some native => {diagnostics with rootTable := native.diagnostics.rootTable}
  let parents ← get "reachable imperative integration parent contexts"
    (SourceCoreStageCodebook.prepareContexts prepared.base.sourceProgram prepared.base.plan
      (prepared.base.locals.bindings.flatMap (·.instances)))
  let mut terminalAnnotations := 0
  let mut reachableAnnotations := 0
  let mut deadSuffixes := 0
  let mut forNodes := 0
  let mut whileNodes := 0
  for named in prepared.base.functions do
    let actual := (CallableIndexedNamedGeneration.representation prepared).atContext named.signature.key []
    let own ← match diagnostics.base.find? named.signature.key with
      | none => throw (IO.userError "reachable imperative integration missing own diagnostics")
      | some own => pure own
    let source := CallableIndexedNamedGeneration.source named
    let scope := named.inputs.reverse.map (fun binding => (binding.1.id, binding.2))
    let reasonAt := diagnostics.reasonAt named.signature.key
    let lower := SourceCoreGeneralFunctions.lowerContextualExpression prepared.base.sourceProgram actual
      prepared.base.sourceProgram.signatures prepared.base.locals parents own.assignments diagnostics
      (CallableIndexedNamedGeneration.context prepared named) prepared.base.callableContext none none
    let policy : SourceCoreLoops.Policy := {
      actual.loopsWithSourceCells actual.expressions.sourceCells named.specialized.function.solvedRequirements
        own.assignments diagnostics named.signature.key lower with
      sourceCells := actual.expressions.sourceCells
      lowerBinder := SourceCoreGeneralFunctions.contextualBinder actual prepared.base.locals named.signature.key [] }
    let statements ← get "reachable imperative integration actual roots"
      (source.roots.mapM (m := Except SourceCoreGeneralFunctions.Error) (fun
        | .statement id => pure id | .expression id => throw (.expectedStatementRoot id)))
    let body ← get "reachable imperative integration actual complete body"
      (SourceCoreLoops.lowerStatementsWithPolicy policy prepared.fuel source scope statements
        named.signature.resultType reasonAt own.fellThroughReason own.table.escapedReason)
    let same ← get "reachable imperative integration actual compiler body"
      (CallableIndexedNamedGeneration.bodyAction prepared named diagnostics parents own statements)
    require (body == same) "reachable imperative integration changed actual compiler body"
    for item in source.nodes do
      match item with
      | .statement node =>
          match node.form with
          | .block _ | .ifThen _ _ (some _) =>
              if node.type == .word then terminalAnnotations := terminalAnnotations + 1
          | .ifThen _ _ none =>
              require (node.type == .unit) "reachable one-branch annotation changed"
              reachableAnnotations := reachableAnnotations + 1
          | .forLoop _ _ _ _ => forNodes := forNodes + 1
          | .whileLoop _ _ => whileNodes := whileNodes + 1
          | _ => pure ()
      | _ => pure ()
    match statements with
    | id :: rest =>
        let node ← match source.lookupStatement? id with
          | none => throw (IO.userError "reachable imperative integration root lookup missing")
          | some node => pure node
        match node.form with
        | .ifThen condition left (some right) =>
            let (_, _) ← get "reachable imperative integration actual statement read" (policy.readStatement source id)
            let condition ← get "reachable imperative integration actual condition" (lower (prepared.fuel - 1) source scope condition reasonAt)
            let leftCode ← get "reachable imperative integration actual left"
              (SourceCoreLoops.lowerFlowStatementsWithPolicy policy (prepared.fuel - 1) source scope left
                named.signature.resultType reasonAt false own.table.escapedReason)
            let rightCode ← get "reachable imperative integration actual right"
              (SourceCoreLoops.lowerFlowStatementsWithPolicy policy (prepared.fuel - 1) source scope right
                named.signature.resultType reasonAt false own.table.escapedReason)
            let suffix ← get "reachable imperative integration emitted suffix"
              (SourceCoreLoops.lowerFlowStatementsWithPolicy policy (prepared.fuel - 1) source scope rest
                named.signature.resultType reasonAt true own.table.escapedReason)
            let whole ← get "reachable imperative integration whole flow"
              (SourceCoreLoops.lowerFlowStatementsWithPolicy policy prepared.fuel source scope statements
                named.signature.resultType reasonAt true own.table.escapedReason)
            require (whole == LocalLoop.sequence named.signature.resultType
              (LocalLoop.conditional named.signature.resultType condition.expression leftCode rightCode) suffix)
              "reachable imperative integration did not retain original emitted suffix"
            if !rest.isEmpty then deadSuffixes := deadSuffixes + 1
        | .block inner =>
            let innerCode ← get "reachable imperative integration actual block child"
              (SourceCoreLoops.lowerFlowStatementsWithPolicy policy (prepared.fuel - 1) source scope inner
                named.signature.resultType reasonAt false own.table.escapedReason)
            let suffix ← get "reachable imperative integration emitted block suffix"
              (SourceCoreLoops.lowerFlowStatementsWithPolicy policy (prepared.fuel - 1) source scope rest
                named.signature.resultType reasonAt true own.table.escapedReason)
            let whole ← get "reachable imperative integration whole block flow"
              (SourceCoreLoops.lowerFlowStatementsWithPolicy policy prepared.fuel source scope statements
                named.signature.resultType reasonAt true own.table.escapedReason)
            require (whole == LocalLoop.sequence named.signature.resultType innerCode suffix)
              "reachable imperative integration did not retain original block suffix"
        | _ => pure ()
    | [] => pure ()
  require (terminalAnnotations == 9 && reachableAnnotations == 1 && deadSuffixes == 1 && forNodes == 7 && whileNodes == 5)
    s!"reachable continuation fixture coverage changed: {terminalAnnotations}/{reachableAnnotations}/{deadSuffixes}/{forNodes}/{whileNodes}"

private def finish (compiled : SourceCoreUnifiedCompilation.Compiled) (name : String)
    (arguments : List SourceTypedRuntime.Value) (fuel : Nat) (initial : SourceTypedRuntime.RuntimeState) : IO SourceTypedRuntime.RunResult := do
  let first ← SourceCoreUnifiedCorpusSupport.execute compiled name arguments fuel initial
  pure (← get "reachable imperative integration public resume" (first.resume 300000)).observation

def run : IO Unit := do
  let compiled ← SourceCoreUnifiedCorpusSupport.prepare "reachable imperative integration" content
    ["both", "block", "nested", "inFor", "inWhile", "reachable", "dead", "failed", "unit"]
  inspect compiled
  let initial : SourceTypedRuntime.RuntimeState := {heap := [⟨.word, some (w 821)⟩]}
  let successes : List (String × List SourceTypedRuntime.Value × SourceTypedRuntime.Value × List (TypeSystem.Ty × Option SourceTypedRuntime.Value)) := [
    ("both", [.bool true], w 7, [(.bool, some (.bool true)), (.word, some (w 1))]),
    ("both", [.bool false], w 9, [(.bool, some (.bool false))]),
    ("block", [], w 11, [(.word, some (w 1))]),
    ("nested", [.bool true], w 13, [(.bool, some (.bool true)), (.word, some (w 13))]),
    ("nested", [.bool false], w 17, [(.bool, some (.bool false)), (.word, some (w 13))]),
    ("inFor", [.bool true], w 43, [(.bool, some (.bool true))]),
    ("inFor", [.bool false], w 47, [(.bool, some (.bool false))]),
    ("inWhile", [.bool true], w 53, [(.bool, some (.bool true))]),
    ("inWhile", [.bool false], w 59, [(.bool, some (.bool false))]),
    ("reachable", [.bool true], w 19, [(.bool, some (.bool true))]),
    ("reachable", [.bool false], w 23, [(.bool, some (.bool false))]),
    ("dead", [.bool true], w 29, [(.bool, some (.bool true))]),
    ("dead", [.bool false], w 31, [(.bool, some (.bool false))]),
    ("failed", [.bool false], w 41, [(.bool, some (.bool false)), (.word, some (w 37))]),
    ("unit", [], .unit, [])]
  let baselines ← successes.mapM (fun test => finish compiled test.1 test.2.1 300000 initial)
  let failure ← finish compiled "failed" [.bool true] 300000 initial
  for fuel in [0, 31, 300000] do
    for ((name, arguments, expected, expectedCells), baseline) in successes.zip baselines do
      let observed ← finish compiled name arguments fuel initial
      require (reprStr observed == reprStr baseline) s!"reachable imperative integration full resume changed {name}"
      match observed with
      | .done result final =>
          require (reprStr result == reprStr expected) s!"reachable imperative integration result changed {name}"
          require (reprStr final.heap == reprStr (initial.heap ++ expectedCells.map (fun (type, value) => ⟨type, value⟩)))
            s!"reachable imperative integration ordered heap/dead suffix changed {name}"
      | other => throw (IO.userError s!"reachable imperative integration expected done {name}: {reprStr other}")
    let observed ← finish compiled "failed" [.bool true] fuel initial
    require (reprStr observed == reprStr failure) "reachable imperative integration full fault resume changed"
    match observed with
    | .fault (.uninitializedLocal _) final =>
        require (reprStr final.heap == reprStr (initial.heap ++ [⟨.bool, some (.bool true)⟩, ⟨.word, some (w 37)⟩, ⟨.word, none⟩]))
          "reachable imperative integration fault executed a dead suffix or changed its prefix"
    | other => throw (IO.userError s!"reachable imperative integration expected head fault: {reprStr other}")
  IO.println "reachable imperative integration: same recursive for/while grammar, non-Unit terminal annotations, source stops, original native child, emitted dead suffix, ordered full heaps and public resume GREEN"

end Tests.SourceCoreReachableImperativeForStatements
end

section
-- leanmerge: from Solcore.Test.SourceCoreReachableImperativeMatchStatements
/-! Terminal block/if constructors extend the existing same recursive match
Tree. Reached children retain static stopping receipts and the suffix retains
its complete original compiler equation. Match ledgers are required only on
reached children. Actual body consumers close all Builtin expression/child
meaning. Direct terminal match heads, residual=true extraction and protected
bounded catalog match closure remain separate boundaries. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 65536
namespace Tests.SourceCoreReachableImperativeMatchStatements
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open GeneralHeap ReadOnly CompatiblePayload CoreProof CallableAncestryPairedLookup
open CallableIndexedHistory SourceCoreCallableIndexedFrames BuiltinImperativeMatchBody
#check_failure SourceTypedRuntime.run
section Syntax
variable {source : TypedSource} {context : SourceSemantics.Context} {expressionSyntax : ExpressionId → Prop}
  {mode : Bool} {id : StatementId} {node : StatementNode} {rest left right : List StatementId}
  {expected : TypeSystem.Ty} {condition : ExpressionId} {conditionNode : ExpressionNode}

theorem actual_nonunit_block_syntax
    (unique : NodeOccurrencesUnique source) (found : source.lookupStatement? id = some node)
    (form : node.form = .block left) (annotation : node.type = expected)
    (inner : GenericImperativeMatch.Syntax source expressionSyntax context (.statements false left) expected)
    (stops : GenericLexicalStatements.Stopped source left) :
    GenericImperativeMatch.Syntax source expressionSyntax context (.statements mode (id :: rest)) expected :=
  .terminalBlock unique found form annotation inner stops

theorem actual_nonunit_if_syntax
    (unique : NodeOccurrencesUnique source) (found : source.lookupStatement? id = some node)
    (form : node.form = .ifThen condition left (some right)) (annotation : node.type = expected)
    (conditionFound : source.lookupExpression? condition = some conditionNode)
    (conditionType : conditionNode.type = .bool)
    (typed : ExpressionHasType source context condition conditionNode.type)
    (conditionSyntax : expressionSyntax condition)
    (thenSyntax : GenericImperativeMatch.Syntax source expressionSyntax context (.statements false left) expected)
    (elseSyntax : GenericImperativeMatch.Syntax source expressionSyntax context (.statements false right) expected)
    (thenStops : GenericLexicalStatements.Stopped source left)
    (elseStops : GenericLexicalStatements.Stopped source right) :
    GenericImperativeMatch.Syntax source expressionSyntax context (.statements mode (id :: rest)) expected :=
  .terminalIf unique found form annotation conditionFound conditionType typed conditionSyntax thenSyntax elseSyntax thenStops elseStops

/-- Reachable nil remains restricted; terminality cannot authenticate an empty list. -/
theorem reachable_nil_nonunit (nonunit : expected ≠ .unit) :
    ¬ GenericImperativeMatch.Syntax source expressionSyntax context (.statements true []) expected := by
  intro tree
  cases tree with
  | body lexical => cases lexical with
    | nil allowed => rcases allowed with impossible | unit; cases impossible; exact nonunit unit

theorem no_empty_stopped : ¬ GenericLexicalStatements.Stopped source [] := by
  rintro ⟨origin, summary, identity, stops⟩
  exact stops.nonempty rfl

/-- Source transport preserves the actual issuing source and callback equation.
It does not assume an arbitrary source-dependent policy accepts the view. -/
theorem original_suffix_transport {origin : TypedSource} {scope : SourceCoreLocalCell.Scope} {type : Ty} {code : Expr}
    (identity : GenericLexicalStatements.StatementSourceIdentity origin source)
    (issued : GenericLexicalStatements.IssuedSuffix origin scope mode rest type code) :
    GenericLexicalStatements.IssuedSuffix source scope mode rest type code :=
  issued.transport identity
/-- No-default exhaustiveness remains typed and pointwise; it does not
supply the universal stopping certificate used by enclosing block/if heads. -/
theorem no_default_match_has_no_stopping_head {resolution : MatchResolution} {summary : ControlSummary}
    (found : source.lookupStatement? id = some node) (form : node.form = .matchWith resolution)
    (absent : resolution.defaultBody = none) :
    ¬ ReachableStatementContinuations.StoppingStatement source id summary := by
  have shape : ∀ actual, source.lookupStatement? id = some actual →
      actual.form = .matchWith resolution := by
    intro actual actualFound
    have same := Option.some.inj (actualFound.symm.trans found)
    exact same ▸ form
  intro receipt
  cases receipt <;> have actualForm := shape _ (by assumption) <;> simp_all

end Syntax

section Extraction
open GenericImperativeMatch
variable {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {values : SourceCoreCompatibleValues.Context} {source : TypedSource} {expressionSyntax : ExpressionId → Prop}
  {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {reasonAt : ExpressionId → Word} {policy : SourceCoreLoops.Policy}
  {matchCompilation : SourceCoreCompatibleDataMatches.Context}
  {administrative : Core.Context} {definitions : DataEnvironment}
  {invalidProjection : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Word}
  {invalidOperand : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Solcore.Syntax.ValueAssignOp → Word}
  {invalidUnary : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Word}
  {missingDefault : SourceCoreElaboration.ErrorSite → Resolved.LocalId → TypeSystem.Ty → Word}
theorem accepted_terminal_block
    (matchPolicy : policy.lowerMatch = some (SourceCoreCompatibleDataMatches.lowerWithReasons matchCompilation))
    (matchValues : matchCompilation.values = values) (matchDefinitions : matchCompilation.definitions = definitions)
    (matchAllocator : matchCompilation.sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator frame globals
      (layouts.allocatorAt owner active onError)))
    (matchChildStatic : MatchChildStatic matchCompilation source certificates definitions administrative)
    (readPolicy : policy.readStatement = SourceCoreCompatibleDataExpressions.readStatement values.checked)
    (binderPolicy : ∀ scope binder, binder.scheme.quantified = [] →
      policy.lowerBinder source scope binder = SourceCoreCompatibleDataExpressions.lowerBinder values.checked source scope binder)
    (allocationPolicy : policy.sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator frame globals
      (layouts.allocatorAt owner active onError)))
    (expressions : ∀ sourceContext, sourceContext.typeVariables = [] → sourceContext.residualTypeVariables = false →
      sourceContext.signatures = values.checked.signatures →
      ∀ {scope fuel id node lowered}, CompatibleExpressionReads.ScopeDeclarations source scope sourceContext → expressionSyntax id →
      source.lookupExpression? id = some node → ExpressionHasType source sourceContext id node.type →
      policy.lowerExpression fuel source scope id reasonAt = .ok lowered →
      certificates sourceContext scope id lowered)
    (assignments : CompatibleAssignmentStatements.AssignmentPolicy policy values invalidProjection invalidOperand missingDefault)
    (unaryPolicy : CompatibleBitNotStatements.Policy policy values invalidProjection invalidUnary missingDefault)
    (unique : NodeOccurrencesUnique source)
    (assignmentExpressions : ∀ sourceContext scope fuel id lowered,
      sourceContext.typeVariables = [] → sourceContext.residualTypeVariables = false →
      sourceContext.signatures = values.checked.signatures →
      CompatibleExpressionReads.ScopeDeclarations source scope sourceContext →
      expressionSyntax id → ∀ node, source.lookupExpression? id = some node →
      ExpressionHasType source sourceContext id node.type →
      policy.lowerExpression fuel source scope id reasonAt = .ok lowered →
        certificates sourceContext scope id lowered ∧
        HasType (SourceCoreLocalCell.coreContext scope ++ administrative) lowered.expression
          (LanguageResult.resultType lowered.type) definitions)
    {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope} {mode : Bool} {id : StatementId}
    {node : StatementNode} {statements rest : List StatementId} {expected : TypeSystem.Ty}
    (exactUnique : NodeOccurrencesUnique source)
    (found : source.lookupStatement? id = some node) (form : node.form = .block statements)
    (annotation : node.type = expected)
    (inner : Syntax source expressionSyntax context (.statements false statements) expected)
    (stops : GenericLexicalStatements.Stopped source statements)
    (closed : context.typeVariables = []) (residual : context.residualTypeVariables = false)
    (sourceSignatures : context.signatures = values.checked.signatures)
    (declarations : CompatibleExpressionReads.ScopeDeclarations source scope context)
    {fuel : Nat} {type : Ty} {code : Expr} {selfReason : Word} {nativeType : Ty}
    (projection : values.checked.catalog.project expected = .ok type)
    (accepted : SourceCoreLoops.lowerFlowStatementsWithPolicy policy fuel source scope (id :: rest) type reasonAt mode selfReason = .ok code)
    (nativeTyped : HasType (SourceCoreLocalCell.coreContext scope ++ administrative) code nativeType definitions) :
    Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
      context scope (.statements mode (id :: rest)) expected type code := by
  exact tree_of_typed_flow matchPolicy matchValues matchDefinitions matchAllocator matchChildStatic readPolicy binderPolicy allocationPolicy expressions assignments unaryPolicy unique
    assignmentExpressions (.terminalBlock exactUnique found form annotation inner stops) closed residual sourceSignatures declarations projection accepted nativeTyped

theorem accepted_terminal_if
    (matchPolicy : policy.lowerMatch = some (SourceCoreCompatibleDataMatches.lowerWithReasons matchCompilation))
    (matchValues : matchCompilation.values = values) (matchDefinitions : matchCompilation.definitions = definitions)
    (matchAllocator : matchCompilation.sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator frame globals
      (layouts.allocatorAt owner active onError)))
    (matchChildStatic : MatchChildStatic matchCompilation source certificates definitions administrative)
    (readPolicy : policy.readStatement = SourceCoreCompatibleDataExpressions.readStatement values.checked)
    (binderPolicy : ∀ scope binder, binder.scheme.quantified = [] →
      policy.lowerBinder source scope binder = SourceCoreCompatibleDataExpressions.lowerBinder values.checked source scope binder)
    (allocationPolicy : policy.sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator frame globals
      (layouts.allocatorAt owner active onError)))
    (expressions : ∀ sourceContext, sourceContext.typeVariables = [] → sourceContext.residualTypeVariables = false →
      sourceContext.signatures = values.checked.signatures →
      ∀ {scope fuel id node lowered}, CompatibleExpressionReads.ScopeDeclarations source scope sourceContext → expressionSyntax id →
      source.lookupExpression? id = some node → ExpressionHasType source sourceContext id node.type →
      policy.lowerExpression fuel source scope id reasonAt = .ok lowered →
      certificates sourceContext scope id lowered)
    (assignments : CompatibleAssignmentStatements.AssignmentPolicy policy values invalidProjection invalidOperand missingDefault)
    (unaryPolicy : CompatibleBitNotStatements.Policy policy values invalidProjection invalidUnary missingDefault)
    (unique : NodeOccurrencesUnique source)
    (assignmentExpressions : ∀ sourceContext scope fuel id lowered,
      sourceContext.typeVariables = [] → sourceContext.residualTypeVariables = false →
      sourceContext.signatures = values.checked.signatures →
      CompatibleExpressionReads.ScopeDeclarations source scope sourceContext →
      expressionSyntax id → ∀ node, source.lookupExpression? id = some node →
      ExpressionHasType source sourceContext id node.type →
      policy.lowerExpression fuel source scope id reasonAt = .ok lowered →
        certificates sourceContext scope id lowered ∧
        HasType (SourceCoreLocalCell.coreContext scope ++ administrative) lowered.expression
          (LanguageResult.resultType lowered.type) definitions)
    {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope} {mode : Bool} {id : StatementId}
    {node : StatementNode} {condition : ExpressionId} {conditionNode : ExpressionNode}
    {thenBody elseBody rest : List StatementId} {expected : TypeSystem.Ty}
    (exactUnique : NodeOccurrencesUnique source)
    (found : source.lookupStatement? id = some node) (form : node.form = .ifThen condition thenBody (some elseBody))
    (annotation : node.type = expected)
    (conditionFound : source.lookupExpression? condition = some conditionNode)
    (conditionType : conditionNode.type = .bool)
    (typed : ExpressionHasType source context condition conditionNode.type)
    (conditionSyntax : expressionSyntax condition)
    (thenSyntax : Syntax source expressionSyntax context (.statements false thenBody) expected)
    (elseSyntax : Syntax source expressionSyntax context (.statements false elseBody) expected)
    (thenStops : GenericLexicalStatements.Stopped source thenBody)
    (elseStops : GenericLexicalStatements.Stopped source elseBody)
    (closed : context.typeVariables = []) (residual : context.residualTypeVariables = false)
    (sourceSignatures : context.signatures = values.checked.signatures)
    (declarations : CompatibleExpressionReads.ScopeDeclarations source scope context)
    {fuel : Nat} {type : Ty} {code : Expr} {selfReason : Word} {nativeType : Ty}
    (projection : values.checked.catalog.project expected = .ok type)
    (accepted : SourceCoreLoops.lowerFlowStatementsWithPolicy policy fuel source scope (id :: rest) type reasonAt mode selfReason = .ok code)
    (nativeTyped : HasType (SourceCoreLocalCell.coreContext scope ++ administrative) code nativeType definitions) :
    Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
      context scope (.statements mode (id :: rest)) expected type code := by
  exact tree_of_typed_flow matchPolicy matchValues matchDefinitions matchAllocator matchChildStatic readPolicy binderPolicy allocationPolicy expressions assignments unaryPolicy unique
    assignmentExpressions (.terminalIf exactUnique found form annotation conditionFound conditionType typed conditionSyntax thenSyntax elseSyntax thenStops elseStops) closed residual sourceSignatures declarations projection accepted nativeTyped
end Extraction

section LedgerConsumers
open GenericImperativeMatch
variable {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {values : ValuesContext} {source : TypedSource} {expressionSyntax : ExpressionId → Prop}
  {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {definitions : DataEnvironment} {administrative : Core.Context}
  {diagnosticPolicy : AssignmentDiagnosticPolicy} {registry : SourceCoreRawMetadata.Registry}
  {faults : FunctionCalls.FaultRep} {solved : List SolvedRequirement} {evidence : Dynamic.EvidenceEnvironment}
  {context : SourceSemantics.Context} {scope : Scope} {mode : Bool} {id : StatementId} {node : StatementNode}
  {rest statements : List StatementId} {expected : TypeSystem.Ty} {type : Ty} {innerCode suffix : Expr}

/-- Ready is reconstructed from the reached inner ledger alone. -/
theorem terminal_block_ready
    (unique : NodeOccurrencesUnique source)
    (found : source.lookupStatement? id = some node) (form : node.form = .block statements)
    (inner : Tree layouts owner active frame globals onError values source expressionSyntax certificates
      definitions administrative context scope (.statements false statements) expected type innerCode)
    (stops : GenericLexicalStatements.Stopped source statements)
    (issued : GenericLexicalStatements.IssuedSuffix source scope mode rest type suffix)
    (innerErrors : Tree.ErrorsFor diagnosticPolicy registry faults inner)
    (innerLedger : Tree.SiteLedgersFor diagnosticPolicy solved registry faults innerErrors)
    (valid : CompatibleExpressionLiterals.ContextValid solved context evidence)
    (signatures : context.signatures = values.checked.signatures) :
    Tree.ReadyFor diagnosticPolicy registry faults (.terminalBlock unique found form inner stops issued) := by
  exact Tree.SiteLedgersFor.ready
    (Tree.SiteLedgersFor.terminalBlock (unique := unique) (found := found) (form := form)
      (stops := stops) (issued := issued) innerLedger) valid signatures

/-- Both reached branches keep their own ledger; no suffix ledger is requested. -/
theorem terminal_if_ready {condition : ExpressionId} {conditionNode : ExpressionNode}
    {thenBody elseBody : List StatementId} {conditionCode thenCode elseCode : Expr}
    (unique : NodeOccurrencesUnique source)
    (found : source.lookupStatement? id = some node)
    (form : node.form = .ifThen condition thenBody (some elseBody))
    (conditionFound : source.lookupExpression? condition = some conditionNode)
    (conditionType : conditionNode.type = .bool)
    (conditionTree : certificates context scope condition ⟨.bool, conditionCode⟩)
    (thenTree : Tree layouts owner active frame globals onError values source expressionSyntax certificates
      definitions administrative context scope (.statements false thenBody) expected type thenCode)
    (elseTree : Tree layouts owner active frame globals onError values source expressionSyntax certificates
      definitions administrative context scope (.statements false elseBody) expected type elseCode)
    (thenStops : GenericLexicalStatements.Stopped source thenBody)
    (elseStops : GenericLexicalStatements.Stopped source elseBody)
    (issued : GenericLexicalStatements.IssuedSuffix source scope mode rest type suffix)
    (thenErrors : Tree.ErrorsFor diagnosticPolicy registry faults thenTree)
    (elseErrors : Tree.ErrorsFor diagnosticPolicy registry faults elseTree)
    (thenLedger : Tree.SiteLedgersFor diagnosticPolicy solved registry faults thenErrors)
    (elseLedger : Tree.SiteLedgersFor diagnosticPolicy solved registry faults elseErrors)
    (valid : CompatibleExpressionLiterals.ContextValid solved context evidence)
    (signatures : context.signatures = values.checked.signatures) :
    Tree.ReadyFor diagnosticPolicy registry faults
      (.terminalIf unique found form conditionFound conditionType conditionTree thenTree elseTree thenStops elseStops issued) := by
  exact Tree.SiteLedgersFor.ready
    (Tree.SiteLedgersFor.terminalIf (unique := unique) (found := found) (form := form)
      (conditionFound := conditionFound) (conditionType := conditionType) (conditionTree := conditionTree)
      (thenStops := thenStops) (elseStops := elseStops) (issued := issued) thenLedger elseLedger) valid signatures
end LedgerConsumers

section CompilerConsumers
variable {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frameLayout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {readFuel : Nat} {values : SourceCoreCompatibleValues.Context}
  {function : Dynamic.Closure} {context : SourceSemantics.Context} {solved : List SolvedRequirement}
  {reasonAt : ExpressionId → Word} {scope : SourceCoreLocalCell.Scope} {type : Ty}
  {administrative : Core.Context}
  {policy : SourceCoreLoops.Policy} {fuel : Nat} {fellThrough escaped : Word} {code : Expr}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient)
  {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends values.registry registry)
  (definitions : layouts.definitions = ambient.definitions)
  (registered : frameLayout.Registered ambient.definitions)
  (catalogValid : SignatureCatalogWellFormed values.checked.signatures)
  (program : SourceSemantics.Program)
  (contextValid : CompatibleExpressionLiterals.ContextValid solved context function.evidence)
  (unique : NodeOccurrencesUnique function.source) {faults : FunctionCalls.FaultRep}
  (escapedFault : faults .controlEscapedFunction escaped)
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))
  (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((reasonAt id).add tag))

  {identities : Dynamic.Value → Word → Prop}
  (faithful : DataEquality.IdentityFaithful identities)
  (functionLeaves : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)
  (functionTypes : FunctionRuntimeViews functions)

include definitions registered catalogValid escapedFault extension faithful functionLeaves functionTypes contextValid unique uninitialized missing in
theorem actual_compiler_body_preserves
    (accepted : SourceCoreLoops.lowerStatementsWithPolicy policy fuel function.source scope
      function.body type reasonAt fellThrough escaped = .ok code)
    (projection : values.checked.catalog.project function.resultType = .ok type)
    {flow : Expr}
    (generated : SourceCoreLoops.lowerFlowStatementsWithPolicy policy fuel function.source scope
      function.body type reasonAt true escaped = .ok flow)
    (tree : BuiltinImperativeMatch.Tree layouts owner active frameLayout globals onError readFuel
      values function.source solved reasonAt ambient.definitions administrative
      context scope (.statements true function.body) function.resultType type flow)
    (errors : GenericImperativeMatch.Tree.Ready registry faults tree)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {outcome : Dynamic.ExpressionOutcome}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    {contextLocation : Location} {native : SourceCoreCallableIndexedFrames.Frame}
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frameLayout.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frameLayout native))
    (unmapped : contextLocation ∉ mapping)
    (trace : FunctionCallBody.Trace program function context environment before outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (code.rename ξ) value finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld function.resultType type faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      TypedMixedNamedBody.ReachedExit values.checked ambient.definitions finalMap finalWorld administrative program function
        context scope environment before after outcome := by
  let certificate := of_extracted accepted projection generated tree
  exact certificate.preserves functions extension definitions registered catalogValid program
    contextValid unique escapedFault uninitialized missing faithful functionLeaves functionTypes
    errors environments heaps locals agrees actualTyped reference read unmapped trace

include definitions registered catalogValid escapedFault extension faithful functionLeaves functionTypes contextValid unique uninitialized missing in
theorem actual_compiler_body_reflects
    (accepted : SourceCoreLoops.lowerStatementsWithPolicy policy fuel function.source scope
      function.body type reasonAt fellThrough escaped = .ok code)
    (projection : values.checked.catalog.project function.resultType = .ok type)
    {flow : Expr}
    (generated : SourceCoreLoops.lowerFlowStatementsWithPolicy policy fuel function.source scope
      function.body type reasonAt true escaped = .ok flow)
    (tree : BuiltinImperativeMatch.Tree layouts owner active frameLayout globals onError readFuel
      values function.source solved reasonAt ambient.definitions administrative
      context scope (.statements true function.body) function.resultType type flow)
    (errors : GenericImperativeMatch.Tree.Ready registry faults tree)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
    {store finalStore : Store} {ξ : Renaming} {value : Value}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    {contextLocation : Location} {native : SourceCoreCallableIndexedFrames.Frame}
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frameLayout.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frameLayout native))
    (unmapped : contextLocation ∉ mapping)
    (evaluated : Evaluates actual store (code.rename ξ) value finalStore) :
    ∃ outcome after finalMap finalWorld,
      FunctionCallBody.Trace program function context environment before outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld function.resultType type faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      TypedMixedNamedBody.ReachedExit values.checked ambient.definitions finalMap finalWorld administrative program function
        context scope environment before after outcome := by
  let certificate := of_extracted accepted projection generated tree
  exact certificate.reflects functions extension definitions registered catalogValid program
    contextValid unique escapedFault uninitialized missing faithful functionLeaves functionTypes
    errors environments heaps locals agrees actualTyped reference read unmapped evaluated
end CompilerConsumers

private def content : String := String.intercalate "\n" [
  "function both(flag: Bool) returns (Word) { if (flag) { match (1) { case 1 {} default {} } return 7; } else { match (2) { case 2 {} default {} } return 9; } }",
  "function block() returns (Word) { { match (3) { case 3 {} default {} } return 11; } }",
  "function arms(seed: Word) returns (Word) { match (seed) { case 0 { if (true) { return 13; } else { return 17; } let gap: Word; gap; } default { { return 19; } let gap: Word; gap; } } return 99; }",
  "function inFor() returns (Word) { for (; true; ) { if (true) { match (4) { case 4 {} default {} } return 23; } else { return 29; } let gap: Word; gap; } return 99; }",
  "function inWhile() returns (Word) { while (true) { { match (5) { case 5 {} default {} } return 31; } let gap: Word; gap; } return 99; }",
  "function failed(flag: Bool) returns (Word) { let prior = 37; if (flag) { match (6) { case 6 {} default {} } let gap: Word; return gap; } else { match (7) { case 7 {} default {} } return 41; } let skipped = 99; return skipped; }",
  "function unit() returns (Unit) { { match (8) { case 8 {} default {} } return; } let gap: Word; gap; }",
  "function directMatch(seed: Word) returns (Word) { match (seed) { case 0 { return 43; } default { return 47; } } }",
  "function pattern(seed: Word) returns (Word) { match ((seed, 11)) { case (0, x) { { return x; } let gap: Word; gap; } default { if (true) { return seed; } else { return 61; } let gap: Word; gap; } } return 99; }",
  "function reachable(flag: Bool) returns (Word) { if (flag) { return 53; } match (9) { case 9 {} default {} } return 59; }"
]
private def w (n : Nat) : SourceTypedRuntime.Value := .word (Word.ofNatModulo n)
private def get {α ε : Type} [Repr ε] := @SourceCoreUnifiedCorpusSupport.get α ε _
private def require := SourceCoreUnifiedCorpusSupport.assertTrue

private def inspect (compiled : SourceCoreUnifiedCompilation.Compiled) : IO Unit := do
  let prepared := compiled.indexed
  let diagnostics ← match prepared.base.diagnostics with
    | none => throw (IO.userError "reachable match integration missing diagnostics")
    | some diagnostic => pure diagnostic.program
  let diagnostics := match prepared.base.callableContext with
    | none => diagnostics
    | some native => {diagnostics with rootTable := native.diagnostics.rootTable}
  let parents ← get "reachable match integration parent contexts"
    (SourceCoreStageCodebook.prepareContexts prepared.base.sourceProgram prepared.base.plan
      (prepared.base.locals.bindings.flatMap (·.instances)))
  let mut terminalAnnotations := 0
  let mut reachableAnnotations := 0
  let mut deadSuffixes := 0
  let mut forNodes := 0
  let mut whileNodes := 0
  let mut matchNodes := 0
  let mut defaultNodes := 0
  for named in prepared.base.functions do
    let actual := (CallableIndexedNamedGeneration.representation prepared).atContext named.signature.key []
    let own ← match diagnostics.base.find? named.signature.key with
      | none => throw (IO.userError "reachable match integration missing own diagnostics")
      | some own => pure own
    let source := CallableIndexedNamedGeneration.source named
    let scope := named.inputs.reverse.map (fun binding => (binding.1.id, binding.2))
    let reasonAt := diagnostics.reasonAt named.signature.key
    let lower := SourceCoreGeneralFunctions.lowerContextualExpression prepared.base.sourceProgram actual
      prepared.base.sourceProgram.signatures prepared.base.locals parents own.assignments diagnostics
      (CallableIndexedNamedGeneration.context prepared named) prepared.base.callableContext none none
    let policy : SourceCoreLoops.Policy := {
      actual.loopsWithSourceCells actual.expressions.sourceCells named.specialized.function.solvedRequirements
        own.assignments diagnostics named.signature.key lower with
      sourceCells := actual.expressions.sourceCells
      lowerBinder := SourceCoreGeneralFunctions.contextualBinder actual prepared.base.locals named.signature.key [] }
    let statements ← get "reachable match integration actual roots"
      (source.roots.mapM (m := Except SourceCoreGeneralFunctions.Error) (fun
        | .statement id => pure id | .expression id => throw (.expectedStatementRoot id)))
    let body ← get "reachable match integration actual complete body"
      (SourceCoreLoops.lowerStatementsWithPolicy policy prepared.fuel source scope statements
        named.signature.resultType reasonAt own.fellThroughReason own.table.escapedReason)
    let same ← get "reachable match integration actual compiler body"
      (CallableIndexedNamedGeneration.bodyAction prepared named diagnostics parents own statements)
    require (body == same) "reachable match integration changed actual compiler body"
    for item in source.nodes do
      match item with
      | .statement node =>
          match node.form with
          | .block _ | .ifThen _ _ (some _) =>
              if node.type == .word then terminalAnnotations := terminalAnnotations + 1
          | .ifThen _ _ none =>
              require (node.type == .unit) "reachable one-branch annotation changed"
              reachableAnnotations := reachableAnnotations + 1
          | .forLoop _ _ _ _ => forNodes := forNodes + 1
          | .whileLoop _ _ => whileNodes := whileNodes + 1
          | .matchWith resolution =>
              matchNodes := matchNodes + 1
              if resolution.defaultBody.isSome then defaultNodes := defaultNodes + 1
              require (!(SourceCoreDataPlaces.declaredBinders source).any (fun binder => binder.id == resolution.hiddenScrutinee))
                "match hidden ID overlaps an ordinary source binder"
          | _ => pure ()
      | _ => pure ()
    match statements with
    | id :: rest =>
        let node ← match source.lookupStatement? id with
          | none => throw (IO.userError "reachable match integration root lookup missing")
          | some node => pure node
        match node.form with
        | .ifThen condition left (some right) =>
            let (_, _) ← get "reachable match integration actual statement read" (policy.readStatement source id)
            let condition ← get "reachable match integration actual condition" (lower (prepared.fuel - 1) source scope condition reasonAt)
            let leftCode ← get "reachable match integration actual left"
              (SourceCoreLoops.lowerFlowStatementsWithPolicy policy (prepared.fuel - 1) source scope left
                named.signature.resultType reasonAt false own.table.escapedReason)
            let rightCode ← get "reachable match integration actual right"
              (SourceCoreLoops.lowerFlowStatementsWithPolicy policy (prepared.fuel - 1) source scope right
                named.signature.resultType reasonAt false own.table.escapedReason)
            let suffix ← get "reachable match integration emitted suffix"
              (SourceCoreLoops.lowerFlowStatementsWithPolicy policy (prepared.fuel - 1) source scope rest
                named.signature.resultType reasonAt true own.table.escapedReason)
            let whole ← get "reachable match integration whole flow"
              (SourceCoreLoops.lowerFlowStatementsWithPolicy policy prepared.fuel source scope statements
                named.signature.resultType reasonAt true own.table.escapedReason)
            require (whole == LocalLoop.sequence named.signature.resultType
              (LocalLoop.conditional named.signature.resultType condition.expression leftCode rightCode) suffix)
              "reachable match integration did not retain original emitted suffix"
            if !rest.isEmpty then deadSuffixes := deadSuffixes + 1
        | .block inner =>
            let innerCode ← get "reachable match integration actual block child"
              (SourceCoreLoops.lowerFlowStatementsWithPolicy policy (prepared.fuel - 1) source scope inner
                named.signature.resultType reasonAt false own.table.escapedReason)
            let suffix ← get "reachable match integration emitted block suffix"
              (SourceCoreLoops.lowerFlowStatementsWithPolicy policy (prepared.fuel - 1) source scope rest
                named.signature.resultType reasonAt true own.table.escapedReason)
            let whole ← get "reachable match integration whole block flow"
              (SourceCoreLoops.lowerFlowStatementsWithPolicy policy prepared.fuel source scope statements
                named.signature.resultType reasonAt true own.table.escapedReason)
            require (whole == LocalLoop.sequence named.signature.resultType innerCode suffix)
              "reachable match integration did not retain original block suffix"
        | _ => pure ()
    | [] => pure ()
  require (terminalAnnotations >= 5 && reachableAnnotations == 1 && forNodes == 1 && whileNodes == 1 && matchNodes == 12 && defaultNodes == 12)
    s!"reachable match fixture coverage changed: {terminalAnnotations}/{reachableAnnotations}/{deadSuffixes}/{forNodes}/{whileNodes}/{matchNodes}/{defaultNodes}"

private def finish (compiled : SourceCoreUnifiedCompilation.Compiled) (name : String)
    (arguments : List SourceTypedRuntime.Value) (fuel : Nat) (initial : SourceTypedRuntime.RuntimeState) : IO SourceTypedRuntime.RunResult := do
  let first ← SourceCoreUnifiedCorpusSupport.execute compiled name arguments fuel initial
  pure (← get "reachable match integration public resume" (first.resume 300000)).observation

def run : IO Unit := do
  let compiled ← SourceCoreUnifiedCorpusSupport.prepare "reachable match integration" content
    ["both", "block", "arms", "inFor", "inWhile", "failed", "unit", "directMatch", "pattern", "reachable"]
  inspect compiled
  let initial : SourceTypedRuntime.RuntimeState := {heap := [⟨.word, some (w 821)⟩]}
  let successes : List (String × List SourceTypedRuntime.Value × SourceTypedRuntime.Value × List (TypeSystem.Ty × Option SourceTypedRuntime.Value)) := [
    ("both", [.bool true], w 7, [(.bool, some (.bool true)), (.word, some (w 1))]),
    ("both", [.bool false], w 9, [(.bool, some (.bool false)), (.word, some (w 2))]),
    ("block", [], w 11, [(.word, some (w 3))]),
    ("arms", [w 0], w 13, [(.word, some (w 0)), (.word, some (w 0))]),
    ("arms", [w 1], w 19, [(.word, some (w 1)), (.word, some (w 1))]),
    ("inFor", [], w 23, [(.word, some (w 4))]),
    ("inWhile", [], w 31, [(.word, some (w 5))]),
    ("failed", [.bool false], w 41, [(.bool, some (.bool false)), (.word, some (w 37)), (.word, some (w 7))]),
    ("unit", [], .unit, [(.word, some (w 8))]),
    ("directMatch", [w 0], w 43, [(.word, some (w 0)), (.word, some (w 0))]),
    ("directMatch", [w 1], w 47, [(.word, some (w 1)), (.word, some (w 1))]),
    ("pattern", [w 0], w 11, [(.word, some (w 0)), (.product .word .word, some (.product (w 0) (w 11))), (.word, some (w 11))]),
    ("pattern", [w 2], w 2, [(.word, some (w 2)), (.product .word .word, some (.product (w 2) (w 11)))]),
    ("reachable", [.bool true], w 53, [(.bool, some (.bool true))]),
    ("reachable", [.bool false], w 59, [(.bool, some (.bool false)), (.word, some (w 9))])]
  let baselines ← successes.mapM (fun test => finish compiled test.1 test.2.1 300000 initial)
  let failure ← finish compiled "failed" [.bool true] 300000 initial
  for fuel in [0, 31, 300000] do
    for ((name, arguments, expected, expectedCells), baseline) in successes.zip baselines do
      let observed ← finish compiled name arguments fuel initial
      require (reprStr observed == reprStr baseline) s!"reachable match integration full resume changed {name}"
      match observed with
      | .done result final =>
          require (reprStr result == reprStr expected) s!"reachable match integration result changed {name}"
          require (reprStr final.heap == reprStr (initial.heap ++ expectedCells.map (fun (type, value) => ⟨type, value⟩)))
            s!"reachable match integration ordered heap/dead suffix changed {name}"
      | other => throw (IO.userError s!"reachable match integration expected done {name}: {reprStr other}")
    let observed ← finish compiled "failed" [.bool true] fuel initial
    require (reprStr observed == reprStr failure) "reachable match integration full fault resume changed"
    match observed with
    | .fault (.uninitializedLocal _) final =>
        require (reprStr final.heap == reprStr (initial.heap ++ [⟨.bool, some (.bool true)⟩, ⟨.word, some (w 37)⟩, ⟨.word, some (w 6)⟩, ⟨.word, none⟩]))
          "reachable match integration fault executed a dead suffix or changed its prefix"
    | other => throw (IO.userError s!"reachable match integration expected head fault: {reprStr other}")
  IO.println "reachable match integration: same recursive match/for/while grammar, non-Unit terminal annotations, source stops, original native child, emitted dead suffix, ordered full heaps and public resume GREEN"


end Tests.SourceCoreReachableImperativeMatchStatements
end

section
-- leanmerge: from Solcore.Test.SourceCoreReachableLexicalStatements
/-! The existing lexical Tree admits terminal non-Unit block/if annotations.
Its stopped suffix is still the exact issued code, while source and original
native witnesses show that it is not executed. Concrete final consumers close
expression meaning using the existing named/Builtin family. The independent
source Syntax receipt and compiler acceptance remain separate; whole for/match
source-syntax extraction is a later unit. -/
#check_failure Solcore.Frontend.SourceTypedRuntime.run
set_option autoImplicit false
namespace Tests.SourceCoreReachableLexicalStatements
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open GeneralHeap ReadOnly CompatiblePayload CoreProof CallableAncestryPairedLookup
open CallableIndexedHistory SourceCoreCallableIndexedFrames RecursiveNamedCatalog

section Syntax
variable {source : TypedSource} {context : SourceSemantics.Context} {expressionSyntax : ExpressionId → Prop}
  {mode : Bool} {id : StatementId} {node : StatementNode} {rest left right : List StatementId}
  {expected : TypeSystem.Ty} {condition : ExpressionId} {conditionNode : ExpressionNode}

theorem actual_nonunit_block_syntax
    (unique : NodeOccurrencesUnique source) (found : source.lookupStatement? id = some node)
    (form : node.form = .block left) (annotation : node.type = expected)
    (inner : GenericLexicalStatements.Syntax source expressionSyntax context false left expected)
    (stops : GenericLexicalStatements.Stopped source left) :
    GenericLexicalStatements.Syntax source expressionSyntax context mode (id :: rest) expected :=
  .terminalBlock unique found form annotation inner stops

theorem actual_nonunit_if_syntax
    (unique : NodeOccurrencesUnique source) (found : source.lookupStatement? id = some node)
    (form : node.form = .ifThen condition left (some right)) (annotation : node.type = expected)
    (conditionFound : source.lookupExpression? condition = some conditionNode)
    (conditionType : conditionNode.type = .bool)
    (typed : ExpressionHasType source context condition conditionNode.type)
    (conditionSyntax : expressionSyntax condition)
    (thenSyntax : GenericLexicalStatements.Syntax source expressionSyntax context false left expected)
    (elseSyntax : GenericLexicalStatements.Syntax source expressionSyntax context false right expected)
    (thenStops : GenericLexicalStatements.Stopped source left)
    (elseStops : GenericLexicalStatements.Stopped source right) :
    GenericLexicalStatements.Syntax source expressionSyntax context mode (id :: rest) expected :=
  .terminalIf unique found form annotation conditionFound conditionType typed conditionSyntax thenSyntax elseSyntax thenStops elseStops

/-- Reachable nil remains restricted; terminality cannot authenticate an empty list. -/
theorem reachable_nil_nonunit (nonunit : expected ≠ .unit) :
    ¬ GenericLexicalStatements.Syntax source expressionSyntax context true [] expected := by
  intro tree
  cases tree with
  | nil allowed => rcases allowed with impossible | unit; cases impossible; exact nonunit unit

theorem no_empty_stopped : ¬ GenericLexicalStatements.Stopped source [] := by
  rintro ⟨origin, summary, identity, stops⟩
  exact stops.nonempty rfl

/-- Source transport preserves the actual issuing source and callback equation.
It does not assume an arbitrary source-dependent policy accepts the view. -/
theorem original_suffix_transport {origin : TypedSource} {scope : SourceCoreLocalCell.Scope} {type : Ty} {code : Expr}
    (identity : GenericLexicalStatements.StatementSourceIdentity origin source)
    (issued : GenericLexicalStatements.IssuedSuffix origin scope mode rest type code) :
    GenericLexicalStatements.IssuedSuffix source scope mode rest type code :=
  issued.transport identity
end Syntax


section Extraction
open GenericLexicalStatements (Tree Syntax Stopped)
variable {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {values : ValuesContext} {source : TypedSource}
  {expressionSyntax : ExpressionId → Prop}
  {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {reasonAt : ExpressionId → Word} {policy : SourceCoreLoops.Policy}

theorem accepted_terminal_block (residualMode : Bool)
    (readPolicy : policy.readStatement = SourceCoreCompatibleDataExpressions.readStatement values.checked)
    (binderPolicy : ∀ scope binder, binder.scheme.quantified = [] →
      policy.lowerBinder source scope binder = SourceCoreCompatibleDataExpressions.lowerBinder values.checked source scope binder)
    (allocationPolicy : policy.sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator frame globals
      (layouts.allocatorAt owner active onError)))
    (extractExpressions : ∀ sourceContext, sourceContext.typeVariables = [] → sourceContext.residualTypeVariables = residualMode →
      sourceContext.signatures = values.checked.signatures →
      ∀ {scope fuel id node lowered}, CompatibleExpressionReads.ScopeDeclarations source scope sourceContext → expressionSyntax id →
      source.lookupExpression? id = some node → ExpressionHasType source sourceContext id node.type →
      policy.lowerExpression fuel source scope id reasonAt = .ok lowered →
      certificates sourceContext scope id lowered)
    {context : SourceSemantics.Context} {scope : Scope} {mode : Bool} {id : StatementId} {node : StatementNode} {statements rest : List StatementId} {expected : TypeSystem.Ty}
    (unique : NodeOccurrencesUnique source)
    (found : source.lookupStatement? id = some node) (form : node.form = .block statements)
    (annotation : node.type = expected)
    (inner : Syntax source expressionSyntax context false statements expected)
    (stops : Stopped source statements)
    (closed : context.typeVariables = []) (residual : context.residualTypeVariables = residualMode)
    (sourceSignatures : context.signatures = values.checked.signatures)
    (declarations : CompatibleExpressionReads.ScopeDeclarations source scope context)
    {fuel : Nat} {type : Ty} {code : Expr} {selfReason : Word}
    (projection : values.checked.catalog.project expected = .ok type)
    (accepted : SourceCoreLoops.lowerFlowStatementsWithPolicy policy fuel source scope (id :: rest) type reasonAt mode selfReason = .ok code) :
    Tree layouts owner active frame globals onError values source certificates
      context scope mode (id :: rest) expected type code := by
  exact GenericLexicalStatements.tree_of_flow_with_residual residualMode readPolicy binderPolicy allocationPolicy
    extractExpressions (.terminalBlock unique found form annotation inner stops) closed residual sourceSignatures declarations projection accepted
end Extraction

section Concrete
variable {checked : Checked} {base : Base checked}
  {prepared : SourceCoreCallableIndexedAncestry.Prepared base} {values : ValuesContext}
  {ambient : AmbientDefinitions values.checked.catalog.definitions} {program : SourceSemantics.Program}
  {body : BuiltinNamedCalls.Body prepared values ambient.definitions program} {locations : Locations} {capturePrefix : Nat}
  {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {compilation : SourceCoreFunctions.Context} {fuel : Nat} {source : TypedSource}
  {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word}
  (functions : FunctionModel values.checked.catalog ambient)
  (definitions : layouts.definitions = ambient.definitions) (registered : frame.Registered ambient.definitions)
  {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends values.registry registry)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)
  (runtimeViews : FunctionRuntimeViews functions) (evidence : Dynamic.EvidenceEnvironment)
  (unique : NodeOccurrencesUnique source)
  (owners : (program.functions.map (fun definition => definition.body.owner)).Nodup)
  {faults : FunctionCalls.FaultRep}
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))
  (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((reasonAt id).add tag))
  (bodyUninitialized : ∀ id location, faults (.uninitializedLocation location) (body.reasonAt id))
  (bodyMissing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((body.reasonAt id).add tag))

include definitions registered extension faithful observations runtimeViews unique owners uninitialized missing bodyUninitialized bodyMissing in
theorem concrete_preserves_at (budget size : Nat) (bounded : size ≤ budget)
    {context : SourceSemantics.Context} {scope : Scope} {mode : Bool}
    {statements : List StatementId} {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (tree : GenericLexicalStatements.Tree layouts owner active frame globals onError values source
      (fun context => CompatibleExpressionCalls.Tree (RecursiveNamedCatalog.Head [Header.of_body body] compilation source context)
        fuel values source context solved reasonAt) context scope mode statements expected type code) :
    RecursiveNamedLexicalContracts.PreservesAt functions program evidence
      (entry := protectedEntry [Header.of_body body] locations capturePrefix compilation.administrativePrefix)
      (source := source) (context := context) (registry := registry) (faults := faults)
      (solved := solved) (frameLayout := frame) (globals := globals)
      size (scope := scope) mode statements expected type code := by
  intro valid mapping world administrative actualContext environment canonical actual before after store ξ contextLocation native outcome finalContext
    environments heaps locals agrees actualTyped reference read unmapped installed trace
  apply RecursiveNamedLexicalTreeBounds.preserves_at functions definitions registered program evidence
    entry_transport entry_binds budget size bounded ?_ tree valid unique
    environments heaps locals agrees actualTyped reference read unmapped installed trace
  intro child within context valid
  exact SourceCoreRecursiveNamedExpressionTreeBounds.concrete_preserves_at
    functions extension body bodyUninitialized bodyMissing faithful observations runtimeViews
    valid unique owners uninitialized missing budget child within

include definitions registered extension faithful observations runtimeViews uninitialized missing bodyUninitialized bodyMissing in
theorem concrete_reflects_at (budget size : Nat) (bounded : size ≤ budget)
    {context : SourceSemantics.Context} {scope : Scope} {mode : Bool}
    {statements : List StatementId} {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (tree : GenericLexicalStatements.Tree layouts owner active frame globals onError values source
      (fun context => CompatibleExpressionCalls.Tree (RecursiveNamedCatalog.Head [Header.of_body body] compilation source context)
        fuel values source context solved reasonAt) context scope mode statements expected type code) :
    RecursiveNamedLexicalContracts.ReflectsAt functions program evidence
      (entry := protectedEntry [Header.of_body body] locations capturePrefix compilation.administrativePrefix)
      (source := source) (context := context) (registry := registry) (faults := faults)
      (solved := solved) (frameLayout := frame) (globals := globals)
      size (scope := scope) mode statements expected type code := by
  intro valid mapping world administrative actualContext environment canonical actual before store finalStore ξ contextLocation native value
    environments heaps locals agrees actualTyped reference read unmapped installed evaluated
  apply RecursiveNamedLexicalTreeBounds.reflects_at functions definitions registered program evidence
    entry_transport entry_binds budget size bounded ?_ tree valid
    environments heaps locals agrees actualTyped reference read unmapped installed evaluated
  intro child within context valid
  exact SourceCoreRecursiveNamedExpressionTreeBounds.concrete_reflects_at
    functions extension body bodyUninitialized bodyMissing faithful observations runtimeViews
    valid uninitialized missing budget child within
include definitions registered extension faithful observations runtimeViews unique owners uninitialized missing bodyUninitialized bodyMissing in
theorem terminal_block_preserves_at (budget size : Nat) (bounded : size ≤ budget)
    {context : SourceSemantics.Context} {scope : Scope} {mode : Bool} {id : StatementId} {node : StatementNode}
    {statements rest : List StatementId} {expected : TypeSystem.Ty} {type : Ty} {innerCode suffix : Expr}
    (exactUnique : NodeOccurrencesUnique source)
    (found : source.lookupStatement? id = some node) (form : node.form = .block statements)
    (inner : GenericLexicalStatements.Tree layouts owner active frame globals onError values source
      (fun context => CompatibleExpressionCalls.Tree (RecursiveNamedCatalog.Head [Header.of_body body] compilation source context)
        fuel values source context solved reasonAt) context scope false statements expected type innerCode)
    (stops : GenericLexicalStatements.Stopped source statements)
    (issued : GenericLexicalStatements.IssuedSuffix source scope mode rest type suffix) :
    RecursiveNamedLexicalContracts.PreservesAt functions program evidence
      (entry := protectedEntry [Header.of_body body] locations capturePrefix compilation.administrativePrefix)
      (source := source) (context := context) (registry := registry) (faults := faults)
      (solved := solved) (frameLayout := frame) (globals := globals)
      size (scope := scope) mode (id :: rest) expected type (LocalLoop.sequence type innerCode suffix) := by
  exact concrete_preserves_at functions definitions registered extension faithful observations runtimeViews
    evidence unique owners uninitialized missing bodyUninitialized bodyMissing budget size bounded
    (.terminalBlock exactUnique found form inner stops issued)

include definitions registered extension faithful observations runtimeViews uninitialized missing bodyUninitialized bodyMissing in
theorem terminal_block_reflects_at (budget size : Nat) (bounded : size ≤ budget)
    {context : SourceSemantics.Context} {scope : Scope} {mode : Bool} {id : StatementId} {node : StatementNode}
    {statements rest : List StatementId} {expected : TypeSystem.Ty} {type : Ty} {innerCode suffix : Expr}
    (exactUnique : NodeOccurrencesUnique source)
    (found : source.lookupStatement? id = some node) (form : node.form = .block statements)
    (inner : GenericLexicalStatements.Tree layouts owner active frame globals onError values source
      (fun context => CompatibleExpressionCalls.Tree (RecursiveNamedCatalog.Head [Header.of_body body] compilation source context)
        fuel values source context solved reasonAt) context scope false statements expected type innerCode)
    (stops : GenericLexicalStatements.Stopped source statements)
    (issued : GenericLexicalStatements.IssuedSuffix source scope mode rest type suffix) :
    RecursiveNamedLexicalContracts.ReflectsAt functions program evidence
      (entry := protectedEntry [Header.of_body body] locations capturePrefix compilation.administrativePrefix)
      (source := source) (context := context) (registry := registry) (faults := faults)
      (solved := solved) (frameLayout := frame) (globals := globals)
      size (scope := scope) mode (id :: rest) expected type (LocalLoop.sequence type innerCode suffix) := by
  exact concrete_reflects_at functions definitions registered extension faithful observations runtimeViews
    evidence uninitialized missing bodyUninitialized bodyMissing budget size bounded
    (.terminalBlock exactUnique found form inner stops issued)

include definitions registered extension faithful observations runtimeViews unique owners uninitialized missing bodyUninitialized bodyMissing in
theorem terminal_if_preserves_at (budget size : Nat) (bounded : size ≤ budget)
    {context : SourceSemantics.Context} {scope : Scope} {mode : Bool} {id : StatementId} {node : StatementNode}
    {condition : ExpressionId} {conditionNode : ExpressionNode} {thenBody elseBody rest : List StatementId} {expected : TypeSystem.Ty} {type : Ty} {conditionCode thenCode elseCode suffix : Expr}
    (exactUnique : NodeOccurrencesUnique source)
    (found : source.lookupStatement? id = some node) (form : node.form = .ifThen condition thenBody (some elseBody))
    (conditionFound : source.lookupExpression? condition = some conditionNode)
    (conditionType : conditionNode.type = .bool)
    (conditionTree : CompatibleExpressionCalls.Tree (RecursiveNamedCatalog.Head [Header.of_body body] compilation source context)
      fuel values source context solved reasonAt scope condition ⟨.bool, conditionCode⟩)
    (thenTree : GenericLexicalStatements.Tree layouts owner active frame globals onError values source
      (fun context => CompatibleExpressionCalls.Tree (RecursiveNamedCatalog.Head [Header.of_body body] compilation source context)
        fuel values source context solved reasonAt) context scope false thenBody expected type thenCode)
    (elseTree : GenericLexicalStatements.Tree layouts owner active frame globals onError values source
      (fun context => CompatibleExpressionCalls.Tree (RecursiveNamedCatalog.Head [Header.of_body body] compilation source context)
        fuel values source context solved reasonAt) context scope false elseBody expected type elseCode)
    (thenStops : GenericLexicalStatements.Stopped source thenBody)
    (elseStops : GenericLexicalStatements.Stopped source elseBody)
    (issued : GenericLexicalStatements.IssuedSuffix source scope mode rest type suffix) :
    RecursiveNamedLexicalContracts.PreservesAt functions program evidence
      (entry := protectedEntry [Header.of_body body] locations capturePrefix compilation.administrativePrefix)
      (source := source) (context := context) (registry := registry) (faults := faults)
      (solved := solved) (frameLayout := frame) (globals := globals)
      size (scope := scope) mode (id :: rest) expected type (LocalLoop.sequence type (LocalLoop.conditional type conditionCode thenCode elseCode) suffix) := by
  exact concrete_preserves_at functions definitions registered extension faithful observations runtimeViews
    evidence unique owners uninitialized missing bodyUninitialized bodyMissing budget size bounded
    (.terminalIf exactUnique found form conditionFound conditionType conditionTree thenTree elseTree thenStops elseStops issued)

include definitions registered extension faithful observations runtimeViews uninitialized missing bodyUninitialized bodyMissing in
theorem terminal_if_reflects_at (budget size : Nat) (bounded : size ≤ budget)
    {context : SourceSemantics.Context} {scope : Scope} {mode : Bool} {id : StatementId} {node : StatementNode}
    {condition : ExpressionId} {conditionNode : ExpressionNode} {thenBody elseBody rest : List StatementId} {expected : TypeSystem.Ty} {type : Ty} {conditionCode thenCode elseCode suffix : Expr}
    (exactUnique : NodeOccurrencesUnique source)
    (found : source.lookupStatement? id = some node) (form : node.form = .ifThen condition thenBody (some elseBody))
    (conditionFound : source.lookupExpression? condition = some conditionNode)
    (conditionType : conditionNode.type = .bool)
    (conditionTree : CompatibleExpressionCalls.Tree (RecursiveNamedCatalog.Head [Header.of_body body] compilation source context)
      fuel values source context solved reasonAt scope condition ⟨.bool, conditionCode⟩)
    (thenTree : GenericLexicalStatements.Tree layouts owner active frame globals onError values source
      (fun context => CompatibleExpressionCalls.Tree (RecursiveNamedCatalog.Head [Header.of_body body] compilation source context)
        fuel values source context solved reasonAt) context scope false thenBody expected type thenCode)
    (elseTree : GenericLexicalStatements.Tree layouts owner active frame globals onError values source
      (fun context => CompatibleExpressionCalls.Tree (RecursiveNamedCatalog.Head [Header.of_body body] compilation source context)
        fuel values source context solved reasonAt) context scope false elseBody expected type elseCode)
    (thenStops : GenericLexicalStatements.Stopped source thenBody)
    (elseStops : GenericLexicalStatements.Stopped source elseBody)
    (issued : GenericLexicalStatements.IssuedSuffix source scope mode rest type suffix) :
    RecursiveNamedLexicalContracts.ReflectsAt functions program evidence
      (entry := protectedEntry [Header.of_body body] locations capturePrefix compilation.administrativePrefix)
      (source := source) (context := context) (registry := registry) (faults := faults)
      (solved := solved) (frameLayout := frame) (globals := globals)
      size (scope := scope) mode (id :: rest) expected type (LocalLoop.sequence type (LocalLoop.conditional type conditionCode thenCode elseCode) suffix) := by
  exact concrete_reflects_at functions definitions registered extension faithful observations runtimeViews
    evidence uninitialized missing bodyUninitialized bodyMissing budget size bounded
    (.terminalIf exactUnique found form conditionFound conditionType conditionTree thenTree elseTree thenStops elseStops issued)

end Concrete

private def content : String := String.intercalate "\n" [
  "function both(flag: Bool) returns (Word) { if (flag) { return 7; } else { return 9; } }",
  "function block() returns (Word) { { return 11; } }",
  "function nested(flag: Bool) returns (Word) { let saved = 13; { if (flag) { return saved; } else { return 17; } } }",
  "function reachable(flag: Bool) returns (Word) { if (flag) { return 19; } return 23; }",
  "function dead(flag: Bool) returns (Word) { if (flag) { return 29; } else { return 31; } let gap: Word; gap; }",
  "function failed(flag: Bool) returns (Word) { let prior = 37; if (flag) { let gap: Word; return gap; } else { return 41; } let skipped = 99; return skipped; }",
  "function unit() returns (Unit) { { return; } let gap: Word; gap; }"
]
private def w (n : Nat) : SourceTypedRuntime.Value := .word (Word.ofNatModulo n)
private def get {α ε : Type} [Repr ε] := @SourceCoreUnifiedCorpusSupport.get α ε _
private def require := SourceCoreUnifiedCorpusSupport.assertTrue

private def inspect (compiled : SourceCoreUnifiedCompilation.Compiled) : IO Unit := do
  let prepared := compiled.indexed
  let diagnostics ← match prepared.base.diagnostics with
    | none => throw (IO.userError "reachable lexical integration missing diagnostics")
    | some diagnostic => pure diagnostic.program
  let diagnostics := match prepared.base.callableContext with
    | none => diagnostics
    | some native => {diagnostics with rootTable := native.diagnostics.rootTable}
  let parents ← get "reachable lexical integration parent contexts"
    (SourceCoreStageCodebook.prepareContexts prepared.base.sourceProgram prepared.base.plan
      (prepared.base.locals.bindings.flatMap (·.instances)))
  let mut terminalAnnotations := 0
  let mut reachableAnnotations := 0
  let mut deadSuffixes := 0
  for named in prepared.base.functions do
    let actual := (CallableIndexedNamedGeneration.representation prepared).atContext named.signature.key []
    let own ← match diagnostics.base.find? named.signature.key with
      | none => throw (IO.userError "reachable lexical integration missing own diagnostics")
      | some own => pure own
    let source := CallableIndexedNamedGeneration.source named
    let scope := named.inputs.reverse.map (fun binding => (binding.1.id, binding.2))
    let reasonAt := diagnostics.reasonAt named.signature.key
    let lower := SourceCoreGeneralFunctions.lowerContextualExpression prepared.base.sourceProgram actual
      prepared.base.sourceProgram.signatures prepared.base.locals parents own.assignments diagnostics
      (CallableIndexedNamedGeneration.context prepared named) prepared.base.callableContext none none
    let policy : SourceCoreLoops.Policy := {
      actual.loopsWithSourceCells actual.expressions.sourceCells named.specialized.function.solvedRequirements
        own.assignments diagnostics named.signature.key lower with
      sourceCells := actual.expressions.sourceCells
      lowerBinder := SourceCoreGeneralFunctions.contextualBinder actual prepared.base.locals named.signature.key [] }
    let statements ← get "reachable lexical integration actual roots"
      (source.roots.mapM (m := Except SourceCoreGeneralFunctions.Error) (fun
        | .statement id => pure id | .expression id => throw (.expectedStatementRoot id)))
    let body ← get "reachable lexical integration actual complete body"
      (SourceCoreLoops.lowerStatementsWithPolicy policy prepared.fuel source scope statements
        named.signature.resultType reasonAt own.fellThroughReason own.table.escapedReason)
    let same ← get "reachable lexical integration actual compiler body"
      (CallableIndexedNamedGeneration.bodyAction prepared named diagnostics parents own statements)
    require (body == same) "reachable lexical integration changed actual compiler body"
    for item in source.nodes do
      match item with
      | .statement node =>
          match node.form with
          | .block _ | .ifThen _ _ (some _) =>
              if node.type == .word then terminalAnnotations := terminalAnnotations + 1
          | .ifThen _ _ none =>
              require (node.type == .unit) "reachable one-branch annotation changed"
              reachableAnnotations := reachableAnnotations + 1
          | _ => pure ()
      | _ => pure ()
    match statements with
    | id :: rest =>
        let node ← match source.lookupStatement? id with
          | none => throw (IO.userError "reachable lexical integration root lookup missing")
          | some node => pure node
        match node.form with
        | .ifThen condition left (some right) =>
            let (_, _) ← get "reachable lexical integration actual statement read" (policy.readStatement source id)
            let condition ← get "reachable lexical integration actual condition" (lower (prepared.fuel - 1) source scope condition reasonAt)
            let leftCode ← get "reachable lexical integration actual left"
              (SourceCoreLoops.lowerFlowStatementsWithPolicy policy (prepared.fuel - 1) source scope left
                named.signature.resultType reasonAt false own.table.escapedReason)
            let rightCode ← get "reachable lexical integration actual right"
              (SourceCoreLoops.lowerFlowStatementsWithPolicy policy (prepared.fuel - 1) source scope right
                named.signature.resultType reasonAt false own.table.escapedReason)
            let suffix ← get "reachable lexical integration emitted suffix"
              (SourceCoreLoops.lowerFlowStatementsWithPolicy policy (prepared.fuel - 1) source scope rest
                named.signature.resultType reasonAt true own.table.escapedReason)
            let whole ← get "reachable lexical integration whole flow"
              (SourceCoreLoops.lowerFlowStatementsWithPolicy policy prepared.fuel source scope statements
                named.signature.resultType reasonAt true own.table.escapedReason)
            require (whole == LocalLoop.sequence named.signature.resultType
              (LocalLoop.conditional named.signature.resultType condition.expression leftCode rightCode) suffix)
              "reachable lexical integration did not retain original emitted suffix"
            if !rest.isEmpty then deadSuffixes := deadSuffixes + 1
        | _ => pure ()
    | [] => pure ()
  require (terminalAnnotations >= 6 && reachableAnnotations == 1 && deadSuffixes == 1)
    s!"reachable continuation fixture coverage changed: {terminalAnnotations}/{reachableAnnotations}/{deadSuffixes}"

private def finish (compiled : SourceCoreUnifiedCompilation.Compiled) (name : String)
    (arguments : List SourceTypedRuntime.Value) (fuel : Nat) (initial : SourceTypedRuntime.RuntimeState) : IO SourceTypedRuntime.RunResult := do
  let first ← SourceCoreUnifiedCorpusSupport.execute compiled name arguments fuel initial
  pure (← get "reachable lexical integration public resume" (first.resume 300000)).observation

def run : IO Unit := do
  let compiled ← SourceCoreUnifiedCorpusSupport.prepare "reachable lexical integration" content
    ["both", "block", "nested", "reachable", "dead", "failed", "unit"]
  inspect compiled
  let initial : SourceTypedRuntime.RuntimeState := {heap := [⟨.word, some (w 821)⟩]}
  let successes : List (String × List SourceTypedRuntime.Value × SourceTypedRuntime.Value × List (TypeSystem.Ty × Option SourceTypedRuntime.Value)) := [
    ("both", [.bool true], w 7, [(.bool, some (.bool true))]),
    ("both", [.bool false], w 9, [(.bool, some (.bool false))]),
    ("block", [], w 11, []),
    ("nested", [.bool true], w 13, [(.bool, some (.bool true)), (.word, some (w 13))]),
    ("nested", [.bool false], w 17, [(.bool, some (.bool false)), (.word, some (w 13))]),
    ("reachable", [.bool true], w 19, [(.bool, some (.bool true))]),
    ("reachable", [.bool false], w 23, [(.bool, some (.bool false))]),
    ("dead", [.bool true], w 29, [(.bool, some (.bool true))]),
    ("dead", [.bool false], w 31, [(.bool, some (.bool false))]),
    ("failed", [.bool false], w 41, [(.bool, some (.bool false)), (.word, some (w 37))]),
    ("unit", [], .unit, [])]
  let baselines ← successes.mapM (fun test => finish compiled test.1 test.2.1 300000 initial)
  let failure ← finish compiled "failed" [.bool true] 300000 initial
  for fuel in [0, 31, 300000] do
    for ((name, arguments, expected, expectedCells), baseline) in successes.zip baselines do
      let observed ← finish compiled name arguments fuel initial
      require (reprStr observed == reprStr baseline) s!"reachable lexical integration full resume changed {name}"
      match observed with
      | .done result final =>
          require (reprStr result == reprStr expected) s!"reachable lexical integration result changed {name}"
          require (reprStr final.heap == reprStr (initial.heap ++ expectedCells.map (fun (type, value) => ⟨type, value⟩)))
            s!"reachable lexical integration ordered heap/dead suffix changed {name}"
      | other => throw (IO.userError s!"reachable lexical integration expected done {name}: {reprStr other}")
    let observed ← finish compiled "failed" [.bool true] fuel initial
    require (reprStr observed == reprStr failure) "reachable lexical integration full fault resume changed"
    match observed with
    | .fault (.uninitializedLocal _) final =>
        require (reprStr final.heap == reprStr (initial.heap ++ [⟨.bool, some (.bool true)⟩, ⟨.word, some (w 37)⟩, ⟨.word, none⟩]))
          "reachable lexical integration fault executed a dead suffix or changed its prefix"
    | other => throw (IO.userError s!"reachable lexical integration expected head fault: {reprStr other}")
  IO.println "reachable lexical integration: actual non-Unit annotations, source stops, original native child, emitted dead suffix and full source heaps/public resume GREEN"

end Tests.SourceCoreReachableLexicalStatements
end

section
-- leanmerge: from Solcore.Test.SourceCoreReachableMatchContinuations
/-! Default-backed stopping and typed no-default stopping are tested separately.
The formal consumers retain actual statement identity, emitted suffixes and
original native child sizes. Runtime checks use the public compiler and resume
API, comparing every source cell. This foundation does not extend the existing
universal statement Tree with a no-default match case. -/
#check_failure Solcore.Frontend.SourceTypedRuntime.run
set_option autoImplicit false

namespace Tests.SourceCoreReachableMatchContinuations
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering CoreProof
open ReachableMatchContinuations

section Formal
variable {source : TypedSource} {id : StatementId} {node : StatementNode}
  {resolution : MatchResolution} {rest fallback : List StatementId}
  {program : SourceSemantics.Program} {context finalContext : SourceSemantics.Context}
  {evidence : Dynamic.EvidenceEnvironment} {environment : Dynamic.Environment}
  {before after : Dynamic.Heap} {outcome : Dynamic.ControlOutcome}

theorem default_stopped_source (mode : Bool) (unique : NodeOccurrencesUnique source)
    (found : source.lookupStatement? id = some node) (form : node.form = .matchWith resolution)
    (present : resolution.defaultBody = some fallback) (branches : BranchStops source resolution)
    (trace : ScalarStatementViews.ListExecutes mode program context evidence source environment before
      (id :: rest) finalContext outcome after) :
    Dynamic.StatementExecutes program context evidence source environment before id finalContext outcome after ∧
      Dynamic.TerminalControl outcome :=
  source_stopped_head mode unique (.of_source found form present branches) trace

theorem default_stopped_fault {reason : Dynamic.SemanticFault}
    (mode : Bool) (unique : NodeOccurrencesUnique source)
    (found : source.lookupStatement? id = some node) (form : node.form = .matchWith resolution)
    (present : resolution.defaultBody = some fallback) (branches : BranchStops source resolution)
    (trace : ScalarStatementViews.ListFaults mode program context evidence source environment before
      (id :: rest) finalContext reason after) :
    finalContext = context ∧ Dynamic.StatementFaults program context evidence source environment before id reason after :=
  source_stopped_fault mode unique (.of_source found form present branches) trace

theorem original_source_receipts {origin : TypedSource} {scope : SourceCoreLocalCell.Scope}
    {mode : Bool} {type : Core.Ty} {suffix : Expr}
    (identity : GenericLexicalStatements.StatementSourceIdentity origin source)
    (stops : DefaultStopped origin id resolution)
    (issued : GenericLexicalStatements.IssuedSuffix origin scope mode rest type suffix) :
    DefaultStopped source id resolution ∧ GenericLexicalStatements.IssuedSuffix source scope mode rest type suffix :=
  ⟨stops.transport identity, issued.transport identity⟩

theorem actual_match_issued {policy : SourceCoreLoops.Policy} {fuel : Nat} {scope : SourceCoreLoops.Scope}
    {type readType : Core.Ty} {reasonAt : ExpressionId → Word} {mode : Bool} {escaped : Word} {code : Expr}
    (read : policy.readStatement source id = .ok (node, readType)) (form : node.form = .matchWith resolution)
    (accepted : SourceCoreLoops.lowerFlowStatementsWithPolicy policy (fuel + 1) source scope (id :: rest)
      type reasonAt mode escaped = .ok code) :
    ∃ callback matched suffix,
      policy.lowerMatch = some callback ∧
      callback policy.lowerExpression
        (fun _ childSource childScope statements resultType childReasonAt childSelfReason =>
          SourceCoreLoops.lowerFlowStatementsWithPolicy policy fuel childSource childScope statements
            resultType childReasonAt false childSelfReason)
        fuel source scope id resolution type reasonAt escaped = .ok matched ∧
      ReachableStatementContinuations.Issued policy fuel source scope rest type reasonAt mode escaped suffix ∧
      code = LocalLoop.sequence type matched suffix :=
  match_issued read form accepted

theorem nonunit_typed_match_stops {control : ControlContext} {facts : StatementFacts} {expected : TypeSystem.Ty}
    (unique : NodeOccurrencesUnique source) (found : source.lookupStatement? id = some node)
    (form : node.form = .matchWith resolution) (typed : StatementHasType source control context id context facts)
    (complete : BodyCompletes expected (BodyFacts.singleton facts)) (nonunit : expected ≠ .unit) :
    MatchControlStopped source control context id node resolution facts :=
  .of_singleton_completes unique found form typed complete nonunit

theorem typed_match_terminal {control : ControlContext} {facts : StatementFacts}
    (stops : MatchControlStopped source control context id node resolution facts)
    (programWF : ProgramWellFormed program) (runtime : Dynamic.SourceRuntimeValid program context source)
    (covers : evidence.Covers context) (agrees : Dynamic.EnvironmentAgrees before context.locals environment)
    (heapTyped : Dynamic.HeapWellTyped context before)
    (trace : Dynamic.StatementExecutes program context evidence source environment before id finalContext outcome after) :
    Dynamic.TerminalControl outcome :=
  stops.terminal_at programWF runtime covers agrees heapTyped trace

theorem typed_sequence_head {control : ControlContext} {facts : StatementFacts}
    (mode : Bool) (unique : NodeOccurrencesUnique source)
    (stops : MatchControlStopped source control context id node resolution facts)
    (programWF : ProgramWellFormed program) (runtime : Dynamic.SourceRuntimeValid program context source)
    (covers : evidence.Covers context) (agrees : Dynamic.EnvironmentAgrees before context.locals environment)
    (heapTyped : Dynamic.HeapWellTyped context before)
    (trace : ScalarStatementViews.ListExecutes mode program context evidence source environment before
      (id :: rest) finalContext outcome after) :
    Dynamic.StatementExecutes program context evidence source environment before id finalContext outcome after ∧
      Dynamic.TerminalControl outcome :=
  source_typed_stopped_head mode unique stops programWF runtime covers agrees heapTyped trace

theorem typed_sequence_fault {control : ControlContext} {facts : StatementFacts} {reason : Dynamic.SemanticFault}
    (mode : Bool) (unique : NodeOccurrencesUnique source)
    (stops : MatchControlStopped source control context id node resolution facts)
    (programWF : ProgramWellFormed program) (runtime : Dynamic.SourceRuntimeValid program context source)
    (covers : evidence.Covers context) (agrees : Dynamic.EnvironmentAgrees before context.locals environment)
    (heapTyped : Dynamic.HeapWellTyped context before)
    (trace : ScalarStatementViews.ListFaults mode program context evidence source environment before
      (id :: rest) finalContext reason after) :
    finalContext = context ∧ Dynamic.StatementFaults program context evidence source environment before id reason after :=
  source_typed_stopped_fault mode unique stops programWF runtime covers agrees heapTyped trace

theorem typed_no_default_excludes_no_branch {control : ControlContext} {scrutineeType : TypeSystem.Ty}
    {caseFacts : List BodyFacts} {value : Dynamic.Value}
    (typed : TypedNoDefault source control context resolution scrutineeType caseFacts)
    (catalog : SignatureCatalogWellFormed context.signatures)
    (valueTyped : Dynamic.ValueHasType context before value scrutineeType)
    (selected : Dynamic.MatchCasesSelect context value resolution.cases resolution.defaultBody .noBranch) : False :=
  typed.no_branch catalog valueTyped selected

theorem typed_selected_arm_stops {control : ControlContext} {scrutineeType : TypeSystem.Ty}
    {caseFacts : List BodyFacts} {value : Dynamic.Value} {body : List StatementId}
    {bindings : List (TypedBinder × Dynamic.Value)} {summary : ControlSummary}
    (typed : TypedNoDefault source control context resolution scrutineeType caseFacts)
    (merged : mergeBodyControls caseFacts none = some summary) (stops : summary.fallthrough = none)
    (selected : Dynamic.MatchCasesSelect context value resolution.cases resolution.defaultBody (.arm body bindings)) :
    ∃ facts armContext bodyFinal,
      StatementsHaveType source control armContext body bodyFinal facts ∧ facts.control.fallthrough = none :=
  typed.arm_control merged stops selected

theorem no_default_not_universal (absent : resolution.defaultBody = none) :
    ¬ DefaultStopped source id resolution := by
  intro stops
  obtain ⟨fallback, present⟩ := stops.default_present
  rw [absent] at present
  cases present

theorem empty_default_not_stopped (present : resolution.defaultBody = some []) :
    ¬ BranchStops source resolution := by
  intro branches
  obtain ⟨_, _, _, stopped⟩ := branches.fallback [] present
  exact stopped.nonempty rfl

/-- Ordinary expression completion witnesses why BodyCompletes alone cannot
be used as a universal stopping cast. -/
theorem completion_can_fallthrough :
    let facts : StatementFacts := {type := .word, hasValue := true, sawReturn := false, control := .ordinary .word}
    BodyCompletes .word (BodyFacts.singleton facts) ∧ facts.control.fallthrough ≠ none := by
  simp [BodyCompletes, BodyFacts.singleton, ControlSummary.ordinary]
end Formal

theorem concrete_native_return {size : Nat} {native : Core.Environment} {initial final : Store}
    {suffix : Expr} {result : Value} (value : Word)
    (original : EvaluationSize size native initial
      (LocalLoop.sequence .word (LocalLoop.returned (.word value)) suffix) result final) :
    result = LocalLoop.returnedValue (.word value) ∧ final = initial ∧
      ∃ child, child < size ∧ EvaluationSize child native initial
        (LocalLoop.returned (.word value)) result final := by
  have head : Evaluates native initial (LocalLoop.returned (.word value)) (LocalLoop.returnedValue (.word value)) initial :=
    LocalLoop.returned_evaluates .word
  obtain ⟨child, smaller, actual, _⟩ := native_issued_stopped rfl original (by
    intro child middle result _ actual
    obtain ⟨same, _⟩ := evaluation_deterministic actual.sound head
    exact same ▸ ReachableStatementContinuations.NativeTerminal.returned (.word value))
  obtain ⟨same, storeEq⟩ := evaluation_deterministic actual.sound head
  exact ⟨same, storeEq, child, smaller, actual⟩

theorem concrete_native_fault {size : Nat} {native : Core.Environment} {initial final : Store}
    {type : Core.Ty} {suffix : Expr} {result : Value} (reason : Word)
    (original : EvaluationSize size native initial
      (LocalLoop.sequence type (LanguageResult.failure (LocalLoop.controlType type) (.word reason)) suffix) result final) :
    result = .inLeft (LocalLoop.controlType type) (.word reason) ∧ final = initial ∧
      ∃ child, child < size ∧ EvaluationSize child native initial
        (LanguageResult.failure (LocalLoop.controlType type) (.word reason)) result final := by
  have head : Evaluates native initial (LanguageResult.failure (LocalLoop.controlType type) (.word reason))
      (.inLeft (LocalLoop.controlType type) (.word reason)) initial := .inLeft .word
  obtain ⟨child, smaller, actual, _⟩ := native_issued_stopped rfl original (by
    intro child middle result _ actual
    obtain ⟨same, _⟩ := evaluation_deterministic actual.sound head
    exact same ▸ ReachableStatementContinuations.NativeTerminal.failure reason)
  obtain ⟨same, storeEq⟩ := evaluation_deterministic actual.sound head
  exact ⟨same, storeEq, child, smaller, actual⟩

private def content : String := String.intercalate "\n" [
  "enum Choice { Left(Word), Right(Word) }",
  "function direct(seed: Word) returns (Word) { match (seed) { case 0 { return 43; } default { return 47; } } }",
  "function dead(seed: Word) returns (Word) { match (seed) { case 0 { if (true) { return 13; } else { return 17; } } default { { return 19; } } } let gap: Word; gap; }",
  "function pattern(seed: Word) returns (Word) { match ((seed, 11)) { case (0, x) { { return x; } let skipped = 99; } default { if (true) { return seed; } else { return 61; } let skipped = 99; } } return 99; }",
  "function same(seed: Word) returns (Word) { match (seed) { case 0 { return 23; } case 1 { return 23; } default { return 23; } } return 99; }",
  "function reachable(seed: Word) returns (Word) { match (seed) { case 0 {} default { return 31; } } return 29; }",
  "function failed(seed: Word) returns (Word) { match (seed) { case 0 { let prior = 37; let gap: Word; return gap; } default { return 41; } } let skipped = 99; return skipped; }",
  "function scrutineeFault() returns (Word) { let gap: Word; match (gap) { case 0 { return 1; } default { return 2; } } let skipped = 99; return skipped; }",
  "function nominalLeft(value: Choice) returns (Word) { match (value) { case .Left(x) { return x; } case .Right(y) { return y; } } }",
  "function nominalRight(value: Choice) returns (Word) { match (value) { case .Left(x) { return x; } case .Right(y) { return y; } } }"
]
private def w (n : Nat) : SourceTypedRuntime.Value := .word (Word.ofNatModulo n)
private def get {α ε : Type} [Repr ε] := @SourceCoreUnifiedCorpusSupport.get α ε _
private def require := SourceCoreUnifiedCorpusSupport.assertTrue

private def inspect (compiled : SourceCoreUnifiedCompilation.Compiled) : IO Unit := do
  let prepared := compiled.indexed
  let diagnostics ← match prepared.base.diagnostics with
    | none => throw (IO.userError "reachable match continuations missing diagnostics")
    | some diagnostic => pure diagnostic.program
  let diagnostics := match prepared.base.callableContext with
    | none => diagnostics
    | some native => {diagnostics with rootTable := native.diagnostics.rootTable}
  let parents ← get "reachable match parent contexts"
    (SourceCoreStageCodebook.prepareContexts prepared.base.sourceProgram prepared.base.plan
      (prepared.base.locals.bindings.flatMap (·.instances)))
  let mut defaultNodes := 0
  let mut noDefaultNodes := 0
  let mut nilSuffixes := 0
  let mut nonemptySuffixes := 0
  for named in prepared.base.functions do
    let actual := (CallableIndexedNamedGeneration.representation prepared).atContext named.signature.key []
    let own ← match diagnostics.base.find? named.signature.key with
      | none => throw (IO.userError "reachable match own diagnostics missing")
      | some own => pure own
    let source := CallableIndexedNamedGeneration.source named
    let scope := named.inputs.reverse.map (fun binding => (binding.1.id, binding.2))
    let reasonAt := diagnostics.reasonAt named.signature.key
    let lower := SourceCoreGeneralFunctions.lowerContextualExpression prepared.base.sourceProgram actual
      prepared.base.sourceProgram.signatures prepared.base.locals parents own.assignments diagnostics
      (CallableIndexedNamedGeneration.context prepared named) prepared.base.callableContext none none
    let policy : SourceCoreLoops.Policy := {
      actual.loopsWithSourceCells actual.expressions.sourceCells named.specialized.function.solvedRequirements
        own.assignments diagnostics named.signature.key lower with
      sourceCells := actual.expressions.sourceCells
      lowerBinder := SourceCoreGeneralFunctions.contextualBinder actual prepared.base.locals named.signature.key [] }
    let statements ← get "reachable match actual roots"
      (source.roots.mapM (m := Except SourceCoreGeneralFunctions.Error) (fun
        | .statement id => pure id | .expression id => throw (.expectedStatementRoot id)))
    let body ← get "reachable match actual body"
      (SourceCoreLoops.lowerStatementsWithPolicy policy prepared.fuel source scope statements
        named.signature.resultType reasonAt own.fellThroughReason own.table.escapedReason)
    let same ← get "reachable match actual compiler body"
      (CallableIndexedNamedGeneration.bodyAction prepared named diagnostics parents own statements)
    require (body == same) "reachable match changed actual body code"
    for item in source.nodes do
      match item with
      | .statement node =>
        match node.form with
        | .matchWith resolution =>
          if resolution.defaultBody.isSome then defaultNodes := defaultNodes + 1
          else noDefaultNodes := noDefaultNodes + 1
          require (!(SourceCoreDataPlaces.declaredBinders source).any (fun binder => binder.id == resolution.hiddenScrutinee))
            "reachable match hidden scrutinee overlaps a source binder"
        | _ => pure ()
      | _ => pure ()
    match statements with
    | id :: rest =>
      let node ← match source.lookupStatement? id with
        | none => throw (IO.userError "reachable match root lookup missing")
        | some node => pure node
      match node.form with
      | .matchWith resolution =>
        let callback ← match policy.lowerMatch with
          | none => throw (IO.userError "reachable match callback missing")
          | some callback => pure callback
        let matched ← get "reachable match actual callback"
          (callback policy.lowerExpression
            (fun _ childSource childScope childStatements resultType childReasonAt escaped =>
              SourceCoreLoops.lowerFlowStatementsWithPolicy policy (prepared.fuel - 1) childSource childScope childStatements
                resultType childReasonAt false escaped)
            (prepared.fuel - 1) source scope id resolution named.signature.resultType reasonAt own.table.escapedReason)
        let suffix ← get "reachable match complete emitted suffix"
          (SourceCoreLoops.lowerFlowStatementsWithPolicy policy (prepared.fuel - 1) source scope rest
            named.signature.resultType reasonAt true own.table.escapedReason)
        let whole ← get "reachable match whole flow"
          (SourceCoreLoops.lowerFlowStatementsWithPolicy policy prepared.fuel source scope statements
            named.signature.resultType reasonAt true own.table.escapedReason)
        require (whole == LocalLoop.sequence named.signature.resultType matched suffix)
          "reachable match did not retain actual callback and full suffix"
        if rest.isEmpty then nilSuffixes := nilSuffixes + 1 else nonemptySuffixes := nonemptySuffixes + 1
      | _ => pure ()
    | [] => pure ()
  require (defaultNodes == 7 && noDefaultNodes == 2 && nilSuffixes == 3 && nonemptySuffixes == 5)
    s!"reachable match fixture coverage changed: {defaultNodes}/{noDefaultNodes}/{nilSuffixes}/{nonemptySuffixes}"

private def finish (compiled : SourceCoreUnifiedCompilation.Compiled) (name : String)
    (arguments : List SourceTypedRuntime.Value) (fuel : Nat) (initial : SourceTypedRuntime.RuntimeState) : IO SourceTypedRuntime.RunResult := do
  let first ← SourceCoreUnifiedCorpusSupport.execute compiled name arguments fuel initial
  pure (← get "reachable match public resume" (first.resume 300000)).observation

def run : IO Unit := do
  let compiled ← SourceCoreUnifiedCorpusSupport.prepare "reachable match continuations" content
    ["direct", "dead", "pattern", "same", "reachable", "failed", "scrutineeFault", "nominalLeft", "nominalRight"]
  inspect compiled
  let initial : SourceTypedRuntime.RuntimeState := {heap := [⟨.word, some (w 821)⟩]}
  let successes : List (String × List SourceTypedRuntime.Value × SourceTypedRuntime.Value × List (TypeSystem.Ty × Option SourceTypedRuntime.Value)) := [
    ("direct", [w 0], w 43, [(.word, some (w 0)), (.word, some (w 0))]),
    ("direct", [w 1], w 47, [(.word, some (w 1)), (.word, some (w 1))]),
    ("dead", [w 0], w 13, [(.word, some (w 0)), (.word, some (w 0))]),
    ("dead", [w 1], w 19, [(.word, some (w 1)), (.word, some (w 1))]),
    ("pattern", [w 0], w 11, [(.word, some (w 0)), (.product .word .word, some (.product (w 0) (w 11))), (.word, some (w 11))]),
    ("pattern", [w 2], w 2, [(.word, some (w 2)), (.product .word .word, some (.product (w 2) (w 11)))]),
    ("same", [w 0], w 23, [(.word, some (w 0)), (.word, some (w 0))]),
    ("same", [w 1], w 23, [(.word, some (w 1)), (.word, some (w 1))]),
    ("same", [w 2], w 23, [(.word, some (w 2)), (.word, some (w 2))]),
    ("reachable", [w 0], w 29, [(.word, some (w 0)), (.word, some (w 0))]),
    ("reachable", [w 1], w 31, [(.word, some (w 1)), (.word, some (w 1))]),
    ("failed", [w 1], w 41, [(.word, some (w 1)), (.word, some (w 1))])]
  let baselines ← successes.mapM (fun test => finish compiled test.1 test.2.1 300000 initial)
  for fuel in [0, 31, 300000] do
    for ((name, arguments, expected, expectedCells), baseline) in successes.zip baselines do
      let observed ← finish compiled name arguments fuel initial
      require (reprStr observed == reprStr baseline) s!"reachable match full resume changed {name}"
      match observed with
      | .done result final =>
        require (reprStr result == reprStr expected) s!"reachable match result changed {name}"
        require (reprStr final.heap == reprStr (initial.heap ++ expectedCells.map (fun (type, value) => ⟨type, value⟩)))
          s!"reachable match full heap/dead suffix changed {name}"
      | other => throw (IO.userError s!"reachable match expected done {name}: {reprStr other}")
  let failures : List (String × List SourceTypedRuntime.Value × List (TypeSystem.Ty × Option SourceTypedRuntime.Value)) := [
    ("failed", [w 0], [(.word, some (w 0)), (.word, some (w 0)), (.word, some (w 37)), (.word, none)]),
    ("scrutineeFault", [], [(.word, none)])]
  for (name, arguments, expectedCells) in failures do
    let baseline ← finish compiled name arguments 300000 initial
    for fuel in [0, 31, 300000] do
      let observed ← finish compiled name arguments fuel initial
      require (reprStr observed == reprStr baseline) s!"reachable match fault resume changed {name}"
      match observed with
      | .fault (.uninitializedLocal _) final =>
        require (reprStr final.heap == reprStr (initial.heap ++ expectedCells.map (fun (type, value) => ⟨type, value⟩)))
          s!"reachable match first fault/dead suffix changed {name}"
      | other => throw (IO.userError s!"reachable match expected fault {name}: {reprStr other}")
  let choice ← match compiled.indexed.base.sourceProgram.signatures.dataTypes.find? (·.name == "Choice") with
    | none => throw (IO.userError "reachable match Choice missing")
    | some choice => pure choice
  let sourceType := TypeSystem.Ty.nominal choice.id []
  for (name, constructor, value) in [("nominalLeft", 0, 5), ("nominalRight", 1, 7)] do
    let metadata : DataConstructorInstantiation := ⟨⟨choice.id, constructor⟩, [], [.word], sourceType⟩
    let expected : SourceTypedRuntime.Value := .constructed metadata [w value]
    let baseline ← finish compiled name [expected] 300000 initial
    for fuel in [0, 31, 300000] do
      let observed ← finish compiled name [expected] fuel initial
      require (reprStr observed == reprStr baseline) s!"reachable typed nominal resume changed {name}"
      match observed with
      | .done result final =>
        require (reprStr result == reprStr (w value)) s!"reachable typed nominal result changed {name}"
        require (reprStr final.heap == reprStr (initial.heap ++ [⟨sourceType, some expected⟩, ⟨sourceType, some expected⟩, ⟨.word, some (w value)⟩]))
          s!"reachable typed nominal full heap changed {name}"
      | other => throw (IO.userError s!"reachable typed nominal expected done {name}: {reprStr other}")
  IO.println "reachable match continuations: separate default/typed exhaustive boundaries, actual issued suffix, full source cells/fault/public resume GREEN"

end Tests.SourceCoreReachableMatchContinuations
end

section
-- leanmerge: from Solcore.Test.SourceCoreReachableStatementContinuations
/-! Terminal source fragments retain the actual non-Unit node annotations and
the compiler's emitted dead suffix. Formal consumers close concrete native
terminal heads. Runtime checks use checked source and the actual contextual
lowerer, including dead suffixes, fault prefixes and public checkpoint resume.
The existing Tree/Syntax integration remains a separate change. -/
#check_failure Solcore.Frontend.SourceTypedRuntime.run
set_option autoImplicit false

namespace Tests.SourceCoreReachableStatementContinuations
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open ReachableStatementContinuations CoreProof

section Formal
variable {source : TypedSource} {id : StatementId} {node : StatementNode} {rest left right : List StatementId}
  {condition : ExpressionId} {leftSummary rightSummary : ControlSummary}
  {program : SourceSemantics.Program} {context finalContext : SourceSemantics.Context}
  {evidence : Dynamic.EvidenceEnvironment} {environment : Dynamic.Environment} {before after : Dynamic.Heap}
  {outcome : Dynamic.ControlOutcome}

theorem actual_terminal_if (mode : Bool) (unique : NodeOccurrencesUnique source)
    (found : source.lookupStatement? id = some node)
    (form : node.form = .ifThen condition left (some right))
    (leftStops : StoppingStatements source left leftSummary)
    (rightStops : StoppingStatements source right rightSummary)
    (trace : ScalarStatementViews.ListExecutes mode program context evidence source environment before
      (id :: rest) finalContext outcome after) :
    Dynamic.StatementExecutes program context evidence source environment before id finalContext outcome after ∧
      Dynamic.TerminalControl outcome :=
  source_stopped_head mode unique (.conditional found form leftStops rightStops) trace

theorem actual_terminal_block_fault {summary : ControlSummary} {reason : Dynamic.SemanticFault}
    (mode : Bool) (unique : NodeOccurrencesUnique source)
    (found : source.lookupStatement? id = some node) (form : node.form = .block left)
    (stops : StoppingStatements source left summary)
    (trace : ScalarStatementViews.ListFaults mode program context evidence source environment before
      (id :: rest) finalContext reason after) :
    finalContext = context ∧ Dynamic.StatementFaults program context evidence source environment before id reason after :=
  source_stopped_fault mode unique (.block found form stops) trace

theorem terminal_if_issued {policy : SourceCoreLoops.Policy} {fuel : Nat} {scope : SourceCoreLoops.Scope}
    {type readType : Core.Ty} {reasonAt : ExpressionId → Word} {mode : Bool} {escaped : Word} {code : Expr}
    (read : policy.readStatement source id = .ok (node, readType))
    (form : node.form = .ifThen condition left (some right))
    (leftStops : StoppingStatements source left leftSummary)
    (rightStops : StoppingStatements source right rightSummary)
    (accepted : SourceCoreLoops.lowerFlowStatementsWithPolicy policy (fuel + 1) source scope (id :: rest)
      type reasonAt mode escaped = .ok code) :
    leftSummary.fallthrough = none ∧ rightSummary.fallthrough = none ∧
      ∃ lowered leftCode rightCode suffix,
        policy.lowerExpression fuel source scope condition reasonAt = .ok lowered ∧
        SourceCoreBasic.ensureType (.occurrence id.occurrence) .bool lowered.type = .ok () ∧
        Issued policy fuel source scope left type reasonAt false escaped leftCode ∧
        Issued policy fuel source scope right type reasonAt false escaped rightCode ∧
        Issued policy fuel source scope rest type reasonAt mode escaped suffix ∧
        code = LocalLoop.sequence type (LocalLoop.conditional type lowered.expression leftCode rightCode) suffix :=
  ⟨leftStops.no_fallthrough, rightStops.no_fallthrough, conditional_issued read form accepted⟩

/-- A reachable nil tail remains restricted in the old grammar. -/
theorem old_nil_nonunit {expected : TypeSystem.Ty} {expressionSyntax : ExpressionId → Prop}
    (nonunit : expected ≠ .unit) :
    ¬ GenericLexicalStatements.Syntax source expressionSyntax context true [] expected := by
  intro syntaxTree
  cases syntaxTree with
  | nil allowed => rcases allowed with impossible | unit; cases impossible; exact nonunit unit

theorem no_terminal_nil (summary : ControlSummary) : ¬ StoppingStatements source [] summary := by
  intro stops
  exact stops.nonempty rfl

theorem no_terminal_one_branch (found : source.lookupStatement? id = some node)
    (form : node.form = .ifThen condition left none) (summary : ControlSummary) :
    ¬ StoppingStatement source id summary := by
  have shape : ∀ actual, source.lookupStatement? id = some actual →
      actual.form = .ifThen condition left none := by
    intro actual actualFound
    have same : actual = node := Option.some.inj (actualFound.symm.trans found)
    exact same ▸ form
  intro stops
  cases stops <;> have actualForm := shape _ (by assumption) <;> simp_all
end Formal

/-- The stopping obligation is discharged by this concrete native return,
not by an input law about a runtime body. The child is the original witness. -/
theorem concrete_return_stops {size : Nat} {native : Core.Environment} {initial final : Store}
    {suffix : Expr} {result : Value} (value : Word)
    (original : EvaluationSize size native initial
      (LocalLoop.sequence .word (LocalLoop.returned (.word value)) suffix) result final) :
    result = LocalLoop.returnedValue (.word value) ∧ final = initial ∧
      ∃ child, child < size ∧ EvaluationSize child native initial
        (LocalLoop.returned (.word value)) result final := by
  have head : Evaluates native initial (LocalLoop.returned (.word value)) (LocalLoop.returnedValue (.word value)) initial :=
    LocalLoop.returned_evaluates .word
  obtain ⟨child, smaller, actual, _⟩ := native_sequence_stopped original (by
    intro child middle result _ actual
    obtain ⟨same, _⟩ := evaluation_deterministic actual.sound head
    exact same ▸ NativeTerminal.returned (.word value))
  obtain ⟨same, storeEq⟩ := evaluation_deterministic actual.sound head
  exact ⟨same, storeEq, child, smaller, actual⟩

theorem concrete_fault_stops {size : Nat} {native : Core.Environment} {initial final : Store}
    {type : Core.Ty} {suffix : Expr} {result : Value} (reason : Word)
    (original : EvaluationSize size native initial
      (LocalLoop.sequence type (LanguageResult.failure (LocalLoop.controlType type) (.word reason)) suffix) result final) :
    result = .inLeft (LocalLoop.controlType type) (.word reason) ∧ final = initial ∧
      ∃ child, child < size ∧ EvaluationSize child native initial
        (LanguageResult.failure (LocalLoop.controlType type) (.word reason)) result final := by
  have head : Evaluates native initial (LanguageResult.failure (LocalLoop.controlType type) (.word reason))
      (.inLeft (LocalLoop.controlType type) (.word reason)) initial := .inLeft .word
  obtain ⟨child, smaller, actual, _⟩ := native_sequence_stopped original (by
    intro child middle result _ actual
    obtain ⟨same, _⟩ := evaluation_deterministic actual.sound head
    exact same ▸ NativeTerminal.failure reason)
  obtain ⟨same, storeEq⟩ := evaluation_deterministic actual.sound head
  exact ⟨same, storeEq, child, smaller, actual⟩

private def content : String := String.intercalate "\n" [
  "function both(flag: Bool) returns (Word) { if (flag) { return 7; } else { return 9; } }",
  "function block() returns (Word) { { return 11; } }",
  "function nested(flag: Bool) returns (Word) { let saved = 13; { if (flag) { return saved; } else { return 17; } } }",
  "function reachable(flag: Bool) returns (Word) { if (flag) { return 19; } return 23; }",
  "function dead(flag: Bool) returns (Word) { if (flag) { return 29; } else { return 31; } let gap: Word; gap; }",
  "function failed(flag: Bool) returns (Word) { let prior = 37; if (flag) { let gap: Word; return gap; } else { return 41; } let skipped = 99; return skipped; }",
  "function unit() returns (Unit) { { return; } let gap: Word; gap; }"
]
private def w (n : Nat) : SourceTypedRuntime.Value := .word (Word.ofNatModulo n)
private def get {α ε : Type} [Repr ε] := @SourceCoreUnifiedCorpusSupport.get α ε _
private def require := SourceCoreUnifiedCorpusSupport.assertTrue

private def inspect (compiled : SourceCoreUnifiedCompilation.Compiled) : IO Unit := do
  let prepared := compiled.indexed
  let diagnostics ← match prepared.base.diagnostics with
    | none => throw (IO.userError "reachable continuations missing diagnostics")
    | some diagnostic => pure diagnostic.program
  let diagnostics := match prepared.base.callableContext with
    | none => diagnostics
    | some native => {diagnostics with rootTable := native.diagnostics.rootTable}
  let parents ← get "reachable continuations parent contexts"
    (SourceCoreStageCodebook.prepareContexts prepared.base.sourceProgram prepared.base.plan
      (prepared.base.locals.bindings.flatMap (·.instances)))
  let mut terminalAnnotations := 0
  let mut reachableAnnotations := 0
  let mut deadSuffixes := 0
  for named in prepared.base.functions do
    let actual := (CallableIndexedNamedGeneration.representation prepared).atContext named.signature.key []
    let own ← match diagnostics.base.find? named.signature.key with
      | none => throw (IO.userError "reachable continuations missing own diagnostics")
      | some own => pure own
    let source := CallableIndexedNamedGeneration.source named
    let scope := named.inputs.reverse.map (fun binding => (binding.1.id, binding.2))
    let reasonAt := diagnostics.reasonAt named.signature.key
    let lower := SourceCoreGeneralFunctions.lowerContextualExpression prepared.base.sourceProgram actual
      prepared.base.sourceProgram.signatures prepared.base.locals parents own.assignments diagnostics
      (CallableIndexedNamedGeneration.context prepared named) prepared.base.callableContext none none
    let policy : SourceCoreLoops.Policy := {
      actual.loopsWithSourceCells actual.expressions.sourceCells named.specialized.function.solvedRequirements
        own.assignments diagnostics named.signature.key lower with
      sourceCells := actual.expressions.sourceCells
      lowerBinder := SourceCoreGeneralFunctions.contextualBinder actual prepared.base.locals named.signature.key [] }
    let statements ← get "reachable continuations actual roots"
      (source.roots.mapM (m := Except SourceCoreGeneralFunctions.Error) (fun
        | .statement id => pure id | .expression id => throw (.expectedStatementRoot id)))
    let body ← get "reachable continuations actual complete body"
      (SourceCoreLoops.lowerStatementsWithPolicy policy prepared.fuel source scope statements
        named.signature.resultType reasonAt own.fellThroughReason own.table.escapedReason)
    let same ← get "reachable continuations actual compiler body"
      (CallableIndexedNamedGeneration.bodyAction prepared named diagnostics parents own statements)
    require (body == same) "reachable continuations changed actual compiler body"
    for item in source.nodes do
      match item with
      | .statement node =>
          match node.form with
          | .block _ | .ifThen _ _ (some _) =>
              if node.type == .word then terminalAnnotations := terminalAnnotations + 1
          | .ifThen _ _ none =>
              require (node.type == .unit) "reachable one-branch annotation changed"
              reachableAnnotations := reachableAnnotations + 1
          | _ => pure ()
      | _ => pure ()
    match statements with
    | id :: rest =>
        let node ← match source.lookupStatement? id with
          | none => throw (IO.userError "reachable continuations root lookup missing")
          | some node => pure node
        match node.form with
        | .ifThen condition left (some right) =>
            let (_, _) ← get "reachable continuations actual statement read" (policy.readStatement source id)
            let condition ← get "reachable continuations actual condition" (lower (prepared.fuel - 1) source scope condition reasonAt)
            let leftCode ← get "reachable continuations actual left"
              (SourceCoreLoops.lowerFlowStatementsWithPolicy policy (prepared.fuel - 1) source scope left
                named.signature.resultType reasonAt false own.table.escapedReason)
            let rightCode ← get "reachable continuations actual right"
              (SourceCoreLoops.lowerFlowStatementsWithPolicy policy (prepared.fuel - 1) source scope right
                named.signature.resultType reasonAt false own.table.escapedReason)
            let suffix ← get "reachable continuations emitted suffix"
              (SourceCoreLoops.lowerFlowStatementsWithPolicy policy (prepared.fuel - 1) source scope rest
                named.signature.resultType reasonAt true own.table.escapedReason)
            let whole ← get "reachable continuations whole flow"
              (SourceCoreLoops.lowerFlowStatementsWithPolicy policy prepared.fuel source scope statements
                named.signature.resultType reasonAt true own.table.escapedReason)
            require (whole == LocalLoop.sequence named.signature.resultType
              (LocalLoop.conditional named.signature.resultType condition.expression leftCode rightCode) suffix)
              "reachable continuations did not retain original emitted suffix"
            if !rest.isEmpty then deadSuffixes := deadSuffixes + 1
        | _ => pure ()
    | [] => pure ()
  require (terminalAnnotations >= 6 && reachableAnnotations == 1 && deadSuffixes == 1)
    s!"reachable continuation fixture coverage changed: {terminalAnnotations}/{reachableAnnotations}/{deadSuffixes}"

private def finish (compiled : SourceCoreUnifiedCompilation.Compiled) (name : String)
    (arguments : List SourceTypedRuntime.Value) (fuel : Nat) (initial : SourceTypedRuntime.RuntimeState) : IO SourceTypedRuntime.RunResult := do
  let first ← SourceCoreUnifiedCorpusSupport.execute compiled name arguments fuel initial
  pure (← get "reachable continuations public resume" (first.resume 300000)).observation

def run : IO Unit := do
  let compiled ← SourceCoreUnifiedCorpusSupport.prepare "reachable statement continuations" content
    ["both", "block", "nested", "reachable", "dead", "failed", "unit"]
  inspect compiled
  let initial : SourceTypedRuntime.RuntimeState := {heap := [⟨.word, some (w 821)⟩]}
  let successes : List (String × List SourceTypedRuntime.Value × SourceTypedRuntime.Value × List (TypeSystem.Ty × Option SourceTypedRuntime.Value)) := [
    ("both", [.bool true], w 7, [(.bool, some (.bool true))]),
    ("both", [.bool false], w 9, [(.bool, some (.bool false))]),
    ("block", [], w 11, []),
    ("nested", [.bool true], w 13, [(.bool, some (.bool true)), (.word, some (w 13))]),
    ("nested", [.bool false], w 17, [(.bool, some (.bool false)), (.word, some (w 13))]),
    ("reachable", [.bool true], w 19, [(.bool, some (.bool true))]),
    ("reachable", [.bool false], w 23, [(.bool, some (.bool false))]),
    ("dead", [.bool true], w 29, [(.bool, some (.bool true))]),
    ("dead", [.bool false], w 31, [(.bool, some (.bool false))]),
    ("failed", [.bool false], w 41, [(.bool, some (.bool false)), (.word, some (w 37))]),
    ("unit", [], .unit, [])]
  let baselines ← successes.mapM (fun test => finish compiled test.1 test.2.1 300000 initial)
  let failure ← finish compiled "failed" [.bool true] 300000 initial
  for fuel in [0, 31, 300000] do
    for ((name, arguments, expected, expectedCells), baseline) in successes.zip baselines do
      let observed ← finish compiled name arguments fuel initial
      require (reprStr observed == reprStr baseline) s!"reachable continuations full resume changed {name}"
      match observed with
      | .done result final =>
          require (reprStr result == reprStr expected) s!"reachable continuations result changed {name}"
          require (reprStr final.heap == reprStr (initial.heap ++ expectedCells.map (fun (type, value) => ⟨type, value⟩)))
            s!"reachable continuations ordered heap/dead suffix changed {name}"
      | other => throw (IO.userError s!"reachable continuations expected done {name}: {reprStr other}")
    let observed ← finish compiled "failed" [.bool true] fuel initial
    require (reprStr observed == reprStr failure) "reachable continuations full fault resume changed"
    match observed with
    | .fault (.uninitializedLocal _) final =>
        require (reprStr final.heap == reprStr (initial.heap ++ [⟨.bool, some (.bool true)⟩, ⟨.word, some (w 37)⟩, ⟨.word, none⟩]))
          "reachable continuations fault executed a dead suffix or changed its prefix"
    | other => throw (IO.userError s!"reachable continuations expected head fault: {reprStr other}")
  IO.println "reachable statement continuations: actual non-Unit annotations, source stops, original native child, emitted dead suffix and full source heaps/public resume GREEN"

end Tests.SourceCoreReachableStatementContinuations
end

section
-- leanmerge: from Solcore.Test.SourceCoreReachableTerminalMatchStatements
/-! A default-present stopping match extends the same existing static grammar.
The actual compiler emits every suffix, while only reached branches require
Trees, diagnostics and ledgers. Universal default stopping stays separate
from typed no-default stopping. Concrete Builtin body consumers close all
runtime child meaning; protected bounded catalog match closure is separate. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 65536
namespace Tests.SourceCoreReachableTerminalMatchStatements
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open GeneralHeap ReadOnly CompatiblePayload CoreProof CallableAncestryPairedLookup
open CallableIndexedHistory SourceCoreCallableIndexedFrames BuiltinImperativeMatchBody
#check_failure SourceTypedRuntime.run
section Syntax
variable {source : TypedSource} {context : SourceSemantics.Context} {expressionSyntax : ExpressionId → Prop}
  {mode : Bool} {id : StatementId} {node : StatementNode} {resolution : MatchResolution}
  {scrutineeNode : ExpressionNode} {rest : List StatementId} {expected : TypeSystem.Ty}
theorem actual_terminal_match_syntax {control : ControlContext} {caseFacts}
      (unique : NodeOccurrencesUnique source)
      (found : source.lookupStatement? id = some node) (form : node.form = .matchWith resolution)
      (sourceType : node.type = .unit ∨ node.type = expected)
      (scrutineeFound : source.lookupExpression? resolution.scrutinee = some scrutineeNode)
      (scrutineeTyped : ExpressionHasType source context resolution.scrutinee scrutineeNode.type)
      (scrutineeSyntax : expressionSyntax resolution.scrutinee)
      (casesTyped : MatchCasesHaveType source control context scrutineeNode.type resolution.cases caseFacts)
      (defaultTyped : ∀ statements, resolution.defaultBody = some statements →
        ∃ finalContext facts, StatementsHaveType source control context statements finalContext facts)
      (hiddenOrdinary : source.inputs.any (fun input => decide (input.id = resolution.hiddenScrutinee)) = false)
      (armsOrdinary : ∀ arm ∈ resolution.cases, ∀ binder ∈ arm.pattern.binderIds,
        source.inputs.any (fun input => decide (input.id = binder)) = false)
      (children : ∀ request childContext,
        GenericMatchChildren.ContextFor source context scrutineeNode.type resolution.cases resolution.defaultBody request childContext →
        GenericImperativeMatch.Syntax source expressionSyntax childContext (.statements false request.statements) expected)
      (stops : ReachableMatchContinuations.DefaultStopped source id resolution) :
      GenericImperativeMatch.Syntax source expressionSyntax context (.statements mode (id :: rest)) expected :=
  .terminalMatch unique found form sourceType scrutineeFound scrutineeTyped scrutineeSyntax casesTyped defaultTyped hiddenOrdinary armsOrdinary children stops

theorem stopped_of_actual_branches {fallback : List StatementId}
    (found : source.lookupStatement? id = some node) (form : node.form = .matchWith resolution)
    (present : resolution.defaultBody = some fallback)
    (branches : ReachableMatchContinuations.BranchStops source resolution) :
    ReachableMatchContinuations.DefaultStopped source id resolution :=
  .of_source found form present branches

theorem original_stops_transport {origin : TypedSource}
    (identity : GenericLexicalStatements.StatementSourceIdentity origin source)
    (stops : ReachableMatchContinuations.DefaultStopped origin id resolution) :
    ReachableMatchContinuations.DefaultStopped source id resolution := stops.transport identity

theorem no_default_stopped (absent : resolution.defaultBody = none) :
    ¬ ReachableMatchContinuations.DefaultStopped source id resolution := by
  intro stopped
  obtain ⟨fallback, present⟩ := stopped.default_present
  rw [absent] at present
  cases present

theorem empty_default_not_stopped (empty : resolution.defaultBody = some []) :
    ¬ ReachableMatchContinuations.DefaultStopped source id resolution := by
  intro stopped
  obtain ⟨origin, summary, _, original⟩ := stopped.current_branches.fallback [] empty
  exact original.nonempty rfl
/-- Reachable nil remains restricted; terminality cannot authenticate an empty list. -/
theorem reachable_nil_nonunit (nonunit : expected ≠ .unit) :
    ¬ GenericImperativeMatch.Syntax source expressionSyntax context (.statements true []) expected := by
  intro tree
  cases tree with
  | body lexical => cases lexical with
    | nil allowed => rcases allowed with impossible | unit; cases impossible; exact nonunit unit

theorem no_empty_stopped : ¬ GenericLexicalStatements.Stopped source [] := by
  rintro ⟨origin, summary, identity, stops⟩
  exact stops.nonempty rfl

/-- Source transport preserves the actual issuing source and callback equation.
It does not assume an arbitrary source-dependent policy accepts the view. -/
theorem original_suffix_transport {origin : TypedSource} {scope : SourceCoreLocalCell.Scope} {type : Ty} {code : Expr}
    (identity : GenericLexicalStatements.StatementSourceIdentity origin source)
    (issued : GenericLexicalStatements.IssuedSuffix origin scope mode rest type code) :
    GenericLexicalStatements.IssuedSuffix source scope mode rest type code :=
  issued.transport identity
end Syntax

section Extraction
open GenericImperativeMatch
variable {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {values : SourceCoreCompatibleValues.Context} {source : TypedSource} {expressionSyntax : ExpressionId → Prop}
  {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {reasonAt : ExpressionId → Word} {policy : SourceCoreLoops.Policy}
  {matchCompilation : SourceCoreCompatibleDataMatches.Context}
  {administrative : Core.Context} {definitions : DataEnvironment}
  {invalidProjection : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Word}
  {invalidOperand : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Solcore.Syntax.ValueAssignOp → Word}
  {invalidUnary : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Word}
  {missingDefault : SourceCoreElaboration.ErrorSite → Resolved.LocalId → TypeSystem.Ty → Word}
theorem accepted_terminal_match (residualMode : Bool) (diagnosticPolicy : AssignmentDiagnosticPolicy) {tracked : Bool}
    (factory : AssignmentDiagnosticOrigins.Factory tracked diagnosticPolicy source invalidOperand)
    (matchPolicy : policy.lowerMatch = some (SourceCoreCompatibleDataMatches.lowerWithReasons matchCompilation))
    (matchValues : matchCompilation.values = values) (matchDefinitions : matchCompilation.definitions = definitions)
    (matchAllocator : matchCompilation.sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator frame globals
      (layouts.allocatorAt owner active onError)))
    (matchChildStatic : MatchChildStatic matchCompilation source certificates definitions administrative)
    (readPolicy : policy.readStatement = SourceCoreCompatibleDataExpressions.readStatement values.checked)
    (binderPolicy : ∀ scope binder, binder.scheme.quantified = [] →
      policy.lowerBinder source scope binder = SourceCoreCompatibleDataExpressions.lowerBinder values.checked source scope binder)
    (allocationPolicy : policy.sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator frame globals
      (layouts.allocatorAt owner active onError)))
    (expressions : ∀ sourceContext, sourceContext.typeVariables = [] → sourceContext.residualTypeVariables = residualMode →
      sourceContext.signatures = values.checked.signatures →
      ∀ {scope fuel id node lowered}, CompatibleExpressionReads.ScopeDeclarations source scope sourceContext → expressionSyntax id →
      source.lookupExpression? id = some node → ExpressionHasType source sourceContext id node.type →
      policy.lowerExpression fuel source scope id reasonAt = .ok lowered →
      certificates sourceContext scope id lowered)
    (assignments : CompatibleAssignmentStatements.AssignmentPolicy policy values invalidProjection invalidOperand missingDefault)
    (unaryPolicy : CompatibleBitNotStatements.Policy policy values invalidProjection invalidUnary missingDefault)
    (assignmentExpressions : ∀ sourceContext scope fuel id lowered,
      sourceContext.typeVariables = [] → sourceContext.residualTypeVariables = residualMode →
      sourceContext.signatures = values.checked.signatures →
      CompatibleExpressionReads.ScopeDeclarations source scope sourceContext →
      expressionSyntax id → ∀ node, source.lookupExpression? id = some node →
      ExpressionHasType source sourceContext id node.type →
      policy.lowerExpression fuel source scope id reasonAt = .ok lowered →
        certificates sourceContext scope id lowered ∧
        HasType (SourceCoreLocalCell.coreContext scope ++ administrative) lowered.expression
          (LanguageResult.resultType lowered.type) definitions)
    {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope} {mode : Bool} {id : StatementId}
    {node : StatementNode} {resolution : MatchResolution} {scrutineeNode : ExpressionNode}
    {rest : List StatementId} {expected : TypeSystem.Ty} {control : ControlContext} {caseFacts}
      (exactUnique : NodeOccurrencesUnique source)
      (found : source.lookupStatement? id = some node) (form : node.form = .matchWith resolution)
      (sourceType : node.type = .unit ∨ node.type = expected)
      (scrutineeFound : source.lookupExpression? resolution.scrutinee = some scrutineeNode)
      (scrutineeTyped : ExpressionHasType source context resolution.scrutinee scrutineeNode.type)
      (scrutineeSyntax : expressionSyntax resolution.scrutinee)
      (casesTyped : MatchCasesHaveType source control context scrutineeNode.type resolution.cases caseFacts)
      (defaultTyped : ∀ statements, resolution.defaultBody = some statements →
        ∃ finalContext facts, StatementsHaveType source control context statements finalContext facts)
      (hiddenOrdinary : source.inputs.any (fun input => decide (input.id = resolution.hiddenScrutinee)) = false)
      (armsOrdinary : ∀ arm ∈ resolution.cases, ∀ binder ∈ arm.pattern.binderIds,
        source.inputs.any (fun input => decide (input.id = binder)) = false)
      (children : ∀ request childContext,
        GenericMatchChildren.ContextFor source context scrutineeNode.type resolution.cases resolution.defaultBody request childContext →
        GenericImperativeMatch.Syntax source expressionSyntax childContext (.statements false request.statements) expected)
      (stops : ReachableMatchContinuations.DefaultStopped source id resolution)
    (closed : context.typeVariables = []) (residual : context.residualTypeVariables = residualMode)
    (sourceSignatures : context.signatures = values.checked.signatures)
    (declarations : CompatibleExpressionReads.ScopeDeclarations source scope context)
    {fuel : Nat} {type : Ty} {code : Expr} {selfReason : Word} {nativeType : Ty}
    (projection : values.checked.catalog.project expected = .ok type)
    (accepted : SourceCoreLoops.lowerFlowStatementsWithPolicy policy fuel source scope (id :: rest) type reasonAt mode selfReason = .ok code)
    (nativeTyped : HasType (SourceCoreLocalCell.coreContext scope ++ administrative) code nativeType definitions) :
    Nonempty (ExtractionFor diagnosticPolicy layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative matchCompilation.solvedRequirements
      context scope (.statements mode (id :: rest)) expected type code) := by
  exact extraction_of_typed_flow_with_residual residualMode diagnosticPolicy factory matchPolicy matchValues matchDefinitions
    matchAllocator matchChildStatic readPolicy binderPolicy allocationPolicy expressions assignments unaryPolicy exactUnique
    assignmentExpressions (.terminalMatch exactUnique found form sourceType scrutineeFound scrutineeTyped scrutineeSyntax casesTyped
      defaultTyped hiddenOrdinary armsOrdinary children stops) closed residual sourceSignatures declarations projection accepted nativeTyped

end Extraction

section LedgerConsumers
open GenericImperativeMatch
variable {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {values : ValuesContext} {source : TypedSource} {expressionSyntax : ExpressionId → Prop}
  {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {definitions : DataEnvironment} {administrative : Core.Context}
  {diagnosticPolicy : AssignmentDiagnosticPolicy} {registry : SourceCoreRawMetadata.Registry}
  {faults : FunctionCalls.FaultRep} {solved : List SolvedRequirement} {evidence : Dynamic.EvidenceEnvironment}
  {context : SourceSemantics.Context} {scope : Scope} {mode : Bool} {id : StatementId} {node : StatementNode}
  {rest statements : List StatementId} {expected : TypeSystem.Ty} {type : Ty} {innerCode suffix : Expr}

theorem branch_only_ready {resolution : MatchResolution} {scrutineeNode : ExpressionNode}
    {matched : Expr} {selfReason : Word} {control : ControlContext} {caseFacts}
      (unique : NodeOccurrencesUnique source)
      (found : source.lookupStatement? id = some node) (form : node.form = .matchWith resolution)
      (scrutineeFound : source.lookupExpression? resolution.scrutinee = some scrutineeNode)
      (scrutineeTyped : ExpressionHasType source context resolution.scrutinee scrutineeNode.type)
      (casesTyped : MatchCasesHaveType source control context scrutineeNode.type resolution.cases caseFacts)
      (defaultTyped : ∀ statements, resolution.defaultBody = some statements →
        ∃ finalContext facts, StatementsHaveType source control context statements finalContext facts)
      (compilation : SourceCoreCompatibleDataMatches.Context)
      (sameValues : compilation.values = values) (sameDefinitions : compilation.definitions = definitions)
      (allocator : compilation.sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator frame globals
        (layouts.allocatorAt owner active onError)))
      (requests : List GenericMatchChildren.Request)
      (receipt : CompatibleMatchCertificates.Certificate compilation source scope id resolution type selfReason
        (certificates context) (GenericMatchChildren.Occurs requests) matched)
      (ordinary : CompatibleMatchSelectionPrefix.Ordinary receipt)
      (children : ∀ request, request ∈ requests → ∀ childContext,
        GenericMatchChildren.ScopedContextFor source context (resolution.hiddenScrutinee :: scope.map Prod.fst) scrutineeNode.type resolution.cases resolution.defaultBody request childContext →
        Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
          childContext request.scope (.statements false request.statements) expected type request.code)
      (stops : ReachableMatchContinuations.DefaultStopped source id resolution)
      (issued : GenericLexicalStatements.IssuedSuffix source scope mode rest type suffix)
    (childErrors : ∀ request member childContext related, Tree.ErrorsFor diagnosticPolicy registry faults (children request member childContext related))
    (sameLedger : compilation.solvedRequirements = solved)
    (childLedgers : ∀ request member childContext related, Tree.SiteLedgersFor diagnosticPolicy solved registry faults (childErrors request member childContext related))
    (valid : CompatibleExpressionLiterals.ContextValid solved context evidence)
    (signatures : context.signatures = values.checked.signatures) :
    Tree.ReadyFor diagnosticPolicy registry faults (.terminalMatch unique found form scrutineeFound scrutineeTyped casesTyped defaultTyped
      compilation sameValues sameDefinitions allocator requests receipt ordinary children stops issued) := by
  exact Tree.SiteLedgersFor.ready
    (Tree.SiteLedgersFor.terminalMatch (unique := unique) (found := found) (scrutineeFound := scrutineeFound)
      (scrutineeTyped := scrutineeTyped) (casesTyped := casesTyped) (defaultTyped := defaultTyped)
      (sameValues := sameValues) (allocator := allocator) (receipt := receipt) (ordinary := ordinary)
      (stops := stops) (issued := issued) form sameDefinitions sameLedger childLedgers) valid signatures
end LedgerConsumers

section CompilerConsumers
variable {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frameLayout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {readFuel : Nat} {values : SourceCoreCompatibleValues.Context}
  {function : Dynamic.Closure} {context : SourceSemantics.Context} {solved : List SolvedRequirement}
  {reasonAt : ExpressionId → Word} {scope : SourceCoreLocalCell.Scope} {type : Ty}
  {administrative : Core.Context}
  {policy : SourceCoreLoops.Policy} {fuel : Nat} {fellThrough escaped : Word} {code : Expr}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient)
  {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends values.registry registry)
  (definitions : layouts.definitions = ambient.definitions)
  (registered : frameLayout.Registered ambient.definitions)
  (catalogValid : SignatureCatalogWellFormed values.checked.signatures)
  (program : SourceSemantics.Program)
  (contextValid : CompatibleExpressionLiterals.ContextValid solved context function.evidence)
  (unique : NodeOccurrencesUnique function.source) {faults : FunctionCalls.FaultRep}
  (escapedFault : faults .controlEscapedFunction escaped)
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))
  (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((reasonAt id).add tag))

  {identities : Dynamic.Value → Word → Prop}
  (faithful : DataEquality.IdentityFaithful identities)
  (functionLeaves : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)
  (functionTypes : FunctionRuntimeViews functions)

include definitions registered catalogValid escapedFault extension faithful functionLeaves functionTypes contextValid unique uninitialized missing in
theorem actual_compiler_body_preserves
    (accepted : SourceCoreLoops.lowerStatementsWithPolicy policy fuel function.source scope
      function.body type reasonAt fellThrough escaped = .ok code)
    (projection : values.checked.catalog.project function.resultType = .ok type)
    {flow : Expr}
    (generated : SourceCoreLoops.lowerFlowStatementsWithPolicy policy fuel function.source scope
      function.body type reasonAt true escaped = .ok flow)
    (tree : BuiltinImperativeMatch.Tree layouts owner active frameLayout globals onError readFuel
      values function.source solved reasonAt ambient.definitions administrative
      context scope (.statements true function.body) function.resultType type flow)
    (errors : GenericImperativeMatch.Tree.Ready registry faults tree)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {outcome : Dynamic.ExpressionOutcome}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    {contextLocation : Location} {native : SourceCoreCallableIndexedFrames.Frame}
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frameLayout.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frameLayout native))
    (unmapped : contextLocation ∉ mapping)
    (trace : FunctionCallBody.Trace program function context environment before outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (code.rename ξ) value finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld function.resultType type faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      TypedMixedNamedBody.ReachedExit values.checked ambient.definitions finalMap finalWorld administrative program function
        context scope environment before after outcome := by
  let certificate := of_extracted accepted projection generated tree
  exact certificate.preserves functions extension definitions registered catalogValid program
    contextValid unique escapedFault uninitialized missing faithful functionLeaves functionTypes
    errors environments heaps locals agrees actualTyped reference read unmapped trace

include definitions registered catalogValid escapedFault extension faithful functionLeaves functionTypes contextValid unique uninitialized missing in
theorem actual_compiler_body_reflects
    (accepted : SourceCoreLoops.lowerStatementsWithPolicy policy fuel function.source scope
      function.body type reasonAt fellThrough escaped = .ok code)
    (projection : values.checked.catalog.project function.resultType = .ok type)
    {flow : Expr}
    (generated : SourceCoreLoops.lowerFlowStatementsWithPolicy policy fuel function.source scope
      function.body type reasonAt true escaped = .ok flow)
    (tree : BuiltinImperativeMatch.Tree layouts owner active frameLayout globals onError readFuel
      values function.source solved reasonAt ambient.definitions administrative
      context scope (.statements true function.body) function.resultType type flow)
    (errors : GenericImperativeMatch.Tree.Ready registry faults tree)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
    {store finalStore : Store} {ξ : Renaming} {value : Value}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    {contextLocation : Location} {native : SourceCoreCallableIndexedFrames.Frame}
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frameLayout.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frameLayout native))
    (unmapped : contextLocation ∉ mapping)
    (evaluated : Evaluates actual store (code.rename ξ) value finalStore) :
    ∃ outcome after finalMap finalWorld,
      FunctionCallBody.Trace program function context environment before outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld function.resultType type faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      TypedMixedNamedBody.ReachedExit values.checked ambient.definitions finalMap finalWorld administrative program function
        context scope environment before after outcome := by
  let certificate := of_extracted accepted projection generated tree
  exact certificate.reflects functions extension definitions registered catalogValid program
    contextValid unique escapedFault uninitialized missing faithful functionLeaves functionTypes
    errors environments heaps locals agrees actualTyped reference read unmapped evaluated
end CompilerConsumers

private def content : String := String.intercalate "\n" [
  "enum Choice { Left(Word), Right(Word) }",
  "function direct(seed: Word) returns (Word) { match (seed) { case 0 { return 43; } default { return 47; } } }",
  "function dead(seed: Word) returns (Word) { match (seed) { case 0 { if (true) { return 13; } else { return 17; } } default { { return 19; } } } let gap: Word; gap; }",
  "function pattern(seed: Word) returns (Word) { match ((seed, 11)) { case (0, x) { { return x; } let skipped = 99; } default { if (true) { return seed; } else { return 61; } let skipped = 99; } } return 99; }",
  "function same(seed: Word) returns (Word) { match (seed) { case 0 { return 23; } case 1 { return 23; } default { return 23; } } return 99; }",
  "function reachable(seed: Word) returns (Word) { match (seed) { case 0 {} default { return 31; } } return 29; }",
  "function failed(seed: Word) returns (Word) { match (seed) { case 0 { let prior = 37; let gap: Word; return gap; } default { return 41; } } let skipped = 99; return skipped; }",
  "function scrutineeFault() returns (Word) { let gap: Word; match (gap) { case 0 { return 1; } default { return 2; } } let skipped = 99; return skipped; }",
  "function inFor() returns (Word) { for (; true; ) { match (4) { case 4 { return 23; } default { return 29; } } let gap: Word; gap; } return 99; }",
  "function inWhile() returns (Word) { while (true) { match (5) { case 5 { return 31; } default { return 37; } } let gap: Word; gap; } return 99; }",
  "function inBlock() returns (Word) { { match (6) { case 6 { return 41; } default { return 43; } } let gap: Word; gap; } let skipped = 99; return skipped; }",
  "function inIf(flag: Bool) returns (Word) { if (flag) { match (7) { case 7 { return 47; } default { return 53; } } let gap: Word; gap; } else { match (8) { case 8 { return 59; } default { return 61; } } let gap: Word; gap; } }",
  "function nominalLeft(value: Choice) returns (Word) { match (value) { case .Left(x) { return x; } case .Right(y) { return y; } } }",
  "function nominalRight(value: Choice) returns (Word) { match (value) { case .Left(x) { return x; } case .Right(y) { return y; } } }"
]
private def w (n : Nat) : SourceTypedRuntime.Value := .word (Word.ofNatModulo n)
private def get {α ε : Type} [Repr ε] := @SourceCoreUnifiedCorpusSupport.get α ε _
private def require := SourceCoreUnifiedCorpusSupport.assertTrue

private def inspect (compiled : SourceCoreUnifiedCompilation.Compiled) : IO Unit := do
  let prepared := compiled.indexed
  let diagnostics ← match prepared.base.diagnostics with
    | none => throw (IO.userError "terminal default match continuations missing diagnostics")
    | some diagnostic => pure diagnostic.program
  let diagnostics := match prepared.base.callableContext with
    | none => diagnostics
    | some native => {diagnostics with rootTable := native.diagnostics.rootTable}
  let parents ← get "terminal default match parent contexts"
    (SourceCoreStageCodebook.prepareContexts prepared.base.sourceProgram prepared.base.plan
      (prepared.base.locals.bindings.flatMap (·.instances)))
  let mut defaultNodes := 0
  let mut noDefaultNodes := 0
  let mut nilSuffixes := 0
  let mut nonemptySuffixes := 0
  for named in prepared.base.functions do
    let actual := (CallableIndexedNamedGeneration.representation prepared).atContext named.signature.key []
    let own ← match diagnostics.base.find? named.signature.key with
      | none => throw (IO.userError "terminal default match own diagnostics missing")
      | some own => pure own
    let source := CallableIndexedNamedGeneration.source named
    let scope := named.inputs.reverse.map (fun binding => (binding.1.id, binding.2))
    let reasonAt := diagnostics.reasonAt named.signature.key
    let lower := SourceCoreGeneralFunctions.lowerContextualExpression prepared.base.sourceProgram actual
      prepared.base.sourceProgram.signatures prepared.base.locals parents own.assignments diagnostics
      (CallableIndexedNamedGeneration.context prepared named) prepared.base.callableContext none none
    let policy : SourceCoreLoops.Policy := {
      actual.loopsWithSourceCells actual.expressions.sourceCells named.specialized.function.solvedRequirements
        own.assignments diagnostics named.signature.key lower with
      sourceCells := actual.expressions.sourceCells
      lowerBinder := SourceCoreGeneralFunctions.contextualBinder actual prepared.base.locals named.signature.key [] }
    let statements ← get "terminal default match actual roots"
      (source.roots.mapM (m := Except SourceCoreGeneralFunctions.Error) (fun
        | .statement id => pure id | .expression id => throw (.expectedStatementRoot id)))
    let body ← get "terminal default match actual body"
      (SourceCoreLoops.lowerStatementsWithPolicy policy prepared.fuel source scope statements
        named.signature.resultType reasonAt own.fellThroughReason own.table.escapedReason)
    let same ← get "terminal default match actual compiler body"
      (CallableIndexedNamedGeneration.bodyAction prepared named diagnostics parents own statements)
    require (body == same) "terminal default match changed actual body code"
    for item in source.nodes do
      match item with
      | .statement node =>
        match node.form with
        | .matchWith resolution =>
          if resolution.defaultBody.isSome then defaultNodes := defaultNodes + 1
          else noDefaultNodes := noDefaultNodes + 1
          require (!(SourceCoreDataPlaces.declaredBinders source).any (fun binder => binder.id == resolution.hiddenScrutinee))
            "terminal default match hidden scrutinee overlaps a source binder"
        | _ => pure ()
      | _ => pure ()
    match statements with
    | id :: rest =>
      let node ← match source.lookupStatement? id with
        | none => throw (IO.userError "terminal default match root lookup missing")
        | some node => pure node
      match node.form with
      | .matchWith resolution =>
        let callback ← match policy.lowerMatch with
          | none => throw (IO.userError "terminal default match callback missing")
          | some callback => pure callback
        let matched ← get "terminal default match actual callback"
          (callback policy.lowerExpression
            (fun _ childSource childScope childStatements resultType childReasonAt escaped =>
              SourceCoreLoops.lowerFlowStatementsWithPolicy policy (prepared.fuel - 1) childSource childScope childStatements
                resultType childReasonAt false escaped)
            (prepared.fuel - 1) source scope id resolution named.signature.resultType reasonAt own.table.escapedReason)
        let suffix ← get "terminal default match complete emitted suffix"
          (SourceCoreLoops.lowerFlowStatementsWithPolicy policy (prepared.fuel - 1) source scope rest
            named.signature.resultType reasonAt true own.table.escapedReason)
        let whole ← get "terminal default match whole flow"
          (SourceCoreLoops.lowerFlowStatementsWithPolicy policy prepared.fuel source scope statements
            named.signature.resultType reasonAt true own.table.escapedReason)
        require (whole == LocalLoop.sequence named.signature.resultType matched suffix)
          "terminal default match did not retain actual callback and full suffix"
        if rest.isEmpty then nilSuffixes := nilSuffixes + 1 else nonemptySuffixes := nonemptySuffixes + 1
      | _ => pure ()
    | [] => pure ()
  require (defaultNodes == 12 && noDefaultNodes == 2 && nilSuffixes == 3 && nonemptySuffixes == 5)
    s!"terminal default match fixture coverage changed: {defaultNodes}/{noDefaultNodes}/{nilSuffixes}/{nonemptySuffixes}"

private def finish (compiled : SourceCoreUnifiedCompilation.Compiled) (name : String)
    (arguments : List SourceTypedRuntime.Value) (fuel : Nat) (initial : SourceTypedRuntime.RuntimeState) : IO SourceTypedRuntime.RunResult := do
  let first ← SourceCoreUnifiedCorpusSupport.execute compiled name arguments fuel initial
  pure (← get "terminal default match public resume" (first.resume 300000)).observation

def run : IO Unit := do
  let compiled ← SourceCoreUnifiedCorpusSupport.prepare "terminal default match continuations" content
    ["direct", "dead", "pattern", "same", "reachable", "failed", "scrutineeFault", "nominalLeft", "nominalRight", "inFor", "inWhile", "inBlock", "inIf"]
  inspect compiled
  let initial : SourceTypedRuntime.RuntimeState := {heap := [⟨.word, some (w 821)⟩]}
  let successes : List (String × List SourceTypedRuntime.Value × SourceTypedRuntime.Value × List (TypeSystem.Ty × Option SourceTypedRuntime.Value)) := [
    ("inFor", [], w 23, [(.word, some (w 4))]),
    ("inWhile", [], w 31, [(.word, some (w 5))]),
    ("inBlock", [], w 41, [(.word, some (w 6))]),
    ("inIf", [.bool true], w 47, [(.bool, some (.bool true)), (.word, some (w 7))]),
    ("inIf", [.bool false], w 59, [(.bool, some (.bool false)), (.word, some (w 8))]),
    ("direct", [w 0], w 43, [(.word, some (w 0)), (.word, some (w 0))]),
    ("direct", [w 1], w 47, [(.word, some (w 1)), (.word, some (w 1))]),
    ("dead", [w 0], w 13, [(.word, some (w 0)), (.word, some (w 0))]),
    ("dead", [w 1], w 19, [(.word, some (w 1)), (.word, some (w 1))]),
    ("pattern", [w 0], w 11, [(.word, some (w 0)), (.product .word .word, some (.product (w 0) (w 11))), (.word, some (w 11))]),
    ("pattern", [w 2], w 2, [(.word, some (w 2)), (.product .word .word, some (.product (w 2) (w 11)))]),
    ("same", [w 0], w 23, [(.word, some (w 0)), (.word, some (w 0))]),
    ("same", [w 1], w 23, [(.word, some (w 1)), (.word, some (w 1))]),
    ("same", [w 2], w 23, [(.word, some (w 2)), (.word, some (w 2))]),
    ("reachable", [w 0], w 29, [(.word, some (w 0)), (.word, some (w 0))]),
    ("reachable", [w 1], w 31, [(.word, some (w 1)), (.word, some (w 1))]),
    ("failed", [w 1], w 41, [(.word, some (w 1)), (.word, some (w 1))])]
  let baselines ← successes.mapM (fun test => finish compiled test.1 test.2.1 300000 initial)
  for fuel in [0, 31, 300000] do
    for ((name, arguments, expected, expectedCells), baseline) in successes.zip baselines do
      let observed ← finish compiled name arguments fuel initial
      require (reprStr observed == reprStr baseline) s!"terminal default match full resume changed {name}"
      match observed with
      | .done result final =>
        require (reprStr result == reprStr expected) s!"terminal default match result changed {name}"
        require (reprStr final.heap == reprStr (initial.heap ++ expectedCells.map (fun (type, value) => ⟨type, value⟩)))
          s!"terminal default match full heap/dead suffix changed {name}"
      | other => throw (IO.userError s!"terminal default match expected done {name}: {reprStr other}")
  let failures : List (String × List SourceTypedRuntime.Value × List (TypeSystem.Ty × Option SourceTypedRuntime.Value)) := [
    ("failed", [w 0], [(.word, some (w 0)), (.word, some (w 0)), (.word, some (w 37)), (.word, none)]),
    ("scrutineeFault", [], [(.word, none)])]
  for (name, arguments, expectedCells) in failures do
    let baseline ← finish compiled name arguments 300000 initial
    for fuel in [0, 31, 300000] do
      let observed ← finish compiled name arguments fuel initial
      require (reprStr observed == reprStr baseline) s!"terminal default match fault resume changed {name}"
      match observed with
      | .fault (.uninitializedLocal _) final =>
        require (reprStr final.heap == reprStr (initial.heap ++ expectedCells.map (fun (type, value) => ⟨type, value⟩)))
          s!"terminal default match first fault/dead suffix changed {name}"
      | other => throw (IO.userError s!"terminal default match expected fault {name}: {reprStr other}")
  let choice ← match compiled.indexed.base.sourceProgram.signatures.dataTypes.find? (·.name == "Choice") with
    | none => throw (IO.userError "terminal default match Choice missing")
    | some choice => pure choice
  let sourceType := TypeSystem.Ty.nominal choice.id []
  for (name, constructor, value) in [("nominalLeft", 0, 5), ("nominalRight", 1, 7)] do
    let metadata : DataConstructorInstantiation := ⟨⟨choice.id, constructor⟩, [], [.word], sourceType⟩
    let expected : SourceTypedRuntime.Value := .constructed metadata [w value]
    let baseline ← finish compiled name [expected] 300000 initial
    for fuel in [0, 31, 300000] do
      let observed ← finish compiled name [expected] fuel initial
      require (reprStr observed == reprStr baseline) s!"reachable typed nominal resume changed {name}"
      match observed with
      | .done result final =>
        require (reprStr result == reprStr (w value)) s!"reachable typed nominal result changed {name}"
        require (reprStr final.heap == reprStr (initial.heap ++ [⟨sourceType, some expected⟩, ⟨sourceType, some expected⟩, ⟨.word, some (w value)⟩]))
          s!"reachable typed nominal full heap changed {name}"
      | other => throw (IO.userError s!"reachable typed nominal expected done {name}: {reprStr other}")
  IO.println "terminal default match continuations: same grammar terminal default, separate typed no-default, actual issued suffix, full source cells/fault/public resume GREEN"

end Tests.SourceCoreReachableTerminalMatchStatements
end

section
-- leanmerge: from Solcore.Test.SourceCoreRecursiveNamedImperativeMatchSyntax
/-! The factory replaces an external statement Syntax premise with independent
source typing and finite static leaf/allocator/stopping receipts. No-default-only
stopping remains typed and pointwise. The retained nonsemicolon block fixture
has actual bodyAction acceptance and exact emitted-code equality; public parser
and checked-source provenance for that retained IR view are not claimed. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 65536
namespace Tests.SourceCoreRecursiveNamedImperativeMatchSyntax
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open RecursiveNamedStatementSyntaxFacts RecursiveNamedImperativeMatchSyntaxFactory

section Formal
variable {source : TypedSource} {expressionSyntax : ExpressionId → Prop}
  {control : ControlContext} {context final : SourceSemantics.Context} {ids : List StatementId}
  {facts : BodyFacts} {typed : StatementsHaveType source control context ids final facts} {ready : Bool}

theorem actual_typed_syntax (unique : NodeOccurrencesUnique source)
    (receipt : BodyReceipts source expressionSyntax typed ready) (annotation : facts.type = control.returnType) :
    GenericImperativeMatch.Syntax source expressionSyntax context (.statements true ids) control.returnType :=
  syntax_of_typed unique receipt annotation

theorem same_typed_stopping (unique : NodeOccurrencesUnique source)
    (receipt : BodyReceipts source expressionSyntax typed ready) (available : ready = true) :
    ReachableStatementContinuations.StoppingStatements source ids facts.control :=
  receipt.stopping unique available

include typed in
theorem returned_annotation (returned : facts.sawReturn = true) : facts.type = control.returnType :=
  returned_type typed returned
end Formal

section ScopedBlock
variable {source : TypedSource} {expressionSyntax : ExpressionId → Prop}
  {control : ControlContext} {context innerFinal final : SourceSemantics.Context}
  {id next : StatementId} {node : StatementNode} {body rest : List StatementId}
  {innerFacts tailFacts : BodyFacts}
  (contains : ContainsStatement source id node) (form : node.form = .block body)
  (innerTyped : StatementsHaveType source control context body innerFinal innerFacts)
  (annotation : node.type = innerFacts.type)
  (tailTyped : StatementsHaveType source control context (next :: rest) final tailFacts)
  {innerReady tailReady : Bool}
  (inner : BodyReceipts source expressionSyntax innerTyped innerReady)
  (tail : BodyReceipts source expressionSyntax tailTyped tailReady)
  (tailAnnotation : tailFacts.type = control.returnType)
  (wholeAnnotation : (BodyFacts.cons
    { type := innerFacts.type, hasValue := innerFacts.sawReturn, sawReturn := innerFacts.sawReturn,
      control := innerFacts.control.eraseValue } tailFacts).type = control.returnType)
include contains form innerTyped annotation tailTyped inner tail tailAnnotation wholeAnnotation

/-- A nonreturn value annotation on the inner block needs no Unit restriction. -/
theorem ordinary_scoped_block (unique : NodeOccurrencesUnique source) :
    GenericImperativeMatch.Syntax source expressionSyntax context (.statements true (id :: next :: rest)) control.returnType := by
  have head : StatementReceipts source expressionSyntax
      (StatementHasType.block contains form innerTyped annotation) innerReady := .block (contains := contains) (form := form) (annotation := annotation) inner
  have receipt : BodyReceipts source expressionSyntax
      (StatementsHaveType.cons (StatementHasType.block contains form innerTyped annotation) tailTyped)
      (innerReady || tailReady) := .cons (head := StatementHasType.block contains form innerTyped annotation) (tail := tailTyped) head tail (fun _ => .inl tailAnnotation)
  exact syntax_of_typed unique receipt wholeAnnotation
end ScopedBlock

section PartialIf
variable {source : TypedSource} {expressionSyntax : ExpressionId → Prop}
  {control : ControlContext} {context thenFinal final : SourceSemantics.Context}
  {id next : StatementId} {node : StatementNode} {condition : ExpressionId} {body rest : List StatementId}
  {bodyFacts tailFacts : BodyFacts}
  (contains : ContainsStatement source id node) (form : node.form = .ifThen condition body none)
  (conditionTyped : ExpressionHasType source context condition .bool)
  (bodyTyped : StatementsHaveType source control context body thenFinal bodyFacts)
  (annotation : node.type = .unit)
  (tailTyped : StatementsHaveType source control context (next :: rest) final tailFacts)
  {bodyReady tailReady : Bool}
  (conditionSyntax : expressionSyntax condition)
  (bodyReceipt : BodyReceipts source expressionSyntax bodyTyped bodyReady)
  (tailReceipt : BodyReceipts source expressionSyntax tailTyped tailReady)
  (tailAnnotation : tailFacts.type = control.returnType)
include contains form conditionTyped bodyTyped annotation tailTyped conditionSyntax bodyReceipt tailReceipt tailAnnotation

/-- A partially returning ordinary if keeps Unit and the actual typed tail. -/
theorem partial_if_with_tail (unique : NodeOccurrencesUnique source) :
    GenericImperativeMatch.Syntax source expressionSyntax context (.statements true (id :: next :: rest)) control.returnType := by
  have head : StatementReceipts source expressionSyntax
      (StatementHasType.ifWithoutElse contains form conditionTyped bodyTyped annotation) false :=
    .ifWithoutElse (contains := contains) (form := form) (conditionTyped := conditionTyped) (annotation := annotation) conditionSyntax bodyReceipt
  have receipt : BodyReceipts source expressionSyntax
      (StatementsHaveType.cons (StatementHasType.ifWithoutElse contains form conditionTyped bodyTyped annotation) tailTyped)
      (false || tailReady) := .cons (head := StatementHasType.ifWithoutElse contains form conditionTyped bodyTyped annotation) (tail := tailTyped) head tailReceipt (fun _ => .inl tailAnnotation)
  exact syntax_of_typed unique receipt (by simp [BodyFacts.cons, tailAnnotation])
end PartialIf

section ReachedTail
variable {source : TypedSource} {expressionSyntax : ExpressionId → Prop}
  {control : ControlContext} {context : SourceSemantics.Context} {id next : StatementId}
  {node : StatementNode} {resolution : MatchResolution} {type : TypeSystem.Ty}
  {caseFacts : List BodyFacts} {summary : ControlSummary}
  (contains : ContainsStatement source id node) (form : node.form = .matchWith resolution)
  (absent : resolution.defaultBody = none)
  (scrutineeTyped : ExpressionHasType source context resolution.scrutinee type)
  (casesTyped : MatchCasesHaveType source control context type resolution.cases caseFacts)
  (requirements : resolution.requirements = resolution.cases.flatMap (fun arm => arm.pattern.requirements))
  (exhaustive : MatchExhaustive context type resolution.cases none)
  (merged : mergeBodyControls caseFacts none = some summary)
  (annotation : node.type = if allBodiesSawReturn caseFacts then control.returnType else .unit)
  {caseReady : Bool} (scrutinee : expressionSyntax resolution.scrutinee)
  (casesReceipt : CasesReceipts source expressionSyntax casesTyped caseReady)
  (hidden : source.inputs.any (fun input => decide (input.id = resolution.hiddenScrutinee)) = false)
  (ordinary : ∀ arm ∈ resolution.cases, ∀ binder ∈ arm.pattern.binderIds,
    source.inputs.any (fun input => decide (input.id = binder)) = false)
  {final : SourceSemantics.Context} {rest : List StatementId} {tailFacts : BodyFacts}
  (tailTyped : StatementsHaveType source control context (next :: rest) final tailFacts)
  {tailReady : Bool} (tail : BodyReceipts source expressionSyntax tailTyped tailReady)
  (tailReturns : tailFacts.sawReturn = true) (tailAnnotation : tailFacts.type = control.returnType)
include contains form absent scrutineeTyped casesTyped requirements exhaustive merged annotation
  scrutinee casesReceipt hidden ordinary tailTyped tail tailReturns tailAnnotation

/-- No-default heads are admitted when the actual typed continuation returns.
They are not globally excluded or promoted to universal stopping. -/
theorem no_default_with_typed_tail (unique : NodeOccurrencesUnique source) :
    GenericImperativeMatch.Syntax source expressionSyntax context (.statements true (id :: next :: rest)) control.returnType := by
  let headTyped := StatementHasType.matchWithoutDefault contains form absent scrutineeTyped casesTyped requirements exhaustive merged annotation
  have head : StatementReceipts source expressionSyntax headTyped false :=
    .matchWithoutDefault (contains := contains) (form := form) (absent := absent)
      (scrutineeTyped := scrutineeTyped) (casesTyped := casesTyped) (requirements := requirements)
      (exhaustive := exhaustive) (merged := merged) (annotation := annotation) scrutinee casesReceipt hidden ordinary
  have receipt : BodyReceipts source expressionSyntax (StatementsHaveType.cons headTyped tailTyped) (false || tailReady) :=
    .cons (head := headTyped) (tail := tailTyped) head tail (fun _ => .inl tailAnnotation)
  exact syntax_of_typed unique receipt (by simp [BodyFacts.cons, tailReturns, tailAnnotation])
end ReachedTail

section Boundaries
variable {source : TypedSource} {context : SourceSemantics.Context} {expressionSyntax : ExpressionId → Prop}
  {control : ControlContext} {mode : Bool} {expected : TypeSystem.Ty}

/-- An empty typed body authenticates no universal stopping selection. -/
theorem empty_has_no_stopping :
    ¬ ReachableStatementContinuations.StoppingStatements source [] (BodyFacts.empty.control) := by
  intro stopped
  exact stopped.nonempty rfl

/-- The new scoped block does not change reachable nil's result restriction. -/
theorem nil_nonunit (nonunit : expected ≠ .unit) :
    ¬ GenericImperativeMatch.Syntax source expressionSyntax context (.statements true []) expected := by
  intro tree
  cases tree with
  | body lexical => cases lexical with
    | nil allowed => rcases allowed with impossible | unit; cases impossible; exact nonunit unit

abbrev no_default_universal := @Tests.SourceCoreReachableImperativeMatchStatements.no_default_match_has_no_stopping_head

/-- The actual ordinary-if form, independent typing and source uniqueness
identify its retained Unit annotation. -/
theorem partial_if_annotation {id : StatementId} {node : StatementNode}
    {condition : ExpressionId} {body : List StatementId} {final : SourceSemantics.Context} {facts : StatementFacts}
    (unique : NodeOccurrencesUnique source)
    (typed : StatementHasType source control context id final facts)
    (found : source.lookupStatement? id = some node) (form : node.form = .ifThen condition body none) :
    node.type = .unit := by
  have sameNode : ∀ actual, ContainsStatement source id actual → actual = node := by
    intro actual contains
    exact Option.some.inj ((lookupStatement?_complete unique contains).symm.trans found)
  cases typed <;> have same := sameNode _ (by assumption) <;> cases same <;> simp_all
end Boundaries

/-- The actual compiler entry consumes the new syntax factory, with completion,
residual context and all original callback equations retained. -/
abbrev actual_body_extraction := @RecursiveNamedImperativeMatchSyntaxFactory.extraction_of_typed_body

private def get {α ε : Type} [Repr ε] := @SourceCoreUnifiedCorpusSupport.get α ε _
private def require := SourceCoreUnifiedCorpusSupport.assertTrue
private def content : String := String.intercalate "\n" [
 "function partialIf(seed: Word) returns (Word) { if (seed == 0) { return 17; } return 23; }",
 "function partialBoth(seed: Word) returns (Word) { if (seed == 0) { if (seed == 1) { return 29; } } else { if (seed == 2) { return 31; } } return 37; }",
 "function totalIf(seed: Word) returns (Word) { if (seed == 0) { return 41; } else { return 43; } }",
 "function blockFalls(seed: Word) returns (Word) { { if (seed == 0) { return 47; } } return 53; }",
 "function scopedValue() returns (Word) { { 61; } return 67; }",
 "function faultBefore(seed: Word) returns (Word) { if (seed == 0) { let gap: Word; return gap; } return 97; }"
]
private def finish (compiled : SourceCoreUnifiedCompilation.Compiled) (name : String)
    (arguments : List SourceTypedRuntime.Value) (fuel : Nat) (initial : SourceTypedRuntime.RuntimeState) : IO SourceTypedRuntime.RunResult := do
  let first ← SourceCoreUnifiedCorpusSupport.execute compiled name arguments fuel initial
  let result ← get "Syntax factory checkpoint resume" (SourceCoreUnifiedCompilation.Result.resume first 300000)
  pure result.observation

def run : IO Unit := do
 let compiled ← SourceCoreUnifiedCorpusSupport.prepare "Syntax factory annotation audit" content
   ["partialIf", "partialBoth", "totalIf", "blockFalls", "scopedValue", "faultBefore"]
 let prepared := compiled.indexed
 let diagnostic ← match prepared.base.diagnostics with
   | none => throw (IO.userError "annotation diagnostics missing") | some diagnostic => pure diagnostic.program
 let diagnostic := match prepared.base.callableContext with
   | none => diagnostic | some native => {diagnostic with rootTable := native.diagnostics.rootTable}
 let parents ← get "annotation contexts" (SourceCoreStageCodebook.prepareContexts prepared.base.sourceProgram prepared.base.plan
   (prepared.base.locals.bindings.flatMap (·.instances)))
 for named in prepared.base.functions do
  let source := CallableIndexedNamedGeneration.source named
  let own ← match diagnostic.base.find? named.signature.key with
    | none => throw (IO.userError "annotation own diagnostics missing") | some own => pure own
  let statements ← get "annotation roots" (source.roots.mapM (m := Except SourceCoreGeneralFunctions.Error) (fun
    | .statement id => pure id | .expression id => throw (.expectedStatementRoot id)))
  let body ← get "annotation actual body" (CallableIndexedNamedGeneration.bodyAction prepared named diagnostic parents own statements)
  IO.println s!"actual accepted body key={reprStr named.signature.key} result={reprStr named.signature.resultType}"
  let mut ifTypes : List TypeSystem.Ty := []
  for item in source.nodes do
   match item with
   | .statement node => match node.form with
     | .ifThen _ _ otherwise =>
       ifTypes := ifTypes ++ [node.type]
       IO.println s!"  if annotation={reprStr node.type} else={otherwise.isSome}"
     | .block _ => IO.println s!"  block annotation={reprStr node.type}"
     | _ => pure ()
   | _ => pure ()
  if some named.signature.key == compiled.keys[0]? then
    require (ifTypes == [.unit]) "partial if annotation is non-Unit"
  if some named.signature.key == compiled.keys[1]? then
    require (ifTypes.length == 3 && ifTypes.all (· == .unit)) "partial both annotation is non-Unit"
  if some named.signature.key == compiled.keys[2]? then
    require (ifTypes == [.word]) "total if annotation is not actual return type"
  if some named.signature.key == compiled.keys[4]? then
   let block ← match statements with
     | id :: _ => pure id | [] => throw (IO.userError "retained block root missing")
   let blockNode ← match source.lookupStatement? block with
     | some node => pure node | none => throw (IO.userError "retained block lookup missing")
   let inner ← match blockNode.form with
     | .block [inner] => pure inner | _ => throw (IO.userError "retained singleton block missing")
   let raw : TypedSource := {source with nodes := source.nodes.map fun
     | .statement node =>
       if node.id == block then .statement {node with type := .word}
       else if node.id == inner then match node.form with
         | .expression expression true => .statement {node with type := .word, form := .expression expression false}
         | _ => .statement node
       else .statement node
     | other => other}
   let retained : SourceCoreGeneralFunctions.Function := {named with specialized := {named.specialized with
     function := {named.specialized.function with typedBody := raw}}}
   let retainedBody ← get "retained ordinary non-Unit block actual bodyAction"
     (CallableIndexedNamedGeneration.bodyAction prepared retained diagnostic parents own statements)
   require (retainedBody == body) "retained ordinary non-Unit block changed actual code"
   IO.println "retained IR ordinary block: Word annotation + non-semicolon Word child, actual bodyAction accepted with identical emitted code"
 let initial : SourceTypedRuntime.RuntimeState := {heap := [⟨.word, some (.word (Word.ofNatModulo 811))⟩]}
 let scenarios := [("partialIf", 0, 17), ("partialIf", 1, 23),
     ("partialBoth", 0, 37), ("partialBoth", 2, 31), ("partialBoth", 3, 37),
     ("totalIf", 0, 41), ("totalIf", 1, 43), ("blockFalls", 0, 47), ("blockFalls", 1, 53),
     ("faultBefore", 1, 97)]
 for (name, seed, expected) in scenarios do
   let arguments := [SourceTypedRuntime.Value.word (Word.ofNatModulo seed)]
   let baseline ← finish compiled name arguments 300000 initial
   for fuel in [0, 1, 31, 300000] do
     let observed ← finish compiled name arguments fuel initial
     require (reprStr observed == reprStr baseline) s!"Syntax factory resume changed {name}"
     match observed with
     | .done value final =>
       require (reprStr value == reprStr (SourceTypedRuntime.Value.word (Word.ofNatModulo expected)))
         s!"Syntax factory result changed {name}"
       require (reprStr final.heap == reprStr (initial.heap ++ [⟨.word, some (.word (Word.ofNatModulo seed))⟩]))
         s!"Syntax factory complete ordered heap changed {name}"
     | other => throw (IO.userError s!"Syntax factory expected success {name}: {reprStr other}")
 for fuel in [0, 1, 31, 300000] do
   let observed ← finish compiled "faultBefore" [.word (Word.ofNatModulo 0)] fuel initial
   match observed with
   | .fault (.uninitializedLocal _) final =>
     require (reprStr final.heap == reprStr (initial.heap ++ [⟨.word, some (.word (Word.ofNatModulo 0))⟩, ⟨.word, none⟩]))
       "Syntax factory fault changed full heap or executed continuation"
   | other => throw (IO.userError s!"Syntax factory expected original fault: {reprStr other}")
 let baseline ← finish compiled "scopedValue" [] 300000 initial
 for fuel in [0, 1, 31, 300000] do
   let observed ← finish compiled "scopedValue" [] fuel initial
   require (reprStr observed == reprStr baseline) "ordinary scoped value resume changed"
   match observed with
   | .done value final =>
     require (reprStr value == reprStr (SourceTypedRuntime.Value.word (Word.ofNatModulo 67))) "ordinary scoped value result changed"
     require (reprStr final.heap == reprStr initial.heap) "ordinary scoped value changed full heap"
   | other => throw (IO.userError s!"ordinary scoped value expected success: {reprStr other}")
 IO.println "Syntax factory GREEN: six actual roots, ordinary/terminal annotation boundary, retained IR bodyAction/code Eq, full heap/fault/resume"

end Tests.SourceCoreRecursiveNamedImperativeMatchSyntax
end
