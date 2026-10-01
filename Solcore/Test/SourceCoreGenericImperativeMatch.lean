import Solcore.SourceSemantics.CoreLowering.GenericImperativeMatchCertificates
import Solcore.Test.SourceCompilerFeatureSupport

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
