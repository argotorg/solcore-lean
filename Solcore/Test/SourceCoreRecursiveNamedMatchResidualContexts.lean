import Solcore.SourceSemantics.CoreLowering.GenericImperativeMatchCertificates
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedSourceContextFacts
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedCatalogNativeContexts
import Solcore.Test.SourceCoreUnifiedCorpusSupport

/-! Match extraction uses the actual declaration context without changing its
residual flag. Source admission, child certificates, emitted native typing and
interpretation of the returned diagnostics remain independent static inputs.
The recursive named match meaning is a separate boundary. -/
#check_failure Solcore.Frontend.SourceTypedRuntime.run
set_option autoImplicit false
namespace Tests.SourceCoreRecursiveNamedMatchResidualContexts
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open GenericImperativeMatch

section ActualHeader
variable {checked : CallableAncestryPairedLookup.Checked} {base : CallableAncestryPairedLookup.Base checked}
  {prepared : SourceCoreCallableIndexedAncestry.Prepared base}
  {values : SourceCoreCompatibleValues.Context} {ambient : AmbientDefinitions values.checked.catalog.definitions}
  {program : SourceSemantics.Program} {header : RecursiveNamedCatalog.Header prepared values ambient.definitions program}
  {administrative : Core.Context} {expressionSyntax : ExpressionId → Prop}
  {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {matchCompilation : SourceCoreCompatibleDataMatches.Context}
  {invalidProjection : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Word}
  {invalidOperand : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Solcore.Syntax.ValueAssignOp → Word}
  {invalidUnary : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Word}
  {missingDefault : SourceCoreElaboration.ErrorSite → Resolved.LocalId → TypeSystem.Ty → Word}

/-- The real Header supplies lexical closure and residual=true. No false
context or source execution is used to reach the one extraction traversal. -/
theorem actual_header_extraction (diagnosticPolicy : AssignmentDiagnosticPolicy) {tracked : Bool}
    (factory : AssignmentDiagnosticOrigins.Factory tracked diagnosticPolicy header.function.source invalidOperand)
    (matchPolicy : header.policy.lowerMatch = some (SourceCoreCompatibleDataMatches.lowerWithReasons matchCompilation))
    (matchValues : matchCompilation.values = values)
    (matchDefinitions : matchCompilation.definitions = ambient.definitions)
    (matchAllocator : matchCompilation.sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator prepared.layout.frame header.globals
      (header.layouts.allocatorAt header.owner header.active header.onError)))
    (hidden : MatchHiddenFresh header.function.source)
    (readPolicy : header.policy.readStatement = SourceCoreCompatibleDataExpressions.readStatement values.checked)
    (binderPolicy : ∀ scope binder, binder.scheme.quantified = [] →
      header.policy.lowerBinder header.function.source scope binder = SourceCoreCompatibleDataExpressions.lowerBinder values.checked header.function.source scope binder)
    (allocationPolicy : header.policy.sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator prepared.layout.frame header.globals
      (header.layouts.allocatorAt header.owner header.active header.onError)))
    (expressions : ∀ sourceContext, sourceContext.typeVariables = [] → sourceContext.residualTypeVariables = true →
      sourceContext.signatures = values.checked.signatures →
      ∀ {scope fuel id node lowered}, CompatibleExpressionReads.ScopeDeclarations header.function.source scope sourceContext → expressionSyntax id →
      header.function.source.lookupExpression? id = some node → ExpressionHasType header.function.source sourceContext id node.type →
      header.policy.lowerExpression fuel header.function.source scope id header.reasonAt = .ok lowered →
      certificates sourceContext scope id lowered)
    (assignments : CompatibleAssignmentStatements.AssignmentPolicy header.policy values invalidProjection invalidOperand missingDefault)
    (unaryPolicy : CompatibleBitNotStatements.Policy header.policy values invalidProjection invalidUnary missingDefault)
    (assignmentExpressions : ∀ sourceContext scope fuel id lowered,
      sourceContext.typeVariables = [] → sourceContext.residualTypeVariables = true →
      sourceContext.signatures = values.checked.signatures →
      CompatibleExpressionReads.ScopeDeclarations header.function.source scope sourceContext →
      expressionSyntax id → ∀ node, header.function.source.lookupExpression? id = some node →
      ExpressionHasType header.function.source sourceContext id node.type →
      header.policy.lowerExpression fuel header.function.source scope id header.reasonAt = .ok lowered →
        certificates sourceContext scope id lowered ∧
        HasType (SourceCoreLocalCell.coreContext scope ++ administrative) lowered.expression
          (LanguageResult.resultType lowered.type) ambient.definitions)
    (syntaxTree : Syntax header.function.source expressionSyntax header.context (.statements true header.function.body) header.function.resultType)
    (sourceSignatures : header.context.signatures = values.checked.signatures)
    (declarations : CompatibleExpressionReads.ScopeDeclarations header.function.source (RecursiveNamedCatalogNativeContexts.bodyScope header) header.context)
    {nativeType : Ty}
    (projection : values.checked.catalog.project header.function.resultType = .ok header.output)
    (accepted : SourceCoreLoops.lowerStatementsWithPolicy header.policy header.fuel header.function.source (RecursiveNamedCatalogNativeContexts.bodyScope header) header.function.body header.output header.reasonAt header.fellThrough header.escaped = .ok header.body)
    (nativeTyped : HasType (SourceCoreLocalCell.coreContext (RecursiveNamedCatalogNativeContexts.bodyScope header) ++ administrative) header.body nativeType ambient.definitions) :
    ∃ flow,
      SourceCoreLoops.lowerFlowStatementsWithPolicy header.policy header.fuel header.function.source (RecursiveNamedCatalogNativeContexts.bodyScope header) header.function.body header.output header.reasonAt true header.escaped = .ok flow ∧
      ∃ _extracted : ExtractionFor diagnosticPolicy header.layouts header.owner header.active prepared.layout.frame header.globals header.onError values header.function.source expressionSyntax certificates ambient.definitions administrative matchCompilation.solvedRequirements
        header.context (RecursiveNamedCatalogNativeContexts.bodyScope header) (.statements true header.function.body) header.function.resultType header.output flow,
      header.body = LocalControl.finish header.output (LocalLoop.toControl header.output flow header.escaped)
        (if header.output = .unit then LanguageResult.success .unit else LanguageResult.failure header.output (.word header.fellThrough)) := by
  exact extraction_of_typed_body_with_residual true diagnosticPolicy factory matchPolicy matchValues matchDefinitions matchAllocator
    (MatchChildStatic.of_hidden hidden) readPolicy binderPolicy allocationPolicy expressions assignments unaryPolicy header.unique
    assignmentExpressions syntaxTree (RecursiveNamedSourceContextFacts.header_typeVariables header)
    (RecursiveNamedSourceContextFacts.header_residual header) sourceSignatures declarations projection accepted nativeTyped

/-- Only the returned receipt's own diagnostics construct its matching Ready. -/
theorem actual_ready {diagnosticPolicy : AssignmentDiagnosticPolicy} {flow : Expr}
    {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
    (receipt : ExtractionFor diagnosticPolicy header.layouts header.owner header.active prepared.layout.frame header.globals
      header.onError values header.function.source expressionSyntax certificates ambient.definitions administrative matchCompilation.solvedRequirements
      header.context (RecursiveNamedCatalogNativeContexts.bodyScope header) (.statements true header.function.body)
      header.function.resultType header.output flow)
    (sourceSignatures : header.context.signatures = values.checked.signatures)
    (sameLedger : matchCompilation.solvedRequirements = header.solved)
    (interpreted : receipt.diagnostics registry faults) : Tree.ReadyFor diagnosticPolicy registry faults receipt.tree := by
  obtain ⟨errors, ledgers⟩ := receipt.materialize registry faults interpreted
  exact ledgers.ready (by simpa only [sameLedger] using header.valid) sourceSignatures

theorem actual_header_context : header.context.typeVariables = [] ∧ header.context.residualTypeVariables = true :=
  RecursiveNamedSourceContextFacts.header_fields header

theorem old_false_excluded : header.context.residualTypeVariables ≠ false :=
  RecursiveNamedSourceContextFacts.header_not_false header
end ActualHeader

/-- Both arm binder extension and default preserve the source residual flag. -/
theorem scoped_context_mode {source : TypedSource} {parent child : SourceSemantics.Context}
    {hidden : List Resolved.LocalId} {type : TypeSystem.Ty} {cases : List TypedMatchCase}
    {fallback : Option (List StatementId)} {request : GenericMatchChildren.Request} {mode : Bool}
    (context : GenericMatchChildren.ScopedContextFor source parent hidden type cases fallback request child)
    (same : parent.residualTypeVariables = mode) : child.residualTypeVariables = mode :=
  context.closed_fields.2.2.trans same

section DuplicateArms
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
private def context : SourceSemantics.Context := (SourceSemantics.Context.ofSignatures signatures).withResidualTypeVariables
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
  have admitted : TypeAdmissible context .unit := .unit (by simp [TypeParameterBindersWellFormed, context, Context.ofSignatures, Context.withResidualTypeVariables])
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
  (expressions : ∀ sourceContext, sourceContext.typeVariables = [] → sourceContext.residualTypeVariables = true →
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
    sourceContext.typeVariables = [] → sourceContext.residualTypeVariables = true →
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
  obtain ⟨receipt⟩ := GenericImperativeMatch.extraction_of_typed_flow_with_residual true .unconditional
    (AssignmentDiagnosticOrigins.Factory.unchanged .unconditional source invalidOperand) matchPolicy matchValues matchDefinitions matchAllocator (GenericImperativeMatch.MatchChildStatic.of_hidden hiddenSourceFresh)
    readPolicy binderPolicy allocationPolicy expressions assignments unaryPolicy unique assignmentExpressions
    (syntaxTree mode) rfl rfl rfl declarations (by cbv) flowAccepted (infer_sound nativeTyped)
  exact receipt.tree
end ActualFlow

end DuplicateArms


private def content : String := String.intercalate "\n" [
  "function choose(n: Word) returns (Word) { let result = 0; match (n) { case 0 { result = 5; } default { result = 7; } } return result; }",
  "function branch(n: Word) returns (Word) { match (n) { case 0 { { return 11; } } default { if (true) { return 13; } else { return 17; } } } return 19; }",
  "function loop(n: Word) returns (Word) { let result = 0; for (let i = 0; i < n; i += 1) { match (i) { case 0 { continue; } default { result += i; } } } return result; }",
  "function keyed(m: mapping(Bool => Word)) returns (Word) { match (m[true]) { case 31 { m[true] = 7; } default { m[false] = 9; } } return m[true]; }",
  "function fail(n: Word) returns (Word) { let result = 29; let gap: Word; match (n) { case 0 { result = 31; return gap; } default { result = 37; } } return result; }"
]
private def require := SourceCoreUnifiedCorpusSupport.assertTrue
private def get {α ε : Type} [Repr ε] := @SourceCoreUnifiedCorpusSupport.get α ε _
private def w (n : Nat) : SourceTypedRuntime.Value := .word (Word.ofNatModulo n)
private def finish (compiled : SourceCoreUnifiedCompilation.Compiled) (name : String)
    (arguments : List SourceTypedRuntime.Value) (fuel : Nat) (initial : SourceTypedRuntime.RuntimeState) : IO SourceTypedRuntime.RunResult := do
  let first ← SourceCoreUnifiedCorpusSupport.execute compiled name arguments fuel initial
  pure (← get "match declaration context resume" (first.resume 300000)).observation
private def cells (initial final : SourceTypedRuntime.RuntimeState)
    (expected : List (TypeSystem.Ty × Option SourceTypedRuntime.Value)) (label : String) : IO Unit := do
  require (reprStr (final.heap.take initial.heap.length) == reprStr initial.heap) s!"match context prefix changed {label}"
  require (reprStr ((final.heap.drop initial.heap.length).map (fun cell => (cell.type, cell.value))) == reprStr expected)
    s!"match context ordered cells changed {label}: {reprStr final.heap}"

def run : IO Unit := do
  let compiled ← SourceCoreUnifiedCorpusSupport.prepare "actual match declaration contexts" content
    ["choose", "branch", "loop", "keyed", "fail"]
  for named in compiled.indexed.base.functions do
    let context := declarationContext compiled.sourceProgram.signatures named.specialized.key.declaration []
      named.specialized.assumptions named.specialized.function.solvedRequirements
    require (context.residualTypeVariables && context.typeVariables.isEmpty) "real declaration context flags changed"
  let mapping : SourceTypedRuntime.Value := .mapping .bool .word [(.bool true, w 31), (.bool true, w 91), (.bool false, w 4)]
  let updated : SourceTypedRuntime.Value := .mapping .bool .word [(.bool true, w 7), (.bool true, w 91), (.bool false, w 4)]
  let tests : List (String × List SourceTypedRuntime.Value × SourceTypedRuntime.Value × List (TypeSystem.Ty × Option SourceTypedRuntime.Value)) := [
    ("choose", [w 0], w 5, [(.word, some (w 0)), (.word, some (w 5)), (.word, some (w 0))]),
    ("choose", [w 3], w 7, [(.word, some (w 3)), (.word, some (w 7)), (.word, some (w 3))]),
    ("branch", [w 0], w 11, [(.word, some (w 0)), (.word, some (w 0))]),
    ("branch", [w 2], w 13, [(.word, some (w 2)), (.word, some (w 2))]),
    ("loop", [w 3], w 3, [(.word, some (w 3)), (.word, some (w 3)), (.word, some (w 3)), (.word, some (w 0)), (.word, some (w 1)), (.word, some (w 2))]),
    ("keyed", [mapping], w 7, [(.mapping .bool .word, some updated), (.word, some (w 31))]),
    ("fail", [w 3], w 37, [(.word, some (w 3)), (.word, some (w 37)), (.word, none), (.word, some (w 3))])]
  let initial : SourceTypedRuntime.RuntimeState := {heap := [⟨.word, some (w 819)⟩, ⟨.bool, some (.bool false)⟩]}
  let baselines ← tests.mapM (fun test => finish compiled test.1 test.2.1 300000 initial)
  let failed ← finish compiled "fail" [w 0] 300000 initial
  for fuel in [0, 7, 43, 300000] do
    for (test, baseline) in tests.zip baselines do
      let (name, arguments, expected, expectedCells) := test
      let observed ← finish compiled name arguments fuel initial
      require (reprStr observed == reprStr baseline) s!"match context public resume changed {name}"
      match observed with
      | .done actual final =>
        require (reprStr actual == reprStr expected) s!"match context result changed {name}"
        cells initial final expectedCells name
      | _ => throw (IO.userError s!"match context expected success {name}")
    let observed ← finish compiled "fail" [w 0] fuel initial
    require (reprStr observed == reprStr failed) "match context first fault/resume changed"
    match observed with
    | .fault (.uninitializedLocal _) final =>
      cells initial final [(.word, some (w 0)), (.word, some (w 31)), (.word, none), (.word, some (w 0))] "fail"
    | _ => throw (IO.userError "match context first fault lost")
  IO.println "match residual contexts: real true scopes, branch/default, terminal blocks/ifs, for-post, mapping order, fault cells/resume GREEN"
end Tests.SourceCoreRecursiveNamedMatchResidualContexts
