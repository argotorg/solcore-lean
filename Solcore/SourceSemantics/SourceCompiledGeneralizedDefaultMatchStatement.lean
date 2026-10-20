import Solcore.SourceSemantics.SourceCompiledGeneralizedMatchStatement
import Solcore.SourceSemantics.SourceCompiledGeneralizedStatementInvariant

set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledGeneralizedSoundness
open Frontend SourceInference TypeSystem SourceInferenceSoundness
open SourceCompiledLocalFinalization SourceInferenceStatementsSoundness ProtectedVariables

theorem statement_match_with_default
    {raw : Workspace.RawWorkspace} {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel childFuel : Nat}
    {selected : Selected compiled row fuel}
    (checkedProgram : Frontend.checkProgram raw fuel = .ok compiled.program)
    (recursiveExpression : ∀ smaller, smaller < childFuel + 1 → ExpressionRetainedSoundness selected smaller)
    {inferenceContext : SourceInference.Context} {statement : Syntax.Statement}
    {scrutinees : Syntax.NonemptyDelimitedList Syntax.Expr} {arms : Syntax.MatchArms}
    {defaultBody : Syntax.Block} {expectedReturn : Ty} {initial : State} {result : Detail.StatementResult}
    {frames : List InitializedLetBinding} {target : SourceSemantics.Context}
    (form : statement.value = .matchWith scrutinees arms)
    (defaultEq : arms.value.defaultBody = some defaultBody)
    (boundary : StatementBoundary selected (childFuel + 1) inferenceContext statement
      expectedReturn initial result frames target)
    (returnSafe : ∀ binder ∈ initial.localBinders, Safe binder.scheme.quantified initial expectedReturn)
    (returnAdmissible : TypeAdmissible target (selected.body.finalized.substitution.apply expectedReturn))
    (recursiveBody : ∀ small, small < childFuel + 1 →
      ∀ {bodySource : List Syntax.Statement} {bodyInitial : State} {bodyResult : Detail.BlockResult}
        {bodyTarget : SourceSemantics.Context},
        (∀ binder ∈ bodyInitial.localBinders, Safe binder.scheme.quantified bodyInitial expectedReturn) →
        TypeAdmissible bodyTarget (selected.body.finalized.substitution.apply expectedReturn) →
        StatementsBoundary selected small inferenceContext bodySource expectedReturn
          bodyInitial bodyResult frames bodyTarget →
        StatementsConclusion selected inferenceContext expectedReturn bodyResult frames bodyTarget) :
    StatementConclusion selected inferenceContext expectedReturn result frames target := by
  obtain ⟨scrutinee, scrutineeState, hiddenScrutinee, hiddenState, checked, defaultResult,
      scrutineeAccepted, hiddenAllocation, casesAccepted, defaultAccepted, _guard, resultEq, contains⟩ :=
    inferStatementFuel_success_matchWithDefault_facts form defaultEq rfl boundary.accepted (bodyRoots selected)
  have formation := boundary.scope.formation checkedProgram
  have canonical := boundary.scope.functionsCanonical checkedProgram
  have catalog := boundary.scope.catalog checkedProgram
  have allocatedInvariant := boundary.invariant.allocateStatementId rfl
  have scrutineeProperties := inferMatchScrutineesFuel_inferenceProperties allocatedInvariant.ready formation canonical scrutineeAccepted
  have hiddenEq : scrutineeState.allocateHiddenLocal.2 = hiddenState := congrArg Prod.snd hiddenAllocation
  have hiddenReady : hiddenState.InferenceReady := by
    rw [← hiddenEq]
    exact scrutineeProperties.2.1.allocateHiddenLocal
  have scrutineeBelow : scrutinee.type.VariablesBelow hiddenState.inference.next := by
    rw [← hiddenEq]
    exact scrutineeProperties.2.2
  have returnBelow : expectedReturn.VariablesBelow hiddenState.inference.next := by
    rw [← hiddenEq]
    exact allocatedInvariant.returnBelow.weaken scrutineeProperties.1.next_le
  have casesProperties := Detail.inferMatchCasesFuel_inferenceProperties hiddenReady formation canonical
    scrutineeBelow returnBelow rfl casesAccepted
  have defaultProperties := Detail.inferStatementsFuel_inferenceProperties casesProperties.2.1 formation canonical
    (returnBelow.weaken casesProperties.1.next_le) defaultAccepted
  have defaultExtension : selected.body.finalized.substitution.SemanticallyExtends defaultResult.state.inference.substitution := by
    simpa [resultEq, State.recordNode, State.restoreLexicalScope] using boundary.extension
  have casesExtension := defaultExtension.trans defaultProperties.1.substitution_extends
  have hiddenNodes : hiddenState.NodesBelowNextOccurrence := by
    rw [← hiddenEq]
    exact State.allocateHiddenLocal_preserves_nodesBelowNextOccurrence _
      (inferMatchScrutineesFuel_success_nodesBelow scrutineeAccepted allocatedInvariant.nodesBelow)
  have casesNodes := (Detail.inferMatchCasesFuel_occurrenceBoundExtends casesAccepted).nodesBelowNextOccurrence hiddenNodes
  have defaultSource : TypingSourceExtends (defaultResult.state.toTypedSource (bodyRoots selected))
      (result.state.toTypedSource (bodyRoots selected)) := by
    rw [resultEq]
    exact ⟨rfl, List.prefix_append _ _⟩
  have casesSource := (inferStatementsFuel_success_typingSourceExtends defaultAccepted casesNodes (bodyRoots selected)).trans defaultSource
  have defaultPatterns : defaultResult.state.integerPatterns ⊆ selected.body.returned.integerPatterns := by
    simpa [resultEq, State.recordNode, State.restoreLexicalScope] using boundary.integerPatterns
  have defaultLiterals : defaultResult.state.integerLiterals ⊆ selected.body.returned.integerLiterals := by
    simpa [resultEq, State.recordNode, State.restoreLexicalScope] using boundary.integerLiterals
  have defaultRequirements : defaultResult.state.requirements ⊆ selected.body.returned.requirements := by
    simpa [resultEq, State.recordNode, State.restoreLexicalScope] using boundary.requirements
  obtain ⟨casesBoundary, scrutineeTyping, hiddenSafe⟩ :=
    matchEntry checkedProgram recursiveExpression boundary returnSafe scrutineeAccepted hiddenAllocation
      casesAccepted casesExtension casesSource
      ((Detail.inferStatementsFuel_integerPatterns_subset defaultAccepted).trans defaultPatterns)
      ((Detail.inferStatementsFuel_integerLiterals_subset defaultAccepted).trans defaultLiterals)
      ((Detail.inferStatementsFuel_requirements_subset defaultAccepted).trans defaultRequirements) contains
  obtain ⟨casesInvariant, casesActual, casesOperational, caseFacts, casesTyping, allReturnEq⟩ :=
    matchCases checkedProgram casesBoundary hiddenSafe returnAdmissible
      (fun small less => recursiveBody small (Nat.lt_trans less (Nat.lt_succ_self childFuel)))
  have casesScope : checked.state.lexicalScope = hiddenState.lexicalScope :=
    Detail.inferMatchCasesFuel_success_lexicalScope_eq rfl casesAccepted
  have defaultSafe : ∀ binder ∈ checked.state.localBinders,
      Safe binder.scheme.quantified checked.state expectedReturn := by
    apply safe_active_iff.mp
    have privacy := inferMatchCasesFuel_private (activeSchemeQuantifiers hiddenState) childFuel
      inferenceContext scrutinee.type expectedReturn hiddenState.lexicalScope arms.value.cases hiddenState
      casesBoundary.invariant.ready casesBoundary.operational.requirements
      (activeSchemeQuantifiers_below_next casesBoundary.operational.quantifiersBelow)
      casesBoundary.operational.privacy.all_live catalog formation canonical scrutineeBelow
      casesBoundary.scrutineeSafe returnBelow hiddenSafe rfl _ casesAccepted
    have binders : checked.state.localBinders = hiddenState.localBinders := congrArg LexicalScope.binders casesScope
    simpa only [activeSchemeQuantifiers, binders] using privacy.1 expectedReturn hiddenSafe
  have finalContains := (boundary.rawSubtree.finalized selected.body.resources).containsStatement contains
  have reference : ∀ child ∈ defaultResult.statements,
      (.statement child : NodeId) ∈ (StatementForm.matchWith {
        scrutinee := scrutinee.id, hiddenScrutinee, cases := checked.cases,
        defaultBody := some defaultResult.statements,
        requirements := checked.cases.flatMap (·.pattern.requirements) }).references := by
    intro child member
    simp only [StatementForm.references, MatchResolution.references]
    apply List.mem_append_right
    simpa using (List.mem_map.mpr ⟨child, member, rfl⟩ : NodeId.statement child ∈ defaultResult.statements.map NodeId.statement)
  obtain ⟨defaultContext, defaultFacts, _, _, defaultOperational, defaultTyping, defaultAgreement⟩ :=
    recursiveBody childFuel (Nat.lt_succ_self _) defaultSafe returnAdmissible ({
      accepted := defaultAccepted, interfaces := boundary.interfaces, extension := defaultExtension
      scope := boundary.scope, invariant := casesInvariant, actual := casesActual, operational := casesOperational
      rawSubtrees := fun child member =>
        (boundary.rawSubtree.child (directChild_statement_reference contains (reference child member))).monoBefore defaultSource
      integerPatterns := defaultPatterns, integerLiterals := defaultLiterals, requirements := defaultRequirements
      covered := fun child member => TemplateScopeCovered.statementChild boundary.covered selected.body.resources.graph_closed
        ((boundary.rawSubtree.finalized selected.body.resources).directChild
          (directChild_statement_reference contains (reference child member))) (fun _ member => member)
      actualCovered := fun child member => boundary.actualCovered.preserved_statement_reference contains
        (boundary.rawSubtree.finalized selected.body.resources) (reference child member) } :
      StatementsBoundary selected childFuel inferenceContext defaultBody.value expectedReturn
        checked.state defaultResult frames target)
  obtain ⟨summary, merged⟩ := mergeBodyControls_withDefault_eq_some caseFacts defaultFacts
  let facts : StatementFacts := {
    type := if allBodiesSawReturn caseFacts && defaultFacts.sawReturn then selected.body.finalized.substitution.apply expectedReturn else .unit
    hasValue := allBodiesSawReturn caseFacts && defaultFacts.sawReturn
    sawReturn := allBodiesSawReturn caseFacts && defaultFacts.sawReturn
    control := summary.eraseValue }
  have resolvedFinal : selected.body.finalized.substitution.apply (defaultResult.state.resolve expectedReturn) =
      selected.body.finalized.substitution.apply expectedReturn := by
    simpa [State.resolve, InferState.resolve] using defaultExtension expectedReturn
  have typeEq : selected.body.finalized.substitution.apply result.type = facts.type := by
    simp only [resultEq]
    change selected.body.finalized.substitution.apply
      (if checked.allReturn && defaultResult.sawReturn then defaultResult.state.resolve expectedReturn else .unit) = _
    dsimp [facts]
    rw [allReturnEq, defaultAgreement.sawReturn_eq]
    cases checked.allReturn <;> cases defaultResult.sawReturn <;> simp [resolvedFinal]
  have typing : StatementHasType selected.body.finalized.typedSource
      { returnType := selected.body.finalized.substitution.apply expectedReturn, loopDepth := inferenceContext.loopDepth }
      target result.id target facts := by
    exact .matchWithDefault finalContains rfl rfl scrutineeTyping casesTyping defaultTyping
      (by simp [MatchResolution.applySubstitution]) merged typeEq
  have agreement : StatementResultMatchesFactsAfterSubstitution selected.body.finalized.substitution result facts := by
    rw [resultEq]
    exact StatementResultMatchesFactsAfterSubstitution.matchWithDefault allReturnEq defaultAgreement defaultExtension _ _
  have active : ActiveLocalContextInvariant result.state selected.body.finalized.substitution target := by
    rw [resultEq, ← casesScope]
    exact casesInvariant.active.restoreLexicalScope_recordNode _
  have operational : GeneralizedActualStateInvariant result.state (evidenceSource selected) := by
    rw [resultEq, ← casesScope]
    exact (defaultOperational.restoreSaved casesOperational.origins
      (ProtectedVariables.inferStatementsFuel_binders_subset defaultAccepted)).recordStatement _ rfl
  have isolation : ActiveSchemeQuantifierIsolation result.state := by
    rw [resultEq, ← casesScope]
    exact casesInvariant.schemeIsolation
  have invariant := boundary.invariant.of_retained_statement_typing boundary.accepted formation canonical active
    (inferStatementFuel_preserves_localBindersBelowNextLocal boundary.invariant.bindersBelow boundary.accepted)
    boundary.extension isolation typing
  exact ⟨target, facts, invariant, casesActual, operational, typing, agreement⟩

theorem statement_match
    {raw : Workspace.RawWorkspace} {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel childFuel : Nat}
    {selected : Selected compiled row fuel}
    (checkedProgram : Frontend.checkProgram raw fuel = .ok compiled.program)
    (recursiveExpression : ∀ smaller, smaller < childFuel + 1 → ExpressionRetainedSoundness selected smaller)
    {inferenceContext : SourceInference.Context} {statement : Syntax.Statement}
    {scrutinees : Syntax.NonemptyDelimitedList Syntax.Expr} {arms : Syntax.MatchArms}
    {expectedReturn : Ty} {initial : State} {result : Detail.StatementResult}
    {frames : List InitializedLetBinding} {target : SourceSemantics.Context}
    (form : statement.value = .matchWith scrutinees arms)
    (boundary : StatementBoundary selected (childFuel + 1) inferenceContext statement
      expectedReturn initial result frames target)
    (returnSafe : ∀ binder ∈ initial.localBinders, Safe binder.scheme.quantified initial expectedReturn)
    (returnAdmissible : TypeAdmissible target (selected.body.finalized.substitution.apply expectedReturn))
    (recursiveBody : ∀ small, small < childFuel + 1 →
      ∀ {bodySource : List Syntax.Statement} {bodyInitial : State} {bodyResult : Detail.BlockResult}
        {bodyTarget : SourceSemantics.Context},
        (∀ binder ∈ bodyInitial.localBinders, Safe binder.scheme.quantified bodyInitial expectedReturn) →
        TypeAdmissible bodyTarget (selected.body.finalized.substitution.apply expectedReturn) →
        StatementsBoundary selected small inferenceContext bodySource expectedReturn
          bodyInitial bodyResult frames bodyTarget →
        StatementsConclusion selected inferenceContext expectedReturn bodyResult frames bodyTarget) :
    StatementConclusion selected inferenceContext expectedReturn result frames target := by
  cases defaultEq : arms.value.defaultBody with
  | none =>
    exact statement_match_without_default checkedProgram recursiveExpression form defaultEq boundary
      returnSafe returnAdmissible recursiveBody
  | some defaultBody =>
    exact statement_match_with_default checkedProgram recursiveExpression form defaultEq boundary
      returnSafe returnAdmissible recursiveBody

end Solcore.SourceSemantics.SourceCompiledGeneralizedSoundness
