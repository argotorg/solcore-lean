import Solcore.SourceSemantics.SourceCompiledGeneralizedMatchEntry
import Solcore.SourceSemantics.SourceCompiledGeneralizedStatementInvariant

set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledGeneralizedSoundness
open Frontend SourceInference TypeSystem SourceInferenceSoundness
open SourceCompiledLocalFinalization SourceInferenceStatementsSoundness ProtectedVariables

theorem statement_match_without_default
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
    (defaultEq : arms.value.defaultBody = none)
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
  obtain ⟨scrutinee, scrutineeState, hiddenScrutinee, hiddenState, checked,
      scrutineeAccepted, hiddenAllocation, casesAccepted, guardPassed, resultEq, contains⟩ :=
    inferStatementFuel_success_matchWithoutDefault_facts form defaultEq rfl boundary.accepted (bodyRoots selected)
  have casesExtension : selected.body.finalized.substitution.SemanticallyExtends checked.state.inference.substitution := by
    simpa [resultEq, State.recordNode] using boundary.extension
  have casesSource : TypingSourceExtends (checked.state.toTypedSource (bodyRoots selected))
      (result.state.toTypedSource (bodyRoots selected)) := by
    rw [resultEq]
    exact ⟨rfl, List.prefix_append _ _⟩
  have patterns : checked.state.integerPatterns ⊆ selected.body.returned.integerPatterns := by
    simpa [resultEq, State.recordNode] using boundary.integerPatterns
  have literals : checked.state.integerLiterals ⊆ selected.body.returned.integerLiterals := by
    simpa [resultEq, State.recordNode] using boundary.integerLiterals
  have requirements : checked.state.requirements ⊆ selected.body.returned.requirements := by
    simpa [resultEq, State.recordNode] using boundary.requirements
  obtain ⟨casesBoundary, scrutineeTyping, hiddenSafe⟩ :=
    matchEntry checkedProgram recursiveExpression boundary returnSafe scrutineeAccepted hiddenAllocation
      casesAccepted casesExtension casesSource patterns literals requirements contains
  obtain ⟨casesInvariant, casesActual, casesOperational, caseFacts, casesTyping, allReturnEq⟩ :=
    matchCases checkedProgram casesBoundary hiddenSafe returnAdmissible
      (fun small less => recursiveBody small (Nat.lt_trans less (Nat.lt_succ_self childFuel)))
  have casesNonempty : checked.cases ≠ [] := by
    intro empty
    have wildcardFalse : checked.hasWildcard = false := by
      cases wildcard : checked.hasWildcard with
      | false => rfl
      | true =>
        obtain ⟨arm, member, _⟩ := Detail.inferMatchCasesFuel_success_hasWildcard_member casesAccepted wildcard
        simp [empty] at member
    have nominalFalse : Detail.exhaustsNominalConstructors inferenceContext checked.state
        scrutinee.type checked.cases = false := by simp [empty, Detail.exhaustsNominalConstructors]
    simp [wildcardFalse, nominalFalse] at guardPassed
  have factsNonempty := matchCasesHaveType_facts_ne_nil_of_cases_ne_nil casesTyping (by simpa using casesNonempty)
  obtain ⟨summary, merged⟩ := mergeBodyControls_withoutDefault_eq_some_of_ne_nil caseFacts factsNonempty
  have signatures : target.signatures = inferenceContext.signatures :=
    boundary.invariant.signaturesEq.trans boundary.scope.signatures.symm
  have catalog : SignatureCatalogWellFormed target.signatures := signatures ▸ boundary.scope.catalog checkedProgram
  have exhaustive := matchExhaustiveWithoutDefault_of_guard catalog signatures casesAccepted casesTyping
    scrutineeTyping.type_admissible casesExtension guardPassed
  let facts : StatementFacts := {
    type := if allBodiesSawReturn caseFacts then selected.body.finalized.substitution.apply expectedReturn else .unit
    hasValue := allBodiesSawReturn caseFacts
    sawReturn := allBodiesSawReturn caseFacts
    control := summary.eraseValue }
  have finalContains := (boundary.rawSubtree.finalized selected.body.resources).containsStatement contains
  have resolvedFinal : selected.body.finalized.substitution.apply (checked.state.resolve expectedReturn) =
      selected.body.finalized.substitution.apply expectedReturn := by
    simpa [State.resolve, InferState.resolve] using casesExtension expectedReturn
  have typeEq : selected.body.finalized.substitution.apply result.type = facts.type := by
    simp only [resultEq]
    change selected.body.finalized.substitution.apply
      (if checked.allReturn then checked.state.resolve expectedReturn else .unit) = _
    dsimp [facts]
    rw [allReturnEq]
    cases checked.allReturn <;> simp [resolvedFinal]
  have typing : StatementHasType selected.body.finalized.typedSource
      { returnType := selected.body.finalized.substitution.apply expectedReturn, loopDepth := inferenceContext.loopDepth }
      target result.id target facts := by
    exact .matchWithoutDefault finalContains rfl rfl scrutineeTyping casesTyping
      (by simp [MatchResolution.applySubstitution]) exhaustive merged typeEq
  have agreement : StatementResultMatchesFactsAfterSubstitution selected.body.finalized.substitution result facts := by
    rw [resultEq]
    exact StatementResultMatchesFactsAfterSubstitution.matchWithoutDefault allReturnEq casesExtension _ _
  have active : ActiveLocalContextInvariant result.state selected.body.finalized.substitution target := by
    rw [resultEq]
    exact casesInvariant.active.recordNode _
  have operational : GeneralizedActualStateInvariant result.state (evidenceSource selected) := by
    rw [resultEq]
    exact casesOperational.recordStatement _ rfl
  have isolation : ActiveSchemeQuantifierIsolation result.state := by
    rw [resultEq]
    exact casesInvariant.schemeIsolation
  have invariant := boundary.invariant.of_retained_statement_typing boundary.accepted
    (boundary.scope.formation checkedProgram) (boundary.scope.functionsCanonical checkedProgram) active
    (inferStatementFuel_preserves_localBindersBelowNextLocal boundary.invariant.bindersBelow boundary.accepted)
    boundary.extension isolation typing
  exact ⟨target, facts, invariant, casesActual, operational, typing, agreement⟩

end Solcore.SourceSemantics.SourceCompiledGeneralizedSoundness
