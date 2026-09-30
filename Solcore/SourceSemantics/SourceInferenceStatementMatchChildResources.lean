import Solcore.SourceSemantics.SourceInferenceStatementMatchAssembly

/-!
Resource transport along the actual source-ordered children of a `match`
statement.  Child typing uses the whole final substitution and evidence
ledgers, so it needs these facts before applying scoped induction hypotheses.
-/

set_option autoImplicit false

namespace Solcore.SourceSemantics.SourceInferenceSoundness

open Frontend Frontend.SourceInference TypeSystem
open SourceInferenceStatementsSoundness

/-- In a successful default-free match, the scrutinee and explicit cases are
prefixes of the parent result.  Finalization extends their substitutions and
the parent retains their literal and requirement ledgers. -/
theorem inferStatementFuel_success_matchWithoutDefault_child_resources
    {fuel : Nat}
    {wholeContext inferenceContext : Frontend.SourceInference.Context}
    {statement : Syntax.Statement}
    {scrutinees : Syntax.NonemptyDelimitedList Syntax.Expr}
    {arms : Syntax.MatchArms} {expectedReturn : Ty}
    {initial allocated : State} {id : StatementId}
    {result : Detail.StatementResult}
    {finalized : Frontend.SourceInference.Result}
    {semanticContext : SourceSemantics.Context}
    (statementEq : statement.value = .matchWith scrutinees arms)
    (defaultEq : arms.value.defaultBody = none)
    (allocationEq : initial.allocateStatementId = (id, allocated))
    (success : Detail.inferStatementFuel (fuel + 1) inferenceContext
      statement expectedReturn initial = .ok result)
    (signatureFormation :
      ProgramSignatureFormationValidated inferenceContext.signatures)
    (functionsCanonical : ∀ candidate ∈
      inferenceContext.signatures.functions,
      candidate.scheme.body = .function
        (Ty.productMany candidate.parameterTypes)
        (Ty.productMany candidate.returnTypes))
    (initialInvariant : RecursiveStatementInvariant wholeContext
      expectedReturn finalized initial semanticContext)
    (resultSubstitutionExtension : finalized.substitution.SemanticallyExtends
      result.state.inference.substitution)
    (roots : List NodeId) :
    ∃ scrutinee scrutineeState hiddenScrutinee hiddenState checked,
      inferMatchScrutineesFuel fuel inferenceContext statement.span
        scrutinees.elements.toList allocated =
          .ok (scrutinee, scrutineeState) ∧
      scrutineeState.allocateHiddenLocal =
        (hiddenScrutinee, hiddenState) ∧
      Detail.inferMatchCasesFuel fuel inferenceContext scrutinee.type
        expectedReturn hiddenState.lexicalScope arms.value.cases
        hiddenState = .ok checked ∧
      finalized.substitution.SemanticallyExtends
        scrutineeState.inference.substitution ∧
      finalized.substitution.SemanticallyExtends
        hiddenState.inference.substitution ∧
      finalized.substitution.SemanticallyExtends
        checked.state.inference.substitution ∧
      TypingSourceExtends (scrutineeState.toTypedSource roots)
        (result.state.toTypedSource roots) ∧
      TypingSourceExtends (hiddenState.toTypedSource roots)
        (result.state.toTypedSource roots) ∧
      TypingSourceExtends (checked.state.toTypedSource roots)
        (result.state.toTypedSource roots) ∧
      scrutineeState.integerPatterns ⊆ result.state.integerPatterns ∧
      scrutineeState.integerLiterals ⊆ result.state.integerLiterals ∧
      scrutineeState.requirements ⊆ result.state.requirements ∧
      checked.state.integerPatterns ⊆ result.state.integerPatterns ∧
      checked.state.integerLiterals ⊆ result.state.integerLiterals ∧
      checked.state.requirements ⊆ result.state.requirements := by
  obtain ⟨scrutinee, scrutineeState, hiddenScrutinee, hiddenState,
    checked, scrutineeSuccess, hiddenAllocation, casesSuccess,
    _guard, resultEq, _contains⟩ :=
    inferStatementFuel_success_matchWithoutDefault_facts statementEq defaultEq
      allocationEq success roots
  have allocatedInvariant : RecursiveStatementInvariant wholeContext
      expectedReturn finalized allocated semanticContext :=
    initialInvariant.allocateStatementId allocationEq
  have scrutineeProperties := inferMatchScrutineesFuel_inferenceProperties
    allocatedInvariant.ready signatureFormation functionsCanonical
    scrutineeSuccess
  have hiddenReady : hiddenState.InferenceReady := by
    have retained := State.InferenceReady.allocateHiddenLocal
      scrutineeProperties.2.1
    have hiddenEq : scrutineeState.allocateHiddenLocal.2 = hiddenState :=
      congrArg Prod.snd hiddenAllocation
    rw [hiddenEq] at retained
    exact retained
  have hiddenScrutineeBelow : scrutinee.type.VariablesBelow
      hiddenState.inference.next := by
    have hiddenEq : scrutineeState.allocateHiddenLocal.2 = hiddenState :=
      congrArg Prod.snd hiddenAllocation
    rw [← hiddenEq]
    exact scrutineeProperties.2.2
  have hiddenReturnBelow : expectedReturn.VariablesBelow
      hiddenState.inference.next := by
    have atScrutinee := allocatedInvariant.returnBelow.weaken
      scrutineeProperties.1.next_le
    have hiddenEq : scrutineeState.allocateHiddenLocal.2 = hiddenState :=
      congrArg Prod.snd hiddenAllocation
    rw [← hiddenEq]
    exact atScrutinee
  have casesProperties := Detail.inferMatchCasesFuel_inferenceProperties
    hiddenReady signatureFormation functionsCanonical
    hiddenScrutineeBelow hiddenReturnBelow rfl casesSuccess
  have checkedExtension : finalized.substitution.SemanticallyExtends
      checked.state.inference.substitution := by
    simpa [resultEq, State.recordNode] using
      resultSubstitutionExtension
  have hiddenExtension : finalized.substitution.SemanticallyExtends
      hiddenState.inference.substitution :=
    Substitution.SemanticallyExtends.trans checkedExtension
      casesProperties.1.substitution_extends
  have hiddenInferenceEq : hiddenState.inference.substitution =
      scrutineeState.inference.substitution := by
    have stateEq := congrArg Prod.snd hiddenAllocation
    simpa [State.allocateHiddenLocal] using
      congrArg (fun state : State => state.inference.substitution)
        stateEq.symm
  have scrutineeExtension : finalized.substitution.SemanticallyExtends
      scrutineeState.inference.substitution := by
    rw [← hiddenInferenceEq]
    exact hiddenExtension
  have allocatedBelow : allocated.NodesBelowNextOccurrence := by
    have retained :=
      State.allocateStatementId_preserves_nodesBelowNextOccurrence initial
        initialInvariant.nodesBelow
    have allocatedEq : initial.allocateStatementId.2 = allocated :=
      congrArg Prod.snd allocationEq
    simpa [allocatedEq] using retained
  have scrutineeBelow : scrutineeState.NodesBelowNextOccurrence :=
    inferMatchScrutineesFuel_success_nodesBelow scrutineeSuccess
      allocatedBelow
  have hiddenBelow : hiddenState.NodesBelowNextOccurrence := by
    have retained := State.allocateHiddenLocal_preserves_nodesBelowNextOccurrence
      scrutineeState scrutineeBelow
    simpa [hiddenAllocation] using retained
  have hiddenToChecked : TypingSourceExtends
      (hiddenState.toTypedSource roots)
      (checked.state.toTypedSource roots) :=
    inferMatchCasesFuel_success_typingSourceExtends casesSuccess
      hiddenBelow roots
  have checkedToResult : TypingSourceExtends
      (checked.state.toTypedSource roots)
      (result.state.toTypedSource roots) := by
    rw [resultEq]
    refine ⟨rfl, ?_⟩
    simp only [State.toTypedSource, State.recordNode]
    exact List.prefix_append _ _
  have scrutineeToHidden : TypingSourceExtends
      (scrutineeState.toTypedSource roots)
      (hiddenState.toTypedSource roots) := by
    have stateEq : scrutineeState.allocateHiddenLocal.2 = hiddenState :=
      congrArg Prod.snd hiddenAllocation
    rw [← stateEq]
    exact ⟨rfl, by simp [State.allocateHiddenLocal, State.toTypedSource]⟩
  have checkedPatterns : checked.state.integerPatterns ⊆
      result.state.integerPatterns := by
    rw [resultEq]
    intro origin member
    exact member
  have checkedLiterals : checked.state.integerLiterals ⊆
      result.state.integerLiterals := by
    rw [resultEq]
    intro origin member
    simpa [State.recordNode] using member
  have checkedRequirements : checked.state.requirements ⊆
      result.state.requirements := by
    rw [resultEq]
    exact State.recordNode_requirements_subset checked.state _
  have hiddenPatternsEq : hiddenState.integerPatterns =
      scrutineeState.integerPatterns := by
    have stateEq := congrArg Prod.snd hiddenAllocation
    simpa [State.allocateHiddenLocal] using
      congrArg State.integerPatterns stateEq.symm
  have hiddenLiteralsEq : hiddenState.integerLiterals =
      scrutineeState.integerLiterals := by
    have stateEq := congrArg Prod.snd hiddenAllocation
    simpa [State.allocateHiddenLocal] using
      congrArg State.integerLiterals stateEq.symm
  have hiddenRequirementsEq : hiddenState.requirements =
      scrutineeState.requirements := by
    have stateEq := congrArg Prod.snd hiddenAllocation
    simpa [State.allocateHiddenLocal] using
      congrArg State.requirements stateEq.symm
  have scrutineePatterns : scrutineeState.integerPatterns ⊆
      result.state.integerPatterns := by
    have initialToChecked : scrutineeState.integerPatterns ⊆
        checked.state.integerPatterns := by
      have viaCases := Detail.inferMatchCasesFuel_integerPatterns_subset
        casesSuccess
      rw [hiddenPatternsEq] at viaCases
      exact viaCases
    exact List.Subset.trans initialToChecked checkedPatterns
  have scrutineeLiterals : scrutineeState.integerLiterals ⊆
      result.state.integerLiterals := by
    have initialToChecked : scrutineeState.integerLiterals ⊆
        checked.state.integerLiterals := by
      have viaCases := Detail.inferMatchCasesFuel_integerLiterals_subset
        casesSuccess
      rw [hiddenLiteralsEq] at viaCases
      exact viaCases
    exact List.Subset.trans initialToChecked checkedLiterals
  have scrutineeRequirements : scrutineeState.requirements ⊆
      result.state.requirements := by
    have initialToChecked : scrutineeState.requirements ⊆
        checked.state.requirements := by
      have viaCases := Detail.inferMatchCasesFuel_requirements_subset
        casesSuccess
      rw [hiddenRequirementsEq] at viaCases
      exact viaCases
    exact List.Subset.trans initialToChecked checkedRequirements
  exact ⟨scrutinee, scrutineeState, hiddenScrutinee, hiddenState, checked,
    scrutineeSuccess, hiddenAllocation, casesSuccess, scrutineeExtension,
    hiddenExtension, checkedExtension,
    scrutineeToHidden.trans (hiddenToChecked.trans checkedToResult),
    hiddenToChecked.trans checkedToResult, checkedToResult,
    scrutineePatterns, scrutineeLiterals, scrutineeRequirements,
    checkedPatterns, checkedLiterals, checkedRequirements⟩

end Solcore.SourceSemantics.SourceInferenceSoundness
