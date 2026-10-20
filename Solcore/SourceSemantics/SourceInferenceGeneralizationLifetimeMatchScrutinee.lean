import Solcore.SourceSemantics.SourceInferenceGeneralizationLifetimeMatchSteps

/-! Scalar and synthetic tuple scrutinees use their real evaluation suffix. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
open Frontend SourceInference TypeSystem Detail SourceInferenceExecution
namespace GeneralizationLifetime
variable {whole : TypedSource} {finalSubstitution : Substitution}
    {binder : TypedBinder} {initializer : ExpressionId}
    {event : RetainedGeneralization whole finalSubstitution binder initializer}

theorem statement_match_scrutinee
    {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Statement}
    {scrutinees : Syntax.NonemptyDelimitedList Syntax.Expr} {arms : Syntax.MatchArms}
    {expectedReturn : Ty} {initial allocated : State} {id : StatementId}
    {scrutinee : InferredExpression} {scrutineeState : State} {result : StatementResult}
    (ready : initial.InferenceReady) (wellFormed : initial.RequirementsWellFormed)
    (catalog : LifetimeInferenceContext context) (returnBelow : expectedReturn.VariablesBelow initial.inference.next)
    (form : source.value = .matchWith scrutinees arms)
    (allocation : initial.allocateStatementId = (id, allocated))
    (scrutineeAccepted : matchScrutinee fuel context source.span scrutinees.elements.toList allocated = .ok (scrutinee, scrutineeState))
    (accepted : inferStatementFuel (fuel + 1) context source expectedReturn initial = .ok result)
    (lifetime : GeneralizationLifetime event allocated.inference.next scrutineeState [scrutinee.type]) :
    GeneralizationLifetime event initial.inference.next result.state [result.type] := by
  have same : allocated = initial.allocateStatementId.2 := (congrArg Prod.snd allocation).symm
  have sameNext : allocated.inference.next = initial.inference.next := by rw [same]; rfl
  have prefixFacts := matchScrutinee_properties (same ▸ ready.allocateStatementId) catalog scrutineeAccepted
  have prefixWF := matchScrutinee_wellFormed (same ▸ wellFormed) scrutineeAccepted
  let hidden := scrutineeState.allocateHiddenLocal.1
  let hiddenState := scrutineeState.allocateHiddenLocal.2
  have hiddenReady : hiddenState.InferenceReady := prefixFacts.2.1.allocateHiddenLocal
  have hiddenLife : GeneralizationLifetime event allocated.inference.next hiddenState [scrutinee.type] :=
    { lifetime with live := lifetime.live.transport rfl (.of_substitution_eq rfl) }
  have completion := matchCompletion_accepted form allocation scrutineeAccepted (show scrutineeState.allocateHiddenLocal = (hidden, hiddenState) from rfl) accepted
  cases casesAccepted : inferMatchCasesFuel fuel context scrutinee.type expectedReturn hiddenState.lexicalScope arms.value.cases hiddenState with
  | error error => simp [matchCompletion, casesAccepted, bind, Except.bind] at completion
  | ok checked =>
      have returnAtHidden : expectedReturn.VariablesBelow hiddenState.inference.next :=
        (sameNext ▸ returnBelow).weaken prefixFacts.1.next_le
      have checkedLife := hiddenLife.inferMatchCases hiddenReady prefixWF catalog prefixFacts.2.2
        (hiddenLife.values _ (List.mem_singleton_self _)) returnAtHidden
        (hiddenLife.older _ (sameNext ▸ returnBelow)) rfl casesAccepted
      have finished := checkedLife.match_after_cases hiddenReady prefixWF catalog prefixFacts.2.2
        returnAtHidden (sameNext ▸ returnBelow) casesAccepted completion
      simpa only [sameNext] using finished

theorem statement_match_single
    {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Statement}
    {scrutinees : Syntax.NonemptyDelimitedList Syntax.Expr} {arms : Syntax.MatchArms}
    {expectedReturn : Ty} {initial allocated : State} {id : StatementId}
    {scrutinee : Syntax.Expr} {value : InferredExpression} {childFinal : State} {result : StatementResult}
    (ready : initial.InferenceReady) (wellFormed : initial.RequirementsWellFormed)
    (catalog : LifetimeInferenceContext context) (returnBelow : expectedReturn.VariablesBelow initial.inference.next)
    (form : source.value = .matchWith scrutinees arms)
    (allocation : initial.allocateStatementId = (id, allocated))
    (single : scrutinees.elements.toList = [scrutinee])
    (childAccepted : inferExprFuel fuel context scrutinee none allocated = .ok (value, childFinal))
    (accepted : inferStatementFuel (fuel + 1) context source expectedReturn initial = .ok result)
    (lifetime : GeneralizationLifetime event allocated.inference.next childFinal [value.type]) :
    GeneralizationLifetime event initial.inference.next result.state [result.type] := by
  have scrutineeAccepted : matchScrutinee fuel context source.span scrutinees.elements.toList allocated = .ok (value, childFinal) := by
    simpa only [matchScrutinee, single] using childAccepted
  exact lifetime.statement_match_scrutinee ready wellFormed catalog returnBelow form allocation scrutineeAccepted accepted

theorem statement_match_many
    {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Statement}
    {scrutinees : Syntax.NonemptyDelimitedList Syntax.Expr} {arms : Syntax.MatchArms}
    {expectedReturn : Ty} {initial allocated : State} {id : StatementId}
    {values : List InferredExpression} {childFinal : State} {result : StatementResult}
    (ready : initial.InferenceReady) (wellFormed : initial.RequirementsWellFormed)
    (catalog : LifetimeInferenceContext context) (returnBelow : expectedReturn.VariablesBelow initial.inference.next)
    (form : source.value = .matchWith scrutinees arms)
    (allocation : initial.allocateStatementId = (id, allocated))
    (multiple : ∀ scrutinee, scrutinees.elements.toList ≠ [scrutinee])
    (childAccepted : inferExprsFuel fuel context scrutinees.elements.toList allocated = .ok (values, childFinal))
    (accepted : inferStatementFuel (fuel + 1) context source expectedReturn initial = .ok result)
    (lifetime : GeneralizationLifetime event allocated.inference.next childFinal (values.map (·.type))) :
    GeneralizationLifetime event initial.inference.next result.state [result.type] := by
  let tuple : InferredExpression := ⟨childFinal.allocateExpressionId.1, Ty.productMany (values.map (·.type))⟩
  let tupleState := childFinal.allocateExpressionId.2.recordNode (.expression {
    id := tuple.id, span := source.span, type := tuple.type, form := .tuple (values.map (·.id)) })
  have scrutineeAccepted : matchScrutinee fuel context source.span scrutinees.elements.toList allocated = .ok (tuple, tupleState) := by
    unfold matchScrutinee
    split
    · rename_i sourceEq
      exact False.elim (multiple _ sourceEq)
    · simp only [childAccepted, bind, Except.bind, pure, Pure.pure, Except.pure]
      rfl
  have tupleSafe : Safe binder.scheme.quantified childFinal tuple.type := by
    exact safe_productMany _ _ _ lifetime.values
  have tupleLife : GeneralizationLifetime event allocated.inference.next tupleState [tuple.type] :=
    { lifetime with
      live := lifetime.live.transport rfl (.of_substitution_eq rfl)
      values := fun type member => (List.mem_singleton.mp member) ▸ tupleSafe }
  exact tupleLife.statement_match_scrutinee ready wellFormed catalog returnBelow form allocation scrutineeAccepted accepted

end GeneralizationLifetime
end Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
