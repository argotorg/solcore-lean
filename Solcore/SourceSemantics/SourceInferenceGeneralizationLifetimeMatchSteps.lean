import Solcore.SourceSemantics.SourceInferenceGeneralizationLifetimeMatchCompletion
import Solcore.SourceSemantics.SourceInferenceActualMatchPrefixProperties

/-! Actual match child calls reach the same enclosing statement result. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
open Frontend SourceInference TypeSystem Detail SourceInferenceExecution
namespace GeneralizationLifetime
variable {whole : TypedSource} {finalSubstitution : Substitution}
    {binder : TypedBinder} {initializer : ExpressionId}
    {event : RetainedGeneralization whole finalSubstitution binder initializer}

private theorem hiddenProgress {initial final : State} {hidden : Resolved.LocalId}
    (ready : initial.InferenceReady)
    (allocation : initial.allocateHiddenLocal = (hidden, final)) :
    initial.InferenceProgress final ∧ final.InferenceReady := by
  have same : final = initial.allocateHiddenLocal.2 := (congrArg Prod.snd allocation).symm
  subst final
  exact ⟨.of_inference_eq ready.solved rfl, ready.allocateHiddenLocal⟩

private theorem hiddenLifetime {entryNext : Nat} {state final : State} {hidden : Resolved.LocalId}
    {outputs : List Ty} (allocation : state.allocateHiddenLocal = (hidden, final))
    (lifetime : GeneralizationLifetime event entryNext state outputs) :
    GeneralizationLifetime event entryNext final outputs := by
  have same : final = state.allocateHiddenLocal.2 := (congrArg Prod.snd allocation).symm
  subst final
  exact { lifetime with live := lifetime.live.transport rfl (.of_substitution_eq rfl) }

private theorem statementMatchPrefix
    {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Statement}
    {scrutinees : Syntax.NonemptyDelimitedList Syntax.Expr} {initial allocated : State}
    {id : StatementId} {scrutinee : InferredExpression} {scrutineeState hiddenState : State}
    {hidden : Resolved.LocalId}
    (ready : initial.InferenceReady) (wellFormed : initial.RequirementsWellFormed)
    (catalog : LifetimeInferenceContext context)
    (allocation : initial.allocateStatementId = (id, allocated))
    (scrutineeAccepted : matchScrutinee fuel context source.span scrutinees.elements.toList allocated = .ok (scrutinee, scrutineeState))
    (hiddenAllocation : scrutineeState.allocateHiddenLocal = (hidden, hiddenState)) :
    initial.InferenceProgress hiddenState ∧ hiddenState.InferenceReady ∧
      hiddenState.RequirementsWellFormed ∧ scrutinee.type.VariablesBelow hiddenState.inference.next := by
  have same : allocated = initial.allocateStatementId.2 := (congrArg Prod.snd allocation).symm
  have facts := matchScrutinee_properties (same ▸ ready.allocateStatementId) catalog scrutineeAccepted
  have hiddenFacts := hiddenProgress facts.2.1 hiddenAllocation
  have hiddenSame : hiddenState = scrutineeState.allocateHiddenLocal.2 := (congrArg Prod.snd hiddenAllocation).symm
  refine ⟨(State.InferenceProgress.allocateStatementId initial ready.solved).trans (same ▸ facts.1) |>.trans hiddenFacts.1,
    hiddenFacts.2, ?_, facts.2.2.weaken hiddenFacts.1.next_le⟩
  rw [hiddenSame]
  exact matchScrutinee_wellFormed (same ▸ wellFormed) scrutineeAccepted

theorem statement_match_cases
    {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Statement}
    {scrutinees : Syntax.NonemptyDelimitedList Syntax.Expr} {arms : Syntax.MatchArms}
    {expectedReturn : Ty} {initial allocated : State} {id : StatementId}
    {scrutinee : InferredExpression} {scrutineeState hiddenState : State} {hidden : Resolved.LocalId}
    {checked : MatchCasesResult} {result : StatementResult}
    (ready : initial.InferenceReady) (wellFormed : initial.RequirementsWellFormed)
    (catalog : LifetimeInferenceContext context) (returnBelow : expectedReturn.VariablesBelow initial.inference.next)
    (form : source.value = .matchWith scrutinees arms)
    (allocation : initial.allocateStatementId = (id, allocated))
    (scrutineeAccepted : matchScrutinee fuel context source.span scrutinees.elements.toList allocated = .ok (scrutinee, scrutineeState))
    (hiddenAllocation : scrutineeState.allocateHiddenLocal = (hidden, hiddenState))
    (casesAccepted : inferMatchCasesFuel fuel context scrutinee.type expectedReturn hiddenState.lexicalScope arms.value.cases hiddenState = .ok checked)
    (accepted : inferStatementFuel (fuel + 1) context source expectedReturn initial = .ok result)
    (lifetime : GeneralizationLifetime event hiddenState.inference.next checked.state []) :
    GeneralizationLifetime event initial.inference.next result.state [result.type] := by
  have prefixFacts := statementMatchPrefix ready wellFormed catalog allocation scrutineeAccepted hiddenAllocation
  have completion := matchCompletion_accepted form allocation scrutineeAccepted hiddenAllocation accepted
  exact (lifetime.match_after_cases prefixFacts.2.1 prefixFacts.2.2.1 catalog prefixFacts.2.2.2
    (returnBelow.weaken prefixFacts.1.next_le) (returnBelow.weaken prefixFacts.1.next_le)
    casesAccepted completion).weaken_entry prefixFacts.1.next_le

theorem statement_match_default
    {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Statement}
    {scrutinees : Syntax.NonemptyDelimitedList Syntax.Expr} {arms : Syntax.MatchArms}
    {expectedReturn : Ty} {initial allocated : State} {id : StatementId}
    {scrutinee : InferredExpression} {scrutineeState hiddenState : State} {hidden : Resolved.LocalId}
    {checked : MatchCasesResult} {body : Syntax.Block} {bodyResult : BlockResult} {result : StatementResult}
    (ready : initial.InferenceReady) (wellFormed : initial.RequirementsWellFormed)
    (catalog : LifetimeInferenceContext context) (returnBelow : expectedReturn.VariablesBelow initial.inference.next)
    (form : source.value = .matchWith scrutinees arms)
    (allocation : initial.allocateStatementId = (id, allocated))
    (scrutineeAccepted : matchScrutinee fuel context source.span scrutinees.elements.toList allocated = .ok (scrutinee, scrutineeState))
    (hiddenAllocation : scrutineeState.allocateHiddenLocal = (hidden, hiddenState))
    (casesAccepted : inferMatchCasesFuel fuel context scrutinee.type expectedReturn hiddenState.lexicalScope arms.value.cases hiddenState = .ok checked)
    (defaultEq : arms.value.defaultBody = some body)
    (bodyAccepted : inferStatementsFuel fuel context body.value expectedReturn checked.state = .ok bodyResult)
    (accepted : inferStatementFuel (fuel + 1) context source expectedReturn initial = .ok result)
    (lifetime : GeneralizationLifetime event checked.state.inference.next bodyResult.state [bodyResult.type]) :
    GeneralizationLifetime event initial.inference.next result.state [result.type] := by
  have prefixFacts := statementMatchPrefix ready wellFormed catalog allocation scrutineeAccepted hiddenAllocation
  have completion := matchCompletion_accepted form allocation scrutineeAccepted hiddenAllocation accepted
  exact (lifetime.match_after_default prefixFacts.2.1 catalog prefixFacts.2.2.2
    (returnBelow.weaken prefixFacts.1.next_le) casesAccepted defaultEq bodyAccepted completion).weaken_entry prefixFacts.1.next_le

end GeneralizationLifetime
end Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
