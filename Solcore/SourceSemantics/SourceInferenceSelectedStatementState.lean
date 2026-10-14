import Solcore.SourceSemantics.SourceInferenceSelectedExpressionState

set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceSoundness
open Frontend Frontend.SourceInference TypeSystem

theorem ActualStateInvariant.allocateStatementId
    {initial final : State} {source : TypedSource} {id : StatementId}
    (invariant : ActualStateInvariant initial source)
    (allocation : initial.allocateStatementId = (id, final)) : ActualStateInvariant final source := by
  obtain ⟨pending, ledger⟩ := invariant.ledger
  have stateEq : initial.allocateStatementId.2 = final := congrArg Prod.snd allocation
  refine ⟨⟨pending, ?_⟩, ?_, ?_, invariant.sourceMonomorphic⟩
  · rw [← stateEq]
    exact ledger.allocateStatementId
  · apply invariant.origins.congr_localBinders
    rw [← stateEq]
    rfl
  · apply activeQuantifiersBelowNext_transport invariant.quantifiersBelow
    · rw [← stateEq]; rfl
    · rw [← stateEq]; exact Nat.le_refl _

theorem ActualStateInvariant.ofStatementPreservingBinders
    {fuel : Nat} {context : Frontend.SourceInference.Context}
    {statement : Syntax.Statement} {returnType : Ty} {initial : State}
    {result : Detail.StatementResult} {source : TypedSource}
    (invariant : ActualStateInvariant initial source)
    (success : Detail.inferStatementFuel fuel context statement returnType initial = .ok result)
    (bindersEq : result.state.localBinders = initial.localBinders)
    (nextLe : initial.inference.next ≤ result.state.inference.next) :
    ActualStateInvariant result.state source := by
  obtain ⟨pending, ledger⟩ := invariant.ledger
  exact ⟨⟨pending, (actualLedgerFamily fuel).statements.statement success ledger⟩,
    invariant.origins.congr_localBinders bindersEq,
    activeQuantifiersBelowNext_transport invariant.quantifiersBelow bindersEq nextLe, invariant.sourceMonomorphic⟩

end Solcore.SourceSemantics.SourceInferenceSoundness
