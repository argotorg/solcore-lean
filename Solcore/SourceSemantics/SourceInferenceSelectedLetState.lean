import Solcore.SourceSemantics.SourceInferenceSelectedStatementState

set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceSoundness
open Frontend Frontend.SourceInference TypeSystem

theorem ActualStateInvariant.withLocals
    {state : State} {source : TypedSource}
    (invariant : ActualStateInvariant state source) (locals : Environment) :
    ActualStateInvariant (state.withLocals locals) source := by
  obtain ⟨pending, ledger⟩ := invariant.ledger
  exact ⟨⟨pending, ⟨ledger.requirements,
    ⟨ledger.templates.classified, ledger.templates.unique, ledger.templates.covered⟩⟩⟩, invariant.origins.congr_localBinders rfl,
    activeQuantifiersBelowNext_transport invariant.quantifiersBelow rfl (Nat.le_refl _), invariant.sourceMonomorphic⟩

theorem ActualStateInvariant.ofStatementWithScope
    {fuel : Nat} {context : Frontend.SourceInference.Context}
    {statement : Syntax.Statement} {returnType : Ty} {initial : State}
    {result : Detail.StatementResult} {source : TypedSource}
    (invariant : ActualStateInvariant initial source)
    (success : Detail.inferStatementFuel fuel context statement returnType initial = .ok result)
    (origins : ActiveBinderCaptureOrigins result.state source)
    (bound : ActiveQuantifiersBelowNext result.state) : ActualStateInvariant result.state source := by
  obtain ⟨pending, ledger⟩ := invariant.ledger
  exact ⟨⟨pending, (actualLedgerFamily fuel).statements.statement success ledger⟩, origins, bound, invariant.sourceMonomorphic⟩

end Solcore.SourceSemantics.SourceInferenceSoundness
