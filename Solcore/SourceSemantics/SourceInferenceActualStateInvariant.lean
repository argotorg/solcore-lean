import Solcore.SourceSemantics.SourceInferenceStatementLedgerInvariant
import Solcore.SourceSemantics.SourceInferenceCaptureOrigins
import Solcore.SourceSemantics.SourceInferenceUnannotatedLetCertificate

set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceSoundness
open Frontend Frontend.SourceInference TypeSystem

/-- The actual requirement ledger and origins of active generalized binders.
For-header traversal may change the pending suffix before its loop is recorded. -/
structure ActualStateInvariant (state : State) (evidenceSource : TypedSource) : Prop where
  ledger : ∃ pending, RecursiveLedgerInvariant state pending
  origins : ActiveBinderCaptureOrigins state evidenceSource
  quantifiersBelow : ActiveQuantifiersBelowNext state

namespace ActualStateInvariant

theorem initial (owner : Resolved.DeclarationId) (locals : Environment)
    (comptime : List Bool) (evidenceSource : TypedSource)
    (monomorphic : ∀ entry ∈ locals, entry.2.quantified = []) :
    ActualStateInvariant (State.initial owner locals comptime) evidenceSource :=
  ⟨⟨[], RecursiveLedgerInvariant.initial owner locals comptime⟩,
    activeBinderCaptureOrigins_initial_mono owner locals comptime evidenceSource monomorphic,
    activeQuantifiersBelowNext_initial_mono owner locals comptime monomorphic⟩

end ActualStateInvariant
end Solcore.SourceSemantics.SourceInferenceSoundness
