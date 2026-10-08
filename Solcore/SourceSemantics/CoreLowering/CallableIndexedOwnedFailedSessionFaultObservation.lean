import Solcore.Frontend.SourceCoreIndexedSession

/-! An actual failed ordinary root request keeps its exact native completion
and diagnostic receiver. RootStart fixes the selected request and key; the
completion receipt fixes the returned values and owned slot weakening.
Source failure origins and exported heap equality remain independent. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedFailedSessionFaultObservation
open Frontend SourceCoreIndexedSession

variable {artifact : Artifact} {origin returned : Session artifact}
  {checkpoint : Checkpoint artifact} {key : Key} {arguments : List SourceCoreIndexedSession.Value}
  {boundaryFuel fuel : Nat} {native : Core.Value} {store : Core.Store} {reason : Core.Word}
  {diagnostic : SourceCoreFaultSites.Diagnostic}

/-- The same pending request and returned values determine the same lookup.
This proof compares the original finite wrappers; it does not run a factory. -/
theorem failed_root_diagnostic
    (started : checkpoint.RootStart origin key arguments boundaryFuel)
    (completed : checkpoint.FailedResultAt fuel native store reason returned)
    (accepted : checkpoint.diagnostic reason = .ok (some diagnostic)) :
    returned.diagnostic key reason = .ok (some diagnostic) := by
  obtain ⟨root, found, _key, _length, encoded, _encoded, _origin, request,
      _world, _state, _registry, _values⟩ := started
  obtain ⟨_done, _decoded, _store, _future, values, owner, _authority, _prefix, _slots⟩ := completed
  unfold Checkpoint.diagnostic at accepted
  unfold Session.diagnostic
  simp only [found, pure, Except.pure, bind, Except.bind]
  simpa only [request, ← values, pure, Except.pure, bind, Except.bind] using accepted

/-- The receiver belongs to this actual failed request and returned session.
Its table retains the exact native token and actual decoded public diagnostic.
The original completion receipt supplies every current store and owner field. -/
structure Packet
    (checkpoint : Checkpoint artifact) (origin returned : Session artifact)
    (key : Key) (arguments : List SourceCoreIndexedSession.Value) (boundaryFuel fuel : Nat)
    (native : Core.Value) (store : Core.Store) (reason : Core.Word)
    (diagnostic : SourceCoreFaultSites.Diagnostic) : Prop where
  started : checkpoint.RootStart origin key arguments boundaryFuel
  completed : checkpoint.FailedResultAt fuel native store reason returned
  publicDecode : returned.diagnostic key reason = .ok (some diagnostic)
  receiver : ∃ table : SourceCoreFaultSites.Table,
    returned.DiagnosticTableAt key table ∧ table.diagnostic? reason = some diagnostic

/-- Actual pending diagnostic acceptance transfers to the failed session.
The existing receipt identifies the very table, whose genuine registry rebuild
and filtered callable append are supplied by DiagnosticTableAt.rebuild. -/
theorem packet_of_pending
    (started : checkpoint.RootStart origin key arguments boundaryFuel)
    (completed : checkpoint.FailedResultAt fuel native store reason returned)
    (accepted : checkpoint.diagnostic reason = .ok (some diagnostic)) :
    Packet checkpoint origin returned key arguments boundaryFuel fuel native store reason diagnostic := by
  have decoded := failed_root_diagnostic started completed accepted
  exact ⟨started, completed, decoded, returned.diagnostic_table_receipt decoded⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedFailedSessionFaultObservation
