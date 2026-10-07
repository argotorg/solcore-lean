import Solcore.SourceSemantics.CoreLowering.ProtectedStateForReady
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedLexicalReadiness

/-! The real native self-cell activation retains the original Source heap.
Its actual administrative effects authenticate every reached row's history. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedForReadiness
open Core Frontend SourceInference
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedIndirectExpressionHeads (StableRows)
open RecursiveNamedLexicalContracts.Stateful.WithReady
universe u
variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)

/-- This producer uses the exact activation endpoint's Source heap index and
real administrative preservation. The reached state and records stay intact. -/
theorem activation : ProtectedFor.Body.Stateful.WithReady.ActivationTransfers callerProtocol
    (CallableIndexedOwnedAdmittedLexicalReadiness.readiness bridge) where
  ready := by
    intro context scope mapping world heap store canonical actual type condition body post reason initial reached
      frame _related _records admitted
    exact ⟨admitted.heap,
      StableRows.after_administrative (bridge.pool initial) (bridge.pool reached) admitted.rows frame⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedForReadiness
