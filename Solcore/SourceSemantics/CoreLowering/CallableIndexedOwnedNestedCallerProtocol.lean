import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedNestedCanonicalState
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedNamedCallerProtocol

/-! Genuine nested formation observations return with the same actual named
call post pool. The retained administrative frame read authenticates reached
metadata against its own ghost; ordered records are projected verbatim. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedNestedCallerProtocol
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedOwnedFunctionState
open CallableIndexedOwnedNestedCanonicalState
open CallableIndexedOwnedExpressionHeads (Globals)
variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (caller : CallableIndexedOwnedFunctionValues.Header compiled program)

/-- Stronger caller facts accompany the actual argument/body returned pool.
The return operation never substitutes an administratively extended pool. -/
def carrier : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers)
    (fun index => Globals (headers := headers) owner 1 index.scope index.canonical)
    (protocol (headers := headers) owner caller) where
  pool := fun state => state.val
  records_eq := fun _ => rfl
  related := fun relation => relation
  slots := fun state => state.property.globals
  restore := by
    intro index initial mapping world heap store reached maps worlds frame metadata relation
    exact ⟨⟨reached, Packet.after owner caller initial.property reached frame⟩, rfl, relation⟩

/-- The carrier reads the same complete pool witness from the wrapper. -/
theorem pool_eq {index : ProtectedStateTransition.Index}
    (state : (protocol (headers := headers) owner caller).State index) :
    (carrier owner caller).pool state = state.val := rfl

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedNestedCallerProtocol
