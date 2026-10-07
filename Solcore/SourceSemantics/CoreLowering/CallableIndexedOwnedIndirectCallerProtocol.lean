import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedCallerProtocol
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedNamedCallerProtocol

/-! Indirect callers return their same actual pool using the real preservation
receipts. Original callers and callers with stronger static slots use the same
return interface; no stronger admission is recovered from a bare pool. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedIndirectCallerProtocol
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedOwnedFunctionState
universe u
variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {caller : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}

/-- Indirect selection does not consume named slots. This projection retains
the original caller's actual pool and its complete return operation. -/
def forget_slots {slots : ProtectedStateTransition.Index → Prop}
    (carrier : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) slots caller) :
    CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) caller where
  pool := carrier.pool
  records_eq := carrier.records_eq
  related := carrier.related
  slots := fun _ => True.intro
  restore := carrier.restore

/-- Compatibility wraps exactly the original returned pool. Original callers
need no extra static admission, so the added preservation receipts are unused. -/
def of_legacy (carrier : CallableIndexedOwnedCallerProtocol.Carrier (headers := headers) caller) :
    CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) caller where
  pool := carrier.pool
  records_eq := carrier.records_eq
  related := carrier.related
  slots := fun _ => True.intro
  restore := fun {_index} initial {_mapping _world _heap _store} reached _maps _worlds _frame _metadata related =>
    ⟨carrier.of_pool initial reached, carrier.pool_of_pool initial reached,
      carrier.return_related initial reached related⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedIndirectCallerProtocol
