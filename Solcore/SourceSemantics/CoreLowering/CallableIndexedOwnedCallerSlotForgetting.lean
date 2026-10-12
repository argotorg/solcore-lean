import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedNamedCallerProtocol

/-! A caller may retain stronger slot receipts while ordinary recursive
children use exactly the same pool, records, restoration and state relation. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedNamedCallerProtocol
open CallableIndexedOwnedFunctionState
universe u
variable {compiled : Frontend.SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}

/-- Forget only the slot proposition; all operational state fields remain
those of the original carrier. -/
def Carrier.forgetSlots {slots : ProtectedStateTransition.Index → Prop}
    {caller : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
    (carrier : Carrier (headers := headers) slots caller) :
    Carrier (headers := headers) (fun _ => True) caller where
  pool := carrier.pool
  records_eq := carrier.records_eq
  related := carrier.related
  slots := fun _ => trivial
  restore := carrier.restore

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedNamedCallerProtocol
