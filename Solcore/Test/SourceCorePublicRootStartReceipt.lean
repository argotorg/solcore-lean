import Solcore.Frontend.SourceCoreIndexedSession

/-! Public startup receipts preserve the actual encoder and machine state.
The source representation of encoded inputs remains an independent obligation. -/
set_option autoImplicit false
namespace Solcore.Test.SourceCorePublicRootStartReceipt
open Frontend.SourceCoreIndexedSession

abbrev actual_start := @Session.start_root_receipt
abbrev original_completion := @Checkpoint.RootStart.native_completed

theorem actual_start_heap {artifact : Artifact} (session : Session artifact)
    {key : Frontend.SourceCoreFunctions.Key} {arguments : List Frontend.SourceCorePublicValues.Value}
    {fuel : Nat} {checkpoint : Checkpoint artifact}
    (accepted : session.start key arguments fuel = .ok checkpoint) :
    checkpoint.heapSize = session.heapSize :=
  (Session.start_root_receipt session accepted).heap_size

end Solcore.Test.SourceCorePublicRootStartReceipt
