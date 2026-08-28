import Solcore.Semantics.HostStorageReadDriver
import Solcore.Semantics.WorldStateCode

/-! Address-selected host execution over a proven-present storage Account. -/

set_option autoImplicit false

namespace Solcore.Semantics

universe u v

namespace FrameCheckpointedWorkingPairWithPresentStorageAccount

/--
Select code from the working WorldState and handle reads through the separately
selected storage Account.
-/
def runCodeWithStorageReads?
    {RollbackState : Type u}
    {TraceState : Type v}
    (context :
      FrameCheckpointedWorkingPairWithPresentStorageAccount
        RollbackState TraceState)
    (codeAddress : Address)
    (fuel : Nat) :
    Option
      (HostDriverResult
        (HostStorageReadDriver.Context RollbackState TraceState)) :=
  (context.context.values.working.1.code? codeAddress).map fun code =>
    code.runWithStorageReads context fuel

end FrameCheckpointedWorkingPairWithPresentStorageAccount

end Solcore.Semantics
