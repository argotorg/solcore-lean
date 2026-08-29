import Solcore.Semantics.HostStorageDriver
import Solcore.Semantics.WorldStateCode

/-! Address-selected host execution over a proven-present storage Account. -/

set_option autoImplicit false

namespace Solcore.Semantics

universe u v

namespace FrameCheckpointedWorkingPairWithPresentStorageAccount

/--
Select code from the working WorldState and handle storage through the
separately selected storage Account.
-/
def runCodeWithStorage?
    {RollbackState : Type u}
    {TraceState : Type v}
    (context :
      FrameCheckpointedWorkingPairWithPresentStorageAccount
        RollbackState TraceState)
    (codeAddress : Address)
    (fuel : Nat) :
    Option
      (HostDriverResult
        (HostStorageDriver.Context RollbackState TraceState)) :=
  (context.context.values.working.1.code? codeAddress).map fun code =>
    code.runWithStorage context codeAddress fuel

end FrameCheckpointedWorkingPairWithPresentStorageAccount

end Solcore.Semantics
