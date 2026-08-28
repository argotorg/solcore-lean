import Solcore.Semantics.FrameCheckpointedWorkingPairWithPresentStorageAccountProperties
import Solcore.Semantics.FrameCheckpointedWorkingPairWithStorageAddressProperties
import Solcore.Semantics.FrameCheckpointedWorkingPairWithStorageAddressStorageReadProperties

/-! Compile-only regressions for selected working Account refinement laws. -/

set_option autoImplicit false

namespace Tests

open Solcore
open Solcore.Semantics

private example
    {RollbackState TraceState : Type}
    (context :
      FrameCheckpointedWorkingPairWithStorageAddress RollbackState TraceState)
    (absent :
      context.values.working.1.account? context.storageAddress = none) :
    context.withPresentStorageAccount? = none := by
  exact
    FrameCheckpointedWorkingPairWithStorageAddress.withPresentStorageAccount?_of_absent
      context absent

private example
    {RollbackState TraceState : Type}
    (context :
      FrameCheckpointedWorkingPairWithStorageAddress RollbackState TraceState)
    (account : Account)
    (present :
      context.values.working.1.account? context.storageAddress = some account) :
    context.withPresentStorageAccount? =
      some ⟨context, account, present⟩ := by
  exact
    FrameCheckpointedWorkingPairWithStorageAddress.withPresentStorageAccount?_of_present
      context account present

private example
    {RollbackState TraceState : Type}
    (refined :
      FrameCheckpointedWorkingPairWithPresentStorageAccount
        RollbackState TraceState)
    (slot value : Core.Word) :
    refined.context.readStorage? slot =
        some (refined.storageAccount.storageRead slot) ∧
      refined.context.writeStorage? slot value =
        some
          ⟨refined.context.storageAddress,
            ⟨refined.context.values.checkpoint,
              (refined.context.values.working.1.putAccount
                refined.context.storageAddress
                (refined.storageAccount.storageWrite slot value),
                refined.context.values.working.2)⟩⟩ := by
  constructor
  · exact
      FrameCheckpointedWorkingPairWithStorageAddress.readStorage?_of_present
        refined.context refined.storageAccount slot
          refined.storageAccount_present
  · exact
      FrameCheckpointedWorkingPairWithStorageAddress.writeStorage?_of_present
        refined.context refined.storageAccount slot value
          refined.storageAccount_present

end Tests
