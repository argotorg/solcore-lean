import Solcore.ContractRuntime.FrameCheckpointedWorkingPairWithStorageAddress
import Solcore.ContractRuntime.WorldState
import Solcore.ContractRuntime.Account
import Solcore.ContractRuntime.WorldStateCode

/-! Evidence that an address-bound working context contains its selected Account. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime

universe u v

/-- An address-bound working context paired with its present selected Account. -/
structure FrameCheckpointedWorkingPairWithPresentStorageAccount
    (RollbackState : Type u) (TraceState : Type v) : Type (max u v) where
  context :
    FrameCheckpointedWorkingPairWithStorageAddress RollbackState TraceState
  storageAccount : Account
  storageAccount_present :
    context.values.working.1.account? context.storageAddress =
      some storageAccount

namespace FrameCheckpointedWorkingPairWithStorageAddress

/-- Refine a context exactly when its selected working Account is present. -/
def withPresentStorageAccount?
    {RollbackState : Type u} {TraceState : Type v}
    (context :
      FrameCheckpointedWorkingPairWithStorageAddress RollbackState TraceState) :
    Option
      (FrameCheckpointedWorkingPairWithPresentStorageAccount
        RollbackState TraceState) :=
  match present :
      context.values.working.1.account? context.storageAddress with
  | none => none
  | some account => some ⟨context, account, present⟩

end FrameCheckpointedWorkingPairWithStorageAddress

end Solcore.ContractRuntime

/-!
## Consolidated module: `Solcore.ContractRuntime.FrameCheckpointedWorkingPairWithPresentStorageAccountProperties`
-/

/-! Branch laws for refining an address-bound context by working Account presence. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.FrameCheckpointedWorkingPairWithStorageAddress

universe u v

/-- A missing selected working Account makes refinement unavailable. -/
@[simp] theorem withPresentStorageAccount?_of_absent
    {RollbackState : Type u} {TraceState : Type v}
    (context :
      FrameCheckpointedWorkingPairWithStorageAddress RollbackState TraceState)
    (absent :
      context.values.working.1.account? context.storageAddress = none) :
    context.withPresentStorageAccount? = none := by
  unfold withPresentStorageAccount?
  split <;> simp_all

/-- A present selected working Account produces its exact evidence carrier. -/
@[simp] theorem withPresentStorageAccount?_of_present
    {RollbackState : Type u} {TraceState : Type v}
    (context :
      FrameCheckpointedWorkingPairWithStorageAddress RollbackState TraceState)
    (account : Account)
    (present :
      context.values.working.1.account? context.storageAddress = some account) :
    context.withPresentStorageAccount? =
      some ⟨context, account, present⟩ := by
  unfold withPresentStorageAccount?
  split
  · simp_all
  · rename_i account' observed
    have same : account' = account :=
      Option.some.inj (observed.symm.trans present)
    subst account'
    rfl

end Solcore.ContractRuntime.FrameCheckpointedWorkingPairWithStorageAddress

/-!
## Consolidated module: `Solcore.ContractRuntime.FrameCheckpointedWorkingPairWithPresentStorageAccountStorageRead`
-/

/-! Total storage reads from a proven-present selected working Account. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.FrameCheckpointedWorkingPairWithPresentStorageAccount

universe u v

/-- Read one slot from the proven-present selected working Account. -/
def readStorage
    {RollbackState : Type u} {TraceState : Type v}
    (context :
      FrameCheckpointedWorkingPairWithPresentStorageAccount
        RollbackState TraceState)
    (slot : Core.Word) : Core.Word :=
  context.storageAccount.storageRead slot

end Solcore.ContractRuntime.FrameCheckpointedWorkingPairWithPresentStorageAccount

/-!
## Consolidated module: `Solcore.ContractRuntime.FrameCheckpointedWorkingPairWithPresentStorageAccountStorageReadProperties`
-/

/-! Coherence between proven-present total reads and address-bound optional reads. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.FrameCheckpointedWorkingPairWithPresentStorageAccount

universe u v

/-- The underlying optional context read returns the total refined read. -/
@[simp] theorem context_readStorage?_eq_some_readStorage
    {RollbackState : Type u} {TraceState : Type v}
    (context :
      FrameCheckpointedWorkingPairWithPresentStorageAccount
        RollbackState TraceState)
    (slot : Core.Word) :
    context.context.readStorage? slot = some (context.readStorage slot) := by
  exact
    FrameCheckpointedWorkingPairWithStorageAddress.readStorage?_of_present
      context.context context.storageAccount slot context.storageAccount_present

end Solcore.ContractRuntime.FrameCheckpointedWorkingPairWithPresentStorageAccount

/-!
## Consolidated module: `Solcore.ContractRuntime.FrameCheckpointedWorkingPairWithPresentStorageAccountStorageWrite`
-/

/-! Total storage writes through a proven-present selected working Account. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.FrameCheckpointedWorkingPairWithPresentStorageAccount

universe u v

/-- Update the selected Account and its working-state entry in lockstep. -/
def writeStorage
    {RollbackState : Type u} {TraceState : Type v}
    (context :
      FrameCheckpointedWorkingPairWithPresentStorageAccount
        RollbackState TraceState)
    (slot value : Core.Word) :
    FrameCheckpointedWorkingPairWithPresentStorageAccount
      RollbackState TraceState :=
  let storageAccount := context.storageAccount.storageWrite slot value
  let nextContext :
      FrameCheckpointedWorkingPairWithStorageAddress
        RollbackState TraceState :=
    ⟨context.context.storageAddress,
      ⟨context.context.values.checkpoint,
        (context.context.values.working.1.putAccount
          context.context.storageAddress storageAccount,
          context.context.values.working.2)⟩⟩
  ⟨nextContext, storageAccount, by
    simp [nextContext, WorldState.putAccount, WorldState.account?]⟩

end Solcore.ContractRuntime.FrameCheckpointedWorkingPairWithPresentStorageAccount

/-!
## Consolidated module: `Solcore.ContractRuntime.FrameCheckpointedWorkingPairWithPresentStorageAccountStorageReadWriteProperties`
-/

/-! Read-after-write laws for proven-present total working storage. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.FrameCheckpointedWorkingPairWithPresentStorageAccount

universe u v

/-- Reading the written slot observes the new total-write value. -/
@[simp] theorem readStorage_writeStorage_same
    {RollbackState : Type u} {TraceState : Type v}
    (context :
      FrameCheckpointedWorkingPairWithPresentStorageAccount
        RollbackState TraceState)
    (slot value : Core.Word) :
    (context.writeStorage slot value).readStorage slot = value := by
  exact Account.storageRead_storageWrite_same
    context.storageAccount slot value

/-- A total write to another slot preserves the prior total read. -/
@[simp] theorem readStorage_writeStorage_other
    {RollbackState : Type u} {TraceState : Type v}
    (context :
      FrameCheckpointedWorkingPairWithPresentStorageAccount
        RollbackState TraceState)
    (writtenSlot value readSlot : Core.Word)
    (different : readSlot ≠ writtenSlot) :
    (context.writeStorage writtenSlot value).readStorage readSlot =
      context.readStorage readSlot := by
  exact Account.storageRead_storageWrite_other
    context.storageAccount writtenSlot value readSlot different

end Solcore.ContractRuntime.FrameCheckpointedWorkingPairWithPresentStorageAccount

/-!
## Consolidated module: `Solcore.ContractRuntime.FrameCheckpointedWorkingPairWithPresentStorageAccountStorageWriteProperties`
-/

/-! Coherence between proven-present total and address-bound optional writes. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.FrameCheckpointedWorkingPairWithPresentStorageAccount

universe u v

/-- The underlying optional write returns the total write's updated context. -/
@[simp] theorem context_writeStorage?_eq_some_writeStorage_context
    {RollbackState : Type u} {TraceState : Type v}
    (context :
      FrameCheckpointedWorkingPairWithPresentStorageAccount
        RollbackState TraceState)
    (slot value : Core.Word) :
    context.context.writeStorage? slot value =
      some (context.writeStorage slot value).context := by
  exact
    FrameCheckpointedWorkingPairWithStorageAddress.writeStorage?_of_present
      context.context context.storageAccount slot value
      context.storageAccount_present

end Solcore.ContractRuntime.FrameCheckpointedWorkingPairWithPresentStorageAccount

/-!
## Consolidated module: `Solcore.ContractRuntime.FrameCheckpointedWorkingPairWithPresentStorageAccountStorageWriteAlgebraProperties`
-/

/-! Algebraic laws for proven-present total working-storage writes. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.FrameCheckpointedWorkingPairWithPresentStorageAccount

universe u v

/-- A later total write to the same slot supersedes the earlier write. -/
@[simp] theorem writeStorage_overwrite
    {RollbackState : Type u} {TraceState : Type v}
    (context :
      FrameCheckpointedWorkingPairWithPresentStorageAccount
        RollbackState TraceState)
    (slot first second : Core.Word) :
    (context.writeStorage slot first).writeStorage slot second =
      context.writeStorage slot second := by
  simp [writeStorage]

/-- Total writes to distinct slots commute. -/
theorem writeStorage_commute_slots
    {RollbackState : Type u} {TraceState : Type v}
    (context :
      FrameCheckpointedWorkingPairWithPresentStorageAccount
        RollbackState TraceState)
    (leftSlot leftValue rightSlot rightValue : Core.Word)
    (different : leftSlot ≠ rightSlot) :
    (context.writeStorage leftSlot leftValue).writeStorage
        rightSlot rightValue =
      (context.writeStorage rightSlot rightValue).writeStorage
        leftSlot leftValue := by
  simp [writeStorage,
    Account.storageWrite_commute context.storageAccount
      leftSlot leftValue rightSlot rightValue different]

end Solcore.ContractRuntime.FrameCheckpointedWorkingPairWithPresentStorageAccount

/-!
## Consolidated module: `Solcore.ContractRuntime.FrameCheckpointedWorkingPairWithPresentStorageAccountStorageWriteProjectionProperties`
-/

/-! Data projections of proven-present total working-storage writes. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.FrameCheckpointedWorkingPairWithPresentStorageAccount

universe u v

/-- A total write retains the exact storage selector. -/
@[simp] theorem storageAddress_writeStorage
    {RollbackState : Type u} {TraceState : Type v}
    (context :
      FrameCheckpointedWorkingPairWithPresentStorageAccount
        RollbackState TraceState)
    (slot value : Core.Word) :
    (context.writeStorage slot value).context.storageAddress =
      context.context.storageAddress := by
  rfl

/-- A total write retains the exact checkpoint. -/
@[simp] theorem checkpoint_writeStorage
    {RollbackState : Type u} {TraceState : Type v}
    (context :
      FrameCheckpointedWorkingPairWithPresentStorageAccount
        RollbackState TraceState)
    (slot value : Core.Word) :
    (context.writeStorage slot value).context.values.checkpoint =
      context.context.values.checkpoint := by
  rfl

/-- A total write retains the exact working effects. -/
@[simp] theorem workingEffects_writeStorage
    {RollbackState : Type u} {TraceState : Type v}
    (context :
      FrameCheckpointedWorkingPairWithPresentStorageAccount
        RollbackState TraceState)
    (slot value : Core.Word) :
    (context.writeStorage slot value).context.values.working.2 =
      context.context.values.working.2 := by
  rfl

/-- A total write stores the exact lower-level Account update. -/
@[simp] theorem storageAccount_writeStorage
    {RollbackState : Type u} {TraceState : Type v}
    (context :
      FrameCheckpointedWorkingPairWithPresentStorageAccount
        RollbackState TraceState)
    (slot value : Core.Word) :
    (context.writeStorage slot value).storageAccount =
      context.storageAccount.storageWrite slot value := by
  rfl

end Solcore.ContractRuntime.FrameCheckpointedWorkingPairWithPresentStorageAccount

/-!
## Consolidated module: `Solcore.ContractRuntime.FrameCheckpointedWorkingPairWithPresentStorageAccountStorageWriteIsolationProperties`
-/

/-! Non-selected working Account isolation for proven-present total writes. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.FrameCheckpointedWorkingPairWithPresentStorageAccount

universe u v

/-- A total storage write preserves every non-selected working Account. -/
@[simp] theorem workingAccount?_writeStorage_other
    {RollbackState : Type u} {TraceState : Type v}
    (context :
      FrameCheckpointedWorkingPairWithPresentStorageAccount
        RollbackState TraceState)
    (slot value : Core.Word)
    (otherAddress : Address)
    (different : otherAddress ≠ context.context.storageAddress) :
    (context.writeStorage slot value).context.values.working.1.account?
        otherAddress =
      context.context.values.working.1.account? otherAddress := by
  exact WorldState.account?_putAccount_other
    context.context.values.working.1 context.context.storageAddress otherAddress
    (context.storageAccount.storageWrite slot value) different

end Solcore.ContractRuntime.FrameCheckpointedWorkingPairWithPresentStorageAccount

/-!
## Consolidated module: `Solcore.ContractRuntime.FrameCheckpointedWorkingPairWithPresentStorageAccountStorageWritePresenceProperties`
-/

/-! Sparse storage presence after proven-present total writes. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.FrameCheckpointedWorkingPairWithPresentStorageAccount

universe u v

/-- Writing zero removes the selected sparse-storage entry. -/
theorem storageValue?_writeStorage_zero
    {RollbackState : Type u} {TraceState : Type v}
    (context :
      FrameCheckpointedWorkingPairWithPresentStorageAccount
        RollbackState TraceState)
    (slot : Core.Word) :
    (context.writeStorage slot Core.Word.zero).storageAccount.storageValue?
        slot = none := by
  rw [storageAccount_writeStorage]
  exact Account.storageValue?_storageWrite_zero context.storageAccount slot

/-- Writing a nonzero word creates the corresponding sparse-storage entry. -/
theorem storageValue?_writeStorage_nonzero
    {RollbackState : Type u} {TraceState : Type v}
    (context :
      FrameCheckpointedWorkingPairWithPresentStorageAccount
        RollbackState TraceState)
    (slot value : Core.Word)
    (nonzero : value ≠ Core.Word.zero) :
    (context.writeStorage slot value).storageAccount.storageValue? slot =
      some value := by
  rw [storageAccount_writeStorage]
  exact Account.storageValue?_storageWrite_nonzero
    context.storageAccount slot value nonzero

end Solcore.ContractRuntime.FrameCheckpointedWorkingPairWithPresentStorageAccount

/-!
## Consolidated module: `Solcore.ContractRuntime.FrameCheckpointedWorkingPairWithPresentStorageAccountStorageWriteCodeProperties`
-/

/-! Checked-code preservation across total working-storage writes. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.FrameCheckpointedWorkingPairWithPresentStorageAccount

universe u v

/-- A storage write preserves checked code at every working-state address. -/
@[simp] theorem workingCode?_writeStorage
    {RollbackState : Type u}
    {TraceState : Type v}
    (context :
      FrameCheckpointedWorkingPairWithPresentStorageAccount
        RollbackState TraceState)
    (slot value : Core.Word)
    (codeAddress : Address) :
    (context.writeStorage slot value).context.values.working.1.code?
        codeAddress =
      context.context.values.working.1.code? codeAddress := by
  change
    ((context.context.values.working.1.putAccount
        context.context.storageAddress
        (context.storageAccount.storageWrite slot value)).account?
      codeAddress).bind (fun account => account.code?) =
    (context.context.values.working.1.account? codeAddress).bind
      (fun account => account.code?)
  by_cases same : codeAddress = context.context.storageAddress
  · subst codeAddress
    rw [WorldState.account?_putAccount_same]
    rw [context.storageAccount_present]
    simp
  · rw [WorldState.account?_putAccount_other _ _ _ _ same]

end Solcore.ContractRuntime.FrameCheckpointedWorkingPairWithPresentStorageAccount

/-!
## Consolidated module: `Solcore.ContractRuntime.FrameCheckpointedWorkingPairWithPresentStorageAccountStorageWriteSparsePreservationProperties`
-/

/-! Distinct-slot sparse-storage preservation for proven-present total writes. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.FrameCheckpointedWorkingPairWithPresentStorageAccount

universe u v

/-- A total write preserves the optional sparse entry at every other slot. -/
theorem storageValue?_writeStorage_other
    {RollbackState : Type u} {TraceState : Type v}
    (context :
      FrameCheckpointedWorkingPairWithPresentStorageAccount
        RollbackState TraceState)
    (writtenSlot value otherSlot : Core.Word)
    (different : otherSlot ≠ writtenSlot) :
    (context.writeStorage writtenSlot value).storageAccount.storageValue?
        otherSlot =
      context.storageAccount.storageValue? otherSlot := by
  rw [storageAccount_writeStorage]
  exact Account.storageValue?_storageWrite_other
    context.storageAccount writtenSlot value otherSlot different

end Solcore.ContractRuntime.FrameCheckpointedWorkingPairWithPresentStorageAccount

/-!
## Consolidated module: `Solcore.ContractRuntime.FrameCheckpointedWorkingPairWithPresentStorageAccountStorageWriteRefinementCoherenceProperties`
-/

/-! Canonical refinement coherence for proven-present optional storage writes. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.FrameCheckpointedWorkingPairWithPresentStorageAccount

universe u v

/-- Optional write followed by refinement recovers the total write result. -/
theorem context_writeStorage?_bind_withPresentStorageAccount?_eq_some_writeStorage
    {RollbackState : Type u} {TraceState : Type v}
    (context :
      FrameCheckpointedWorkingPairWithPresentStorageAccount
        RollbackState TraceState)
    (slot value : Core.Word) :
    (context.context.writeStorage? slot value).bind
        FrameCheckpointedWorkingPairWithStorageAddress.withPresentStorageAccount? =
      some (context.writeStorage slot value) := by
  rw [context_writeStorage?_eq_some_writeStorage_context]
  simp only [Option.bind_some]
  exact
    FrameCheckpointedWorkingPairWithStorageAddress.withPresentStorageAccount?_of_present
      (context.writeStorage slot value).context
      (context.writeStorage slot value).storageAccount
      (context.writeStorage slot value).storageAccount_present

end Solcore.ContractRuntime.FrameCheckpointedWorkingPairWithPresentStorageAccount
