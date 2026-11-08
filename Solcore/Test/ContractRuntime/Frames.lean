import Solcore.ContractRuntime.Internal.FrameLaws
import Solcore.ContractRuntime.Internal.ParentIndexedFrames

/-!
# Frame tests

Checkpointed working pairs and their storage reads and writes, continuation contexts, frame outcomes,
resolution and run results, traces and effect journals, with trap reason mapping.
-/

section
-- leanmerge: from Solcore.Test.FrameCheckpointSnapshot
/-! Definition-only compile regressions for nominal checkpoint snapshots. -/

set_option autoImplicit false

namespace Tests

open Solcore
open Solcore.ContractRuntime

universe u v

private example
    {RollbackState : Type u} {TraceState : Type v}
    (working : WorldState × FrameEffectJournal RollbackState TraceState) :
    FrameCheckpointSnapshot.fromWorkingPair working =
      (⟨working.1, working.2⟩ :
        FrameCheckpointSnapshot RollbackState TraceState) := by
  rfl

private def address : Address := ⟨0x12, by decide⟩
private def slot : Core.Word := ⟨0x34, by decide⟩
private def value : Core.Word := ⟨0x56, by decide⟩

private def concreteState : WorldState :=
  WorldState.empty.putAccount address
    (Account.empty.storageWrite slot value)

private def concreteEffects : FrameEffectJournal Nat (List Nat) :=
  ⟨37, [2, 3]⟩

private def concreteWorking :
    WorldState × FrameEffectJournal Nat (List Nat) :=
  (concreteState, concreteEffects)

private example :
    (FrameCheckpointSnapshot.fromWorkingPair concreteWorking).state =
      concreteState := by
  rfl

private example :
    (FrameCheckpointSnapshot.fromWorkingPair concreteWorking).effects =
      (⟨37, [2, 3]⟩ : FrameEffectJournal Nat (List Nat)) := by
  rfl

end Tests
end

section
-- leanmerge: from Solcore.Test.FrameCheckpointedWorkingPair
/-! Definition-only compile regressions for checkpointed working pairs. -/

set_option autoImplicit false

namespace Tests

open Solcore
open Solcore.ContractRuntime

universe u v

private example
    {RollbackState : Type u} {TraceState : Type v}
    (checkpoint : FrameCheckpointSnapshot RollbackState TraceState)
    (working : WorldState × FrameEffectJournal RollbackState TraceState) :
    (⟨checkpoint, working⟩ :
      FrameCheckpointedWorkingPair RollbackState TraceState) =
      FrameCheckpointedWorkingPair.mk checkpoint working := by
  rfl

private def checkpointValue : Core.Word := ⟨0x56, by decide⟩
private def workingValue : Core.Word := ⟨0x78, by decide⟩

private def stateWith (value : Core.Word) : WorldState :=
  WorldState.empty.putAccount address
    (Account.empty.storageWrite slot value)

private def checkpoint : FrameCheckpointSnapshot Nat (List Nat) :=
  ⟨stateWith checkpointValue, ⟨10, [1]⟩⟩

private def working : WorldState × FrameEffectJournal Nat (List Nat) :=
  (stateWith workingValue, ⟨20, [1, 2]⟩)

private def concrete : FrameCheckpointedWorkingPair Nat (List Nat) :=
  ⟨checkpoint, working⟩

private example :
    concrete.checkpoint =
      (⟨stateWith checkpointValue, ⟨10, [1]⟩⟩ :
        FrameCheckpointSnapshot Nat (List Nat)) := by
  rfl

private example :
    concrete.working =
      (stateWith workingValue,
        (⟨20, [1, 2]⟩ : FrameEffectJournal Nat (List Nat))) := by
  rfl

end Tests
end

section
-- leanmerge: from Solcore.Test.FrameCheckpointedWorkingPairStorageWrite
/-! Runtime regressions for checkpointed working-world storage writes. -/

set_option autoImplicit false

namespace Tests

open Solcore
open Solcore.ContractRuntime

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do
    throw (IO.userError message)

private def addressA : Address := ⟨0x12, by decide⟩
private def addressB : Address := ⟨0x34, by decide⟩
private def slotA : Core.Word := ⟨0x56, by decide⟩
private def slotB : Core.Word := ⟨0x78, by decide⟩
private def checkpointValue_variant : Core.Word := ⟨0x9a, by decide⟩
private def oldValue : Core.Word := ⟨0xbc, by decide⟩
private def replacement : Core.Word := ⟨0xde, by decide⟩
private def otherSlotValue : Core.Word := ⟨0xf0, by decide⟩
private def otherAccountValue : Core.Word := ⟨0x11, by decide⟩

private def checkpointState : WorldState :=
  WorldState.empty.putAccount addressA
    (Account.empty.storageWrite slotA checkpointValue_variant)

private def workingState : WorldState :=
  WorldState.empty
    |>.putAccount addressA
      (Account.empty.storageWrite slotA oldValue
        |>.storageWrite slotB otherSlotValue)
    |>.putAccount addressB
      (Account.empty.storageWrite slotB otherAccountValue)

private def checkpoint_variant : FrameCheckpointSnapshot Nat (List Nat) :=
  ⟨checkpointState, ⟨7, [8]⟩⟩

private def workingEffects : FrameEffectJournal Nat (List Nat) :=
  ⟨9, [10, 11]⟩

private def presentValues : FrameCheckpointedWorkingPair Nat (List Nat) :=
  ⟨checkpoint_variant, (workingState, workingEffects)⟩

private def absentValues : FrameCheckpointedWorkingPair Nat (List Nat) :=
  ⟨checkpoint_variant, (WorldState.empty, workingEffects)⟩

private def accountSlotEq
    (state : WorldState) (address : Address)
    (slot expected : Core.Word) : Bool :=
  match state.account? address with
  | none => false
  | some account => account.storageValue? slot == some expected

private def accountSlotAbsentButPresent
    (state : WorldState) (address : Address) (slot : Core.Word) : Bool :=
  match state.account? address with
  | none => false
  | some account =>
      account.storageValue? slot == none &&
        account.storageRead slot == Core.Word.zero

private def preserved
    (values : FrameCheckpointedWorkingPair Nat (List Nat)) : Bool :=
  accountSlotEq values.checkpoint.state addressA slotA checkpointValue_variant &&
    values.checkpoint.effects.rollback == 7 &&
    values.checkpoint.effects.trace == [8] &&
    values.working.2.rollback == 9 &&
    values.working.2.trace == [10, 11] &&
    accountSlotEq values.working.1 addressA slotB otherSlotValue &&
    accountSlotEq values.working.1 addressB slotB otherAccountValue

def testFrameCheckpointedWorkingPairStorageWrite : IO Unit := do
  assertTrue
    (accountSlotEq absentValues.checkpoint.state addressA slotA
        checkpointValue_variant &&
      (absentValues.writeWorkingStorage?
        addressA slotA replacement).isNone)
    "a checkpoint account must not rescue an absent working account"
  assertTrue
    (match presentValues.writeWorkingStorage? addressA slotA replacement with
      | none => false
      | some updated =>
          accountSlotEq updated.working.1 addressA slotA replacement &&
            preserved updated)
    "a nonzero write must update only the selected working storage slot"
  assertTrue
    (match presentValues.writeWorkingStorage?
        addressA slotA Core.Word.zero with
      | none => false
      | some updated =>
          accountSlotAbsentButPresent updated.working.1 addressA slotA &&
            preserved updated)
    "a zero write must delete only the selected working storage slot"

end Tests
end

section
-- leanmerge: from Solcore.Test.FrameCheckpointedWorkingPairStorageWriteAlgebra
/-! Compile-only regressions for checkpointed working storage-write algebra. -/

set_option autoImplicit false

namespace Tests

open Solcore
open Solcore.ContractRuntime

private example
    {RollbackState TraceState : Type}
    (values : FrameCheckpointedWorkingPair RollbackState TraceState)
    (address : Address) (slot first second : Core.Word) :
    (values.writeWorkingStorage? address slot first).bind
        (fun next => next.writeWorkingStorage? address slot second) =
      values.writeWorkingStorage? address slot second := by
  exact FrameCheckpointedWorkingPair.writeWorkingStorage?_overwrite
    values address slot first second

private example
    {RollbackState TraceState : Type}
    (values : FrameCheckpointedWorkingPair RollbackState TraceState)
    (address : Address)
    (leftSlot leftValue rightSlot rightValue : Core.Word)
    (different : leftSlot ≠ rightSlot) :
    (values.writeWorkingStorage? address leftSlot leftValue).bind
        (fun next =>
          next.writeWorkingStorage? address rightSlot rightValue) =
      (values.writeWorkingStorage? address rightSlot rightValue).bind
        (fun next =>
          next.writeWorkingStorage? address leftSlot leftValue) := by
  exact FrameCheckpointedWorkingPair.writeWorkingStorage?_commute_slots
    values address leftSlot leftValue rightSlot rightValue different

private example
    {RollbackState TraceState : Type}
    (values : FrameCheckpointedWorkingPair RollbackState TraceState)
    (leftAddress rightAddress : Address)
    (leftSlot leftValue rightSlot rightValue : Core.Word)
    (different : leftAddress ≠ rightAddress) :
    (values.writeWorkingStorage? leftAddress leftSlot leftValue).bind
        (fun next =>
          next.writeWorkingStorage? rightAddress rightSlot rightValue) =
      (values.writeWorkingStorage? rightAddress rightSlot rightValue).bind
        (fun next =>
          next.writeWorkingStorage? leftAddress leftSlot leftValue) := by
  exact FrameCheckpointedWorkingPair.writeWorkingStorage?_commute_addresses
    values leftAddress rightAddress leftSlot leftValue rightSlot rightValue
      different

end Tests
end

section
-- leanmerge: from Solcore.Test.FrameCheckpointedWorkingPairWithPresentStorageAccount
/-! Runtime regressions for selected working Account refinement. -/

set_option autoImplicit false

namespace Tests

open Solcore
open Solcore.ContractRuntime

private def addressA_variant : Address := ⟨0x21, by decide⟩
private def addressB_variant : Address := ⟨0x43, by decide⟩
private def slotA_variant : Core.Word := ⟨0x65, by decide⟩
private def slotB_variant : Core.Word := ⟨0x87, by decide⟩
private def checkpointValue_variant2 : Core.Word := ⟨0x91, by decide⟩
private def workingAA : Core.Word := ⟨0xa1, by decide⟩
private def workingAB : Core.Word := ⟨0xa2, by decide⟩
private def workingBA : Core.Word := ⟨0xb1, by decide⟩
private def workingBB : Core.Word := ⟨0xb2, by decide⟩

private def accountWith (valueA valueB : Core.Word) : Account :=
  Account.empty.storageWrite slotA_variant valueA |>.storageWrite slotB_variant valueB

private def checkpoint_variant2 : FrameCheckpointSnapshot Nat (List Nat) :=
  ⟨WorldState.empty.putAccount addressA_variant
      (Account.empty.storageWrite slotA_variant checkpointValue_variant2),
    ⟨17, [18]⟩⟩

private def effects : FrameEffectJournal Nat (List Nat) := ⟨27, [28, 29]⟩

private def contextAt (address : Address) (working : WorldState) :
    FrameCheckpointedWorkingPairWithStorageAddress Nat (List Nat) :=
  ⟨address, ⟨checkpoint_variant2, (working, effects)⟩⟩

private def onlyB : WorldState :=
  WorldState.empty.putAccount addressB_variant (accountWith workingBA workingBB)

private def emptyAWithB : WorldState := onlyB.putAccount addressA_variant Account.empty

private def full : WorldState :=
  onlyB.putAccount addressA_variant (accountWith workingAA workingAB)

private def storageReadEq
    (state : WorldState) (address : Address)
    (slot expected : Core.Word) : Bool :=
  match state.account? address with
  | none => false
  | some account => account.storageRead slot == expected

private def contextPreserved
    (refined :
      FrameCheckpointedWorkingPairWithPresentStorageAccount Nat (List Nat))
    (address : Address) (workingA workingB : Core.Word) : Bool :=
  refined.context.storageAddress == address &&
    storageReadEq refined.context.values.checkpoint.state
      addressA_variant slotA_variant checkpointValue_variant2 &&
    (refined.context.values.checkpoint.state.account? addressB_variant).isNone &&
    refined.context.values.checkpoint.effects.rollback == 17 &&
    refined.context.values.checkpoint.effects.trace == [18] &&
    storageReadEq refined.context.values.working.1
      addressA_variant slotA_variant workingA &&
    storageReadEq refined.context.values.working.1
      addressB_variant slotA_variant workingB &&
    refined.context.values.working.2.rollback == 27 &&
    refined.context.values.working.2.trace == [28, 29]

def testFrameCheckpointedWorkingPairWithPresentStorageAccount : IO Unit := do
  assertTrue
    ((contextAt addressA_variant onlyB).withPresentStorageAccount?.isNone &&
      (contextAt addressB_variant onlyB).withPresentStorageAccount?.isSome)
    "checkpoint presence and an unrelated working account must not rescue the target"
  assertTrue
    (match (contextAt addressA_variant emptyAWithB).withPresentStorageAccount? with
      | none => false
      | some refined =>
          contextPreserved refined addressA_variant Core.Word.zero workingBA &&
            refined.storageAccount.storageRead slotA_variant == Core.Word.zero &&
            refined.storageAccount.storageRead slotB_variant == Core.Word.zero)
    "a present empty working account must refine without changing its context"
  assertTrue
    (match (contextAt addressA_variant full).withPresentStorageAccount?,
        (contextAt addressB_variant full).withPresentStorageAccount? with
      | some refinedA, some refinedB =>
          contextPreserved refinedA addressA_variant workingAA workingBA &&
            contextPreserved refinedB addressB_variant workingAA workingBA &&
            refinedA.storageAccount.storageRead slotA_variant == workingAA &&
            refinedA.storageAccount.storageRead slotB_variant == workingAB &&
            refinedB.storageAccount.storageRead slotA_variant == workingBA &&
            refinedB.storageAccount.storageRead slotB_variant == workingBB
      | _, _ => false)
    "two selectors must recover exact Accounts and preserve their shared context"

end Tests
end

section
-- leanmerge: from Solcore.Test.FrameCheckpointedWorkingPairWithPresentStorageAccountProperties
/-! Compile-only regressions for selected working Account refinement laws. -/

set_option autoImplicit false

namespace Tests

open Solcore
open Solcore.ContractRuntime

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
end

section
-- leanmerge: from Solcore.Test.FrameCheckpointedWorkingPairWithPresentStorageAccountStorageRead
/-! Runtime regressions for total reads from a present selected working Account. -/

set_option autoImplicit false

namespace Tests

open Solcore
open Solcore.ContractRuntime

private def addressA_variant2 : Address := ⟨0x31, by decide⟩
private def addressB_variant2 : Address := ⟨0x53, by decide⟩
private def slotA_variant2 : Core.Word := ⟨0x75, by decide⟩
private def slotB_variant2 : Core.Word := ⟨0x97, by decide⟩
private def checkpointA : Core.Word := ⟨0xc1, by decide⟩
private def checkpointB : Core.Word := ⟨0xc2, by decide⟩
private def accountWith_variant (valueA valueB : Core.Word) : Account :=
  Account.empty.storageWrite slotA_variant2 valueA |>.storageWrite slotB_variant2 valueB

private def checkpoint_variant3 : FrameCheckpointSnapshot Nat (List Nat) :=
  ⟨WorldState.empty
      |>.putAccount addressA_variant2 (accountWith_variant checkpointA checkpointB)
      |>.putAccount addressB_variant2 (accountWith_variant checkpointB checkpointA),
    ⟨37, [38]⟩⟩

private def effects_variant : FrameEffectJournal Nat (List Nat) := ⟨47, [48, 49]⟩

private def contextAt_variant (state : WorldState) (address : Address) :
    FrameCheckpointedWorkingPairWithStorageAddress Nat (List Nat) :=
  ⟨address, ⟨checkpoint_variant3, (state, effects_variant)⟩⟩

private def emptyA : WorldState :=
  WorldState.empty
    |>.putAccount addressA_variant2 Account.empty
    |>.putAccount addressB_variant2 (accountWith_variant workingBA workingBB)

private def full_variant : WorldState :=
  emptyA.putAccount addressA_variant2 (accountWith_variant workingAA workingAB)

private def readRefined?
    (state : WorldState) (address : Address) (slot : Core.Word) :
    Option Core.Word :=
  (contextAt_variant state address).withPresentStorageAccount?.map
    (fun refined => refined.readStorage slot)

def testFrameCheckpointedWorkingPairWithPresentStorageAccountStorageRead :
    IO Unit := do
  assertTrue
    (readRefined? emptyA addressA_variant2 slotA_variant2 == some Core.Word.zero)
    "a present empty working Account must return the zero slot default"
  assertTrue
    (readRefined? full_variant addressA_variant2 slotA_variant2 == some workingAA &&
      readRefined? full_variant addressA_variant2 slotB_variant2 == some workingAB)
    "selector A must read both of its exact working slot values"
  assertTrue
    (readRefined? full_variant addressB_variant2 slotA_variant2 == some workingBA &&
      readRefined? full_variant addressB_variant2 slotB_variant2 == some workingBB)
    "selector B must read both values without cross-address confusion"

end Tests
end

section
-- leanmerge: from Solcore.Test.FrameCheckpointedWorkingPairWithPresentStorageAccountStorageReadProperties
/-! Compile-only regressions for proven-present total-read coherence. -/

set_option autoImplicit false

namespace Tests

open Solcore
open Solcore.ContractRuntime

private example
    {RollbackState TraceState : Type}
    (context :
      FrameCheckpointedWorkingPairWithPresentStorageAccount
        RollbackState TraceState)
    (slot : Core.Word) :
    context.context.readStorage? slot = some (context.readStorage slot) := by
  exact
    FrameCheckpointedWorkingPairWithPresentStorageAccount.context_readStorage?_eq_some_readStorage
      context slot

private example
    {RollbackState TraceState : Type}
    (context :
      FrameCheckpointedWorkingPairWithPresentStorageAccount
        RollbackState TraceState)
    (slot fallback : Core.Word) :
    (context.context.readStorage? slot).getD fallback =
      context.readStorage slot := by
  rw [FrameCheckpointedWorkingPairWithPresentStorageAccount.context_readStorage?_eq_some_readStorage]
  rfl

end Tests
end

section
-- leanmerge: from Solcore.Test.FrameCheckpointedWorkingPairWithPresentStorageAccountStorageReadWrite
/-! Compile-only regressions for proven-present total read/write coherence. -/

set_option autoImplicit false

namespace Tests

open Solcore
open Solcore.ContractRuntime

private example
    {RollbackState TraceState : Type}
    (context :
      FrameCheckpointedWorkingPairWithPresentStorageAccount
        RollbackState TraceState)
    (slot value : Core.Word) :
    (context.writeStorage slot value).readStorage slot = value := by
  exact
    FrameCheckpointedWorkingPairWithPresentStorageAccount.readStorage_writeStorage_same
      context slot value

private example
    {RollbackState TraceState : Type}
    (context :
      FrameCheckpointedWorkingPairWithPresentStorageAccount
        RollbackState TraceState)
    (writtenSlot value readSlot : Core.Word)
    (different : readSlot ≠ writtenSlot) :
    (context.writeStorage writtenSlot value).readStorage readSlot =
      context.readStorage readSlot := by
  exact
    FrameCheckpointedWorkingPairWithPresentStorageAccount.readStorage_writeStorage_other
      context writtenSlot value readSlot different

private example
    {RollbackState TraceState : Type}
    (context :
      FrameCheckpointedWorkingPairWithPresentStorageAccount
        RollbackState TraceState)
    (slot value : Core.Word) :
    (context.writeStorage slot value).context.readStorage? slot =
      some value := by
  rw [FrameCheckpointedWorkingPairWithPresentStorageAccount.context_readStorage?_eq_some_readStorage]
  rw [FrameCheckpointedWorkingPairWithPresentStorageAccount.readStorage_writeStorage_same]

end Tests
end

section
-- leanmerge: from Solcore.Test.FrameCheckpointedWorkingPairWithPresentStorageAccountStorageWrite
/-! Runtime regressions for total writes through a present selected working Account. -/

set_option autoImplicit false

namespace Tests

open Solcore
open Solcore.ContractRuntime

private def unrelatedA : Core.Word := ⟨0xb1, by decide⟩
private def unrelatedB : Core.Word := ⟨0xb2, by decide⟩
private def oldValue_variant : Core.Word := ⟨0xc1, by decide⟩
private def firstValue : Core.Word := ⟨0xd1, by decide⟩
private def secondValue : Core.Word := ⟨0xd2, by decide⟩
private def otherValue : Core.Word := ⟨0xe1, by decide⟩

private def contextAt_variant2 (working : WorldState) :
    FrameCheckpointedWorkingPairWithStorageAddress Nat (List Nat) :=
  ⟨addressA_variant, ⟨checkpoint_variant2, (working, effects)⟩⟩

private def unrelatedAccount : Account := accountWith unrelatedA unrelatedB

private def withSelected (account : Account) : WorldState :=
  WorldState.empty
    |>.putAccount addressB_variant unrelatedAccount
    |>.putAccount addressA_variant account

private def storageValueMissing
    (state : WorldState) (address : Address) (slot : Core.Word) : Bool :=
  match state.account? address with
  | none => false
  | some account => (account.storageValue? slot).isNone

private def contextPreserved_variant
    (context :
      FrameCheckpointedWorkingPairWithStorageAddress Nat (List Nat)) : Bool :=
  context.storageAddress == addressA_variant &&
    storageReadEq context.values.checkpoint.state
      addressA_variant slotA_variant checkpointValue_variant2 &&
    (context.values.checkpoint.state.account? addressB_variant).isNone &&
    context.values.checkpoint.effects.rollback == 17 &&
    context.values.checkpoint.effects.trace == [18] &&
    storageReadEq context.values.working.1 addressB_variant slotA_variant unrelatedA &&
    storageReadEq context.values.working.1 addressB_variant slotB_variant unrelatedB &&
    context.values.working.2.rollback == 27 &&
    context.values.working.2.trace == [28, 29]

def testFrameCheckpointedWorkingPairWithPresentStorageAccountStorageWrite :
    IO Unit := do
  assertTrue
    (match (contextAt_variant2
        (withSelected Account.empty)).withPresentStorageAccount? with
      | none => false
      | some refined =>
          let written := refined.writeStorage slotA_variant firstValue
          written.storageAccount.storageRead slotA_variant == firstValue &&
            storageReadEq written.context.values.working.1
              addressA_variant slotA_variant firstValue &&
            contextPreserved_variant written.context)
    "a nonzero write must synchronize the Account and retained context"
  assertTrue
    (match (contextAt_variant2 (withSelected
        (Account.empty.storageWrite slotA_variant oldValue_variant))).withPresentStorageAccount? with
      | none => false
      | some refined =>
          let written := refined.writeStorage slotA_variant Core.Word.zero
          (written.storageAccount.storageValue? slotA_variant).isNone &&
            written.storageAccount.storageRead slotA_variant == Core.Word.zero &&
            storageValueMissing written.context.values.working.1 addressA_variant slotA_variant &&
            contextPreserved_variant written.context)
    "a zero write must delete the slot without deleting the selected Account"
  assertTrue
    (match (contextAt_variant2 (withSelected
        (Account.empty.storageWrite slotB_variant otherValue))).withPresentStorageAccount? with
      | none => false
      | some refined =>
          let first := refined.writeStorage slotA_variant firstValue
          let second := first.writeStorage slotA_variant secondValue
          first.storageAccount.storageRead slotA_variant == firstValue &&
            storageReadEq first.context.values.working.1
              addressA_variant slotA_variant firstValue &&
            second.storageAccount.storageRead slotA_variant == secondValue &&
            second.storageAccount.storageRead slotB_variant == otherValue &&
            storageReadEq second.context.values.working.1
              addressA_variant slotA_variant secondValue &&
            storageReadEq second.context.values.working.1
              addressA_variant slotB_variant otherValue &&
            contextPreserved_variant second.context)
    "sequential overwrite must retain the other slot and frame context"

end Tests
end

section
-- leanmerge: from Solcore.Test.FrameCheckpointedWorkingPairWithPresentStorageAccountStorageWriteAlgebra
/-! Compile-only regressions for proven-present total write algebra. -/

set_option autoImplicit false

namespace Tests

private example
    {RollbackState TraceState : Type}
    (context :
      Solcore.ContractRuntime.FrameCheckpointedWorkingPairWithPresentStorageAccount
        RollbackState TraceState)
    (slot first second : Solcore.Core.Word) :
    (context.writeStorage slot first).writeStorage slot second =
      context.writeStorage slot second := by
  exact
    Solcore.ContractRuntime.FrameCheckpointedWorkingPairWithPresentStorageAccount.writeStorage_overwrite
      context slot first second

private example
    {RollbackState TraceState : Type}
    (context :
      Solcore.ContractRuntime.FrameCheckpointedWorkingPairWithPresentStorageAccount
        RollbackState TraceState)
    (leftSlot leftValue rightSlot rightValue : Solcore.Core.Word)
    (different : leftSlot ≠ rightSlot) :
    (context.writeStorage leftSlot leftValue).writeStorage
        rightSlot rightValue =
      (context.writeStorage rightSlot rightValue).writeStorage
        leftSlot leftValue := by
  exact
    Solcore.ContractRuntime.FrameCheckpointedWorkingPairWithPresentStorageAccount.writeStorage_commute_slots
      context leftSlot leftValue rightSlot rightValue different

end Tests
end

section
-- leanmerge: from Solcore.Test.FrameCheckpointedWorkingPairWithPresentStorageAccountStorageWriteIsolation
/-! Compile-only regressions for proven-present total-write isolation. -/

set_option autoImplicit false

namespace Tests

private example
    {RollbackState TraceState : Type}
    (context :
      Solcore.ContractRuntime.FrameCheckpointedWorkingPairWithPresentStorageAccount
        RollbackState TraceState)
    (slot value : Solcore.Core.Word)
    (otherAddress : Solcore.ContractRuntime.Address)
    (different : otherAddress ≠ context.context.storageAddress) :
    (context.writeStorage slot value).context.values.working.1.account?
        otherAddress =
      context.context.values.working.1.account? otherAddress := by
  exact
    Solcore.ContractRuntime.FrameCheckpointedWorkingPairWithPresentStorageAccount.workingAccount?_writeStorage_other
      context slot value otherAddress different

private example
    {RollbackState TraceState : Type}
    (context :
      Solcore.ContractRuntime.FrameCheckpointedWorkingPairWithPresentStorageAccount
        RollbackState TraceState)
    (firstSlot firstValue secondSlot secondValue : Solcore.Core.Word)
    (otherAddress : Solcore.ContractRuntime.Address)
    (different : otherAddress ≠ context.context.storageAddress) :
    ((context.writeStorage firstSlot firstValue).writeStorage
        secondSlot secondValue).context.values.working.1.account? otherAddress =
      context.context.values.working.1.account? otherAddress := by
  rw [
    Solcore.ContractRuntime.FrameCheckpointedWorkingPairWithPresentStorageAccount.workingAccount?_writeStorage_other
      (context.writeStorage firstSlot firstValue)
      secondSlot secondValue otherAddress different,
    Solcore.ContractRuntime.FrameCheckpointedWorkingPairWithPresentStorageAccount.workingAccount?_writeStorage_other
      context firstSlot firstValue otherAddress different]

end Tests
end

section
-- leanmerge: from Solcore.Test.FrameCheckpointedWorkingPairWithPresentStorageAccountStorageWritePresence
/-! Compile-only regressions for proven-present total-write presence. -/

set_option autoImplicit false

namespace Tests

private example
    {RollbackState TraceState : Type}
    (context :
      Solcore.ContractRuntime.FrameCheckpointedWorkingPairWithPresentStorageAccount
        RollbackState TraceState)
    (slot : Solcore.Core.Word) :
    (context.writeStorage slot Solcore.Core.Word.zero).storageAccount.storageValue?
        slot = none := by
  exact
    Solcore.ContractRuntime.FrameCheckpointedWorkingPairWithPresentStorageAccount.storageValue?_writeStorage_zero
      context slot

private example
    {RollbackState TraceState : Type}
    (context :
      Solcore.ContractRuntime.FrameCheckpointedWorkingPairWithPresentStorageAccount
        RollbackState TraceState)
    (slot value : Solcore.Core.Word)
    (nonzero : value ≠ Solcore.Core.Word.zero) :
    (context.writeStorage slot value).storageAccount.storageValue? slot =
      some value := by
  exact
    Solcore.ContractRuntime.FrameCheckpointedWorkingPairWithPresentStorageAccount.storageValue?_writeStorage_nonzero
      context slot value nonzero

end Tests
end

section
-- leanmerge: from Solcore.Test.FrameCheckpointedWorkingPairWithPresentStorageAccountStorageWriteProjection
/-! Compile-only regressions for proven-present total-write projections. -/

set_option autoImplicit false

namespace Tests

private example
    {RollbackState TraceState : Type}
    (context :
      Solcore.ContractRuntime.FrameCheckpointedWorkingPairWithPresentStorageAccount
        RollbackState TraceState)
    (slot value : Solcore.Core.Word) :
    (context.writeStorage slot value).context.storageAddress =
      context.context.storageAddress := by
  exact
    Solcore.ContractRuntime.FrameCheckpointedWorkingPairWithPresentStorageAccount.storageAddress_writeStorage
      context slot value

private example
    {RollbackState TraceState : Type}
    (context :
      Solcore.ContractRuntime.FrameCheckpointedWorkingPairWithPresentStorageAccount
        RollbackState TraceState)
    (slot value : Solcore.Core.Word) :
    (context.writeStorage slot value).context.values.checkpoint =
      context.context.values.checkpoint := by
  exact
    Solcore.ContractRuntime.FrameCheckpointedWorkingPairWithPresentStorageAccount.checkpoint_writeStorage
      context slot value

private example
    {RollbackState TraceState : Type}
    (context :
      Solcore.ContractRuntime.FrameCheckpointedWorkingPairWithPresentStorageAccount
        RollbackState TraceState)
    (slot value : Solcore.Core.Word) :
    (context.writeStorage slot value).context.values.working.2 =
      context.context.values.working.2 := by
  exact
    Solcore.ContractRuntime.FrameCheckpointedWorkingPairWithPresentStorageAccount.workingEffects_writeStorage
      context slot value

private example
    {RollbackState TraceState : Type}
    (context :
      Solcore.ContractRuntime.FrameCheckpointedWorkingPairWithPresentStorageAccount
        RollbackState TraceState)
    (slot value : Solcore.Core.Word) :
    (context.writeStorage slot value).storageAccount =
      context.storageAccount.storageWrite slot value := by
  exact
    Solcore.ContractRuntime.FrameCheckpointedWorkingPairWithPresentStorageAccount.storageAccount_writeStorage
      context slot value

private example
    {RollbackState TraceState : Type}
    (context :
      Solcore.ContractRuntime.FrameCheckpointedWorkingPairWithPresentStorageAccount
        RollbackState TraceState)
    (firstSlot firstValue secondSlot secondValue : Solcore.Core.Word)
    (otherAddress : Solcore.ContractRuntime.Address)
    (different : otherAddress ≠ context.context.storageAddress) :
    ((context.writeStorage firstSlot firstValue).writeStorage
        secondSlot secondValue).context.values.working.1.account? otherAddress =
      context.context.values.working.1.account? otherAddress := by
  simp [different]

end Tests
end

section
-- leanmerge: from Solcore.Test.FrameCheckpointedWorkingPairWithPresentStorageAccountStorageWriteProperties
/-! Compile-only regressions for proven-present total-write coherence. -/

set_option autoImplicit false

namespace Tests

open Solcore
open Solcore.ContractRuntime

private example
    {RollbackState TraceState : Type}
    (context :
      FrameCheckpointedWorkingPairWithPresentStorageAccount
        RollbackState TraceState)
    (slot value : Core.Word) :
    context.context.writeStorage? slot value =
      some (context.writeStorage slot value).context := by
  exact
    FrameCheckpointedWorkingPairWithPresentStorageAccount.context_writeStorage?_eq_some_writeStorage_context
      context slot value

private example
    {RollbackState TraceState Result : Type}
    (context :
      FrameCheckpointedWorkingPairWithPresentStorageAccount
        RollbackState TraceState)
    (slot value : Core.Word)
    (observe :
      FrameCheckpointedWorkingPairWithStorageAddress
        RollbackState TraceState → Result) :
    (context.context.writeStorage? slot value).map observe =
      some (observe (context.writeStorage slot value).context) := by
  rw [FrameCheckpointedWorkingPairWithPresentStorageAccount.context_writeStorage?_eq_some_writeStorage_context]
  rfl

private example
    {RollbackState TraceState : Type}
    (context :
      FrameCheckpointedWorkingPairWithPresentStorageAccount
        RollbackState TraceState)
    (slot value : Core.Word) :
    (context.context.writeStorage? slot value).bind
        FrameCheckpointedWorkingPairWithStorageAddress.withPresentStorageAccount? =
      some (context.writeStorage slot value) := by
  rw [FrameCheckpointedWorkingPairWithPresentStorageAccount.context_writeStorage?_eq_some_writeStorage_context]
  simp only [Option.bind_some]
  exact
    FrameCheckpointedWorkingPairWithStorageAddress.withPresentStorageAccount?_of_present
      (context.writeStorage slot value).context
      (context.writeStorage slot value).storageAccount
      (context.writeStorage slot value).storageAccount_present

end Tests
end

section
-- leanmerge: from Solcore.Test.FrameCheckpointedWorkingPairWithPresentStorageAccountStorageWriteRefinementCoherence
/-! Compile-only regressions for optional/total write re-refinement coherence. -/

set_option autoImplicit false

namespace Tests

private example
    {RollbackState TraceState : Type}
    (context :
      Solcore.ContractRuntime.FrameCheckpointedWorkingPairWithPresentStorageAccount
        RollbackState TraceState)
    (slot value : Solcore.Core.Word) :
    (context.context.writeStorage? slot value).bind
        Solcore.ContractRuntime.FrameCheckpointedWorkingPairWithStorageAddress.withPresentStorageAccount? =
      some (context.writeStorage slot value) := by
  exact
    Solcore.ContractRuntime.FrameCheckpointedWorkingPairWithPresentStorageAccount.context_writeStorage?_bind_withPresentStorageAccount?_eq_some_writeStorage
      context slot value

private example
    {RollbackState TraceState : Type}
    (context :
      Solcore.ContractRuntime.FrameCheckpointedWorkingPairWithPresentStorageAccount
        RollbackState TraceState)
    (firstSlot firstValue secondSlot secondValue : Solcore.Core.Word) :
    ((context.context.writeStorage? firstSlot firstValue).bind
        Solcore.ContractRuntime.FrameCheckpointedWorkingPairWithStorageAddress.withPresentStorageAccount?).bind
        (fun next =>
          (next.context.writeStorage? secondSlot secondValue).bind
            Solcore.ContractRuntime.FrameCheckpointedWorkingPairWithStorageAddress.withPresentStorageAccount?) =
      some
        ((context.writeStorage firstSlot firstValue).writeStorage
          secondSlot secondValue) := by
  rw [
    Solcore.ContractRuntime.FrameCheckpointedWorkingPairWithPresentStorageAccount.context_writeStorage?_bind_withPresentStorageAccount?_eq_some_writeStorage
      context firstSlot firstValue]
  exact
    Solcore.ContractRuntime.FrameCheckpointedWorkingPairWithPresentStorageAccount.context_writeStorage?_bind_withPresentStorageAccount?_eq_some_writeStorage
      (context.writeStorage firstSlot firstValue) secondSlot secondValue

end Tests
end

section
-- leanmerge: from Solcore.Test.FrameCheckpointedWorkingPairWithPresentStorageAccountStorageWriteSparsePreservation
/-! Compile-only regressions for distinct-slot sparse-storage preservation. -/

set_option autoImplicit false

namespace Tests

private example
    (account : Solcore.ContractRuntime.Account)
    (writtenSlot value otherSlot : Solcore.Core.Word)
    (different : otherSlot ≠ writtenSlot) :
    (account.storageWrite writtenSlot value).storageValue? otherSlot =
      account.storageValue? otherSlot := by
  exact Solcore.ContractRuntime.Account.storageValue?_storageWrite_other
    account writtenSlot value otherSlot different

private example
    {RollbackState TraceState : Type}
    (context :
      Solcore.ContractRuntime.FrameCheckpointedWorkingPairWithPresentStorageAccount
        RollbackState TraceState)
    (writtenSlot value otherSlot : Solcore.Core.Word)
    (different : otherSlot ≠ writtenSlot) :
    (context.writeStorage writtenSlot value).storageAccount.storageValue?
        otherSlot =
      context.storageAccount.storageValue? otherSlot := by
  exact
    Solcore.ContractRuntime.FrameCheckpointedWorkingPairWithPresentStorageAccount.storageValue?_writeStorage_other
      context writtenSlot value otherSlot different

end Tests
end

section
-- leanmerge: from Solcore.Test.FrameCheckpointedWorkingPairWithStorageAddress
/-! Runtime regressions for address-bound checkpointed working storage writes. -/

set_option autoImplicit false

namespace Tests

open Solcore
open Solcore.ContractRuntime

private def slot_variant : Core.Word := ⟨0x65, by decide⟩
private def checkpointA_variant : Core.Word := ⟨0x81, by decide⟩
private def checkpointB_variant : Core.Word := ⟨0x82, by decide⟩
private def oldA : Core.Word := ⟨0x91, by decide⟩
private def oldB : Core.Word := ⟨0x92, by decide⟩
private def newA : Core.Word := ⟨0xa1, by decide⟩
private def newB : Core.Word := ⟨0xa2, by decide⟩

private def stateWithTwo (valueA valueB : Core.Word) : WorldState :=
  WorldState.empty
    |>.putAccount addressA_variant (Account.empty.storageWrite slot_variant valueA)
    |>.putAccount addressB_variant (Account.empty.storageWrite slot_variant valueB)

private def checkpoint_variant4 : FrameCheckpointSnapshot Nat (List Nat) :=
  ⟨stateWithTwo checkpointA_variant checkpointB_variant, ⟨17, [18]⟩⟩

private def base : FrameCheckpointedWorkingPair Nat (List Nat) :=
  ⟨checkpoint_variant4, (stateWithTwo oldA oldB, effects)⟩

private def onlyB_variant : FrameCheckpointedWorkingPair Nat (List Nat) :=
  ⟨checkpoint_variant4,
    (WorldState.empty.putAccount addressB_variant
      (Account.empty.storageWrite slot_variant oldB), effects)⟩

private def slotEq
    (state : WorldState) (address : Address)
    (expected : Core.Word) : Bool :=
  match state.account? address with
  | none => false
  | some account => account.storageValue? slot_variant == some expected

private def framePreserved
    (values : FrameCheckpointedWorkingPair Nat (List Nat)) : Bool :=
  slotEq values.checkpoint.state addressA_variant checkpointA_variant &&
    slotEq values.checkpoint.state addressB_variant checkpointB_variant &&
    values.checkpoint.effects.rollback == 17 &&
    values.checkpoint.effects.trace == [18] &&
    values.working.2.rollback == 27 &&
    values.working.2.trace == [28, 29]

def testFrameCheckpointedWorkingPairWithStorageAddress : IO Unit := do
  let missing :=
    FrameCheckpointedWorkingPairWithStorageAddress.mk addressA_variant onlyB_variant
  let targetA :=
    FrameCheckpointedWorkingPairWithStorageAddress.mk addressA_variant base
  let targetB :=
    FrameCheckpointedWorkingPairWithStorageAddress.mk addressB_variant base
  assertTrue
    ((missing.values.working.1.account? addressA_variant).isNone &&
      slotEq missing.values.working.1 addressB_variant oldB &&
      slotEq missing.values.checkpoint.state addressA_variant checkpointA_variant &&
      framePreserved missing.values &&
      (missing.writeStorage? slot_variant newA).isNone)
    "an unrelated account and checkpoint account must not rescue the target"
  assertTrue
    (match targetA.writeStorage? slot_variant newA with
      | none => false
      | some updated =>
          updated.storageAddress == addressA_variant &&
            slotEq updated.values.working.1 addressA_variant newA &&
            slotEq updated.values.working.1 addressB_variant oldB &&
            framePreserved updated.values)
    "the first stored address must select and retain only the first account"
  assertTrue
    (match targetB.writeStorage? slot_variant newB with
      | none => false
      | some updated =>
          updated.storageAddress == addressB_variant &&
            slotEq updated.values.working.1 addressB_variant newB &&
            slotEq updated.values.working.1 addressA_variant oldA &&
            framePreserved updated.values)
    "the second stored address must select and retain only the second account"

end Tests
end

section
-- leanmerge: from Solcore.Test.FrameCheckpointedWorkingPairWithStorageAddressStorageRead
/-! Runtime regressions for address-bound working storage reads. -/

set_option autoImplicit false

namespace Tests

open Solcore
open Solcore.ContractRuntime

private def checkpointA_variant2 : Core.Word := ⟨0x91, by decide⟩
private def checkpointB_variant2 : Core.Word := ⟨0x92, by decide⟩
private def accountWith_variant2 (valueA valueB : Core.Word) : Account :=
  Account.empty
    |>.storageWrite slotA_variant valueA
    |>.storageWrite slotB_variant valueB

private def checkpointState_variant : WorldState :=
  WorldState.empty
    |>.putAccount addressA_variant (Account.empty.storageWrite slotA_variant checkpointA_variant2)
    |>.putAccount addressB_variant (Account.empty.storageWrite slotA_variant checkpointB_variant2)

private def checkpoint_variant5 : FrameCheckpointSnapshot Nat (List Nat) :=
  ⟨checkpointState_variant, ⟨7, [8]⟩⟩

private def effects_variant2 : FrameEffectJournal Nat (List Nat) :=
  ⟨9, [10, 11]⟩

private def pairWith
    (state : WorldState) : FrameCheckpointedWorkingPair Nat (List Nat) :=
  ⟨checkpoint_variant5, (state, effects_variant2)⟩

private def onlyB_variant2 : WorldState :=
  WorldState.empty.putAccount addressB_variant (accountWith_variant2 workingBA workingBB)

private def emptyAWithB_variant : WorldState :=
  onlyB_variant2.putAccount addressA_variant Account.empty

private def full_variant2 : WorldState :=
  onlyB_variant2.putAccount addressA_variant (accountWith_variant2 workingAA workingAB)

private def contextAt_variant3
    (address : Address) (state : WorldState) :
    FrameCheckpointedWorkingPairWithStorageAddress Nat (List Nat) :=
  ⟨address, pairWith state⟩

private def checkpointSlotA : Option Core.Word := do
  let account ← checkpoint_variant5.state.account? addressA_variant
  some (account.storageRead slotA_variant)

def testFrameCheckpointedWorkingPairWithStorageAddressStorageRead : IO Unit := do
  assertTrue
    (checkpointSlotA == some checkpointA_variant2 &&
      (contextAt_variant3 addressA_variant onlyB_variant2).readStorage? slotA_variant == none &&
      (contextAt_variant3 addressB_variant onlyB_variant2).readStorage? slotA_variant == some workingBA)
    "a checkpoint value and unrelated working Account must not rescue a read"
  assertTrue
    (checkpointSlotA == some checkpointA_variant2 &&
      (contextAt_variant3 addressA_variant emptyAWithB_variant).readStorage? slotA_variant ==
        some Core.Word.zero &&
      (contextAt_variant3 addressB_variant emptyAWithB_variant).readStorage? slotA_variant == some workingBA)
    "a present empty working Account must return zero, not checkpoint data"
  assertTrue
    ((contextAt_variant3 addressA_variant full_variant2).readStorage? slotA_variant == some workingAA &&
      (contextAt_variant3 addressA_variant full_variant2).readStorage? slotB_variant == some workingAB &&
      (contextAt_variant3 addressB_variant full_variant2).readStorage? slotA_variant == some workingBA &&
      (contextAt_variant3 addressB_variant full_variant2).readStorage? slotB_variant == some workingBB)
    "stored address and slot must select exact values from one working state"

end Tests
end

section
-- leanmerge: from Solcore.Test.FrameCheckpointedWorkingPairWithStorageAddressStorageReadWrite
/-! Compile-only regressions for address-bound storage read/write laws. -/

set_option autoImplicit false

namespace Tests

open Solcore
open Solcore.ContractRuntime

private example
    {RollbackState TraceState : Type}
    (context :
      FrameCheckpointedWorkingPairWithStorageAddress RollbackState TraceState)
    (slot value : Core.Word) :
    (context.writeStorage? slot value).map
        (fun next => next.readStorage? slot) =
      (context.values.working.1.account? context.storageAddress).map
        (fun _ => some value) := by
  simp

private example
    {RollbackState TraceState : Type}
    (context :
      FrameCheckpointedWorkingPairWithStorageAddress RollbackState TraceState)
    (writtenSlot value readSlot : Core.Word)
    (different : readSlot ≠ writtenSlot) :
    (context.writeStorage? writtenSlot value).map
        (fun next => next.readStorage? readSlot) =
      (context.values.working.1.account? context.storageAddress).map
        (fun _ => context.readStorage? readSlot) := by
  simp [different]

end Tests
end

section
-- leanmerge: from Solcore.Test.FrameCheckpointedWorkingPairWithStorageAddressStorageWriteAlgebra
/-! Compile-only regressions for retained-address storage-write algebra. -/

set_option autoImplicit false

namespace Tests

open Solcore
open Solcore.ContractRuntime

private example
    {RollbackState TraceState : Type}
    (context :
      FrameCheckpointedWorkingPairWithStorageAddress RollbackState TraceState)
    (slot first second : Core.Word) :
    (context.writeStorage? slot first).bind
        (fun next => next.writeStorage? slot second) =
      context.writeStorage? slot second := by
  exact
    FrameCheckpointedWorkingPairWithStorageAddress.writeStorage?_overwrite
      context slot first second

private example
    {RollbackState TraceState : Type}
    (context :
      FrameCheckpointedWorkingPairWithStorageAddress RollbackState TraceState)
    (leftSlot leftValue rightSlot rightValue : Core.Word)
    (different : leftSlot ≠ rightSlot) :
    (context.writeStorage? leftSlot leftValue).bind
        (fun next => next.writeStorage? rightSlot rightValue) =
      (context.writeStorage? rightSlot rightValue).bind
        (fun next => next.writeStorage? leftSlot leftValue) := by
  exact
    FrameCheckpointedWorkingPairWithStorageAddress.writeStorage?_commute_slots
      context leftSlot leftValue rightSlot rightValue different

end Tests
end

section
-- leanmerge: from Solcore.Test.FrameCheckpointedWorkingPairWithStorageAddressStorageWriteCoherence
/-! Compile-only regressions for retained-address write values coherence. -/

set_option autoImplicit false

namespace Tests

open Solcore
open Solcore.ContractRuntime

private example
    {RollbackState TraceState : Type}
    (context :
      FrameCheckpointedWorkingPairWithStorageAddress RollbackState TraceState)
    (slot value : Core.Word) :
    (context.writeStorage? slot value).map (fun next => next.values) =
      context.values.writeWorkingStorage?
        context.storageAddress slot value := by
  simp

private example
    {RollbackState TraceState Result : Type}
    (context :
      FrameCheckpointedWorkingPairWithStorageAddress RollbackState TraceState)
    (slot value : Core.Word)
    (observe :
      FrameCheckpointedWorkingPair RollbackState TraceState → Result) :
    (context.writeStorage? slot value).map
        (fun next => observe next.values) =
      (context.values.writeWorkingStorage?
        context.storageAddress slot value).map observe := by
  change (context.writeStorage? slot value).map
      (observe ∘ fun next => next.values) = _
  rw [← Option.map_map]
  rw [FrameCheckpointedWorkingPairWithStorageAddress.values_writeStorage?]

end Tests
end

section
-- leanmerge: from Solcore.Test.FrameCheckpointedWorkingPairWithStorageAddressStorageWritePreservation
/-! Compile-only regressions for retained-address storage-write preservation. -/

set_option autoImplicit false

namespace Tests

open Solcore
open Solcore.ContractRuntime

private example
    {RollbackState TraceState : Type}
    (context :
      FrameCheckpointedWorkingPairWithStorageAddress RollbackState TraceState)
    (slot value : Core.Word) :
    (context.writeStorage? slot value).map
        (fun next => next.storageAddress) =
      (context.values.working.1.account? context.storageAddress).map
        (fun _ => context.storageAddress) := by
  simp

private example
    {RollbackState TraceState : Type}
    (context :
      FrameCheckpointedWorkingPairWithStorageAddress RollbackState TraceState)
    (account : Account) (slot value : Core.Word)
    (present :
      context.values.working.1.account? context.storageAddress = some account) :
    (context.writeStorage? slot value).map
        (fun next => next.values.checkpoint) =
      some context.values.checkpoint := by
  rw [FrameCheckpointedWorkingPairWithStorageAddress.checkpoint_writeStorage?]
  simp [present]

private example
    {RollbackState TraceState : Type}
    (context :
      FrameCheckpointedWorkingPairWithStorageAddress RollbackState TraceState)
    (slot value : Core.Word)
    (absent :
      context.values.working.1.account? context.storageAddress = none) :
    (context.writeStorage? slot value).map
        (fun next => next.values.working.2) = none := by
  rw [FrameCheckpointedWorkingPairWithStorageAddress.workingEffects_writeStorage?]
  simp [absent]

end Tests
end

section
-- leanmerge: from Solcore.Test.FrameContinuationContext
/-! Executable tests for the caller-owned frame continuation context. -/

set_option autoImplicit false

namespace Tests

open Solcore
open Solcore.ContractRuntime

private inductive ContextReason where
  | marker

private def isReturnedPayload? : FrameOutcome ContextReason → Bool
  | .returned data => data == [0x12].toByteArray
  | _ => false

private def isEmptyRevert? : FrameOutcome ContextReason → Bool
  | .reverted data => data.isEmpty
  | _ => false

private def isMarker? : FrameOutcome ContextReason → Bool
  | .trapped .marker => true
  | _ => false

private def address_variant : Address := ⟨0, by decide⟩
private def slot_variant2 : Core.Word := ⟨0x11, by decide⟩
private def checkpointValue_variant3 : Core.Word := ⟨0xaa, by decide⟩
private def workingValue_variant : Core.Word := ⟨0xbb, by decide⟩

private def stateWith_variant (value : Core.Word) : WorldState :=
  WorldState.empty.putAccount address_variant (Account.empty.storageWrite slot_variant2 value)

private def stateCheckpoint : WorldState := stateWith_variant checkpointValue_variant3
private def workingWorld : WorldState := stateWith_variant workingValue_variant

private def effectCheckpoint : FrameEffectJournal Nat Nat := ⟨10, 100⟩
private def effectWorking : FrameEffectJournal Nat Nat := ⟨20, 200⟩

private def contextWith
    (outcome : FrameOutcome ContextReason) :
    FrameContinuationContext Nat Nat ContextReason :=
  ⟨stateCheckpoint, effectCheckpoint, effectWorking,
    ⟨workingWorld, outcome⟩⟩

private def observedValue? (state : WorldState) : Option Core.Word := do
  let account ← state.account? address_variant
  account.storageValue? slot_variant2

private def observeSelected
    (selected : WorldState × FrameEffectJournal Nat Nat) :
    Option (Option Core.Word × Nat × Nat) :=
  some (observedValue? selected.1, selected.2.rollback, selected.2.trace)

def testFrameContinuationContext : IO Unit := do
  let returnedContext := contextWith (.returned [0x12].toByteArray)
  let returnedObserved := returnedContext.continue? observeSelected
  assertTrue
    (observedValue? returnedContext.stateCheckpoint == some checkpointValue_variant3 &&
      returnedContext.effectCheckpoint.rollback == 10 &&
      returnedContext.effectCheckpoint.trace == 100 &&
      returnedContext.effectWorking.rollback == 20 &&
      returnedContext.effectWorking.trace == 200 &&
      observedValue? returnedContext.result.working == some workingValue_variant &&
      isReturnedPayload? returnedContext.result.outcome &&
      returnedObserved == some (some workingValue_variant, 20, 200))
    "return context must expose its inputs and continue with the working pair"

  let revertedContext := contextWith (.reverted [].toByteArray)
  let revertedObserved := revertedContext.continue? observeSelected
  assertTrue
    (isEmptyRevert? revertedContext.result.outcome &&
      revertedObserved == some (some checkpointValue_variant3, 10, 200))
    "revert context must restore checkpoint state and rollback with working trace"

  let trappedContext := contextWith (.trapped .marker)
  let trappedObserved := trappedContext.continue? observeSelected
  assertTrue
    (isMarker? trappedContext.result.outcome && trappedObserved.isNone)
    "trap context must preserve its reason and skip the sentinel continuation"

end Tests
end

section
-- leanmerge: from Solcore.Test.FrameContinuationContextContinueTrapReasonMap
/-! Compile-only regressions for continuation-result invariance. -/

set_option autoImplicit false

namespace Tests

open Solcore.ContractRuntime

universe u v w x y z

private example
    {RollbackState : Type u} {TraceState : Type v}
    {TrapReason : Type w} {MappedTrapReason : Type x} {Next : Type y}
    (mapReason : TrapReason → MappedTrapReason)
    (context : FrameContinuationContext RollbackState TraceState TrapReason)
    (next :
      (WorldState × FrameEffectJournal RollbackState TraceState) →
        Option Next) :
    (context.mapTrapReason mapReason).continue? next = context.continue? next := by
  simp

private example
    {RollbackState : Type u} {TraceState : Type v}
    {TrapReason : Type w} {IntermediateTrapReason : Type x}
    {MappedTrapReason : Type y} {Next : Type z}
    (first : TrapReason → IntermediateTrapReason)
    (second : IntermediateTrapReason → MappedTrapReason)
    (context : FrameContinuationContext RollbackState TraceState TrapReason)
    (next :
      (WorldState × FrameEffectJournal RollbackState TraceState) →
        Option Next) :
    ((context.mapTrapReason first).mapTrapReason second).continue? next =
      context.continue? next := by
  simp

end Tests
end

section
-- leanmerge: from Solcore.Test.FrameContinuationContextFromCheckpointedWorkingPair
/-! Definition-only compile regressions for continuation-context construction. -/

set_option autoImplicit false

namespace Tests

open Solcore
open Solcore.ContractRuntime

universe u v w

private example
    {RollbackState : Type u} {TraceState : Type v} {TrapReason : Type w}
    (values : FrameCheckpointedWorkingPair RollbackState TraceState)
    (outcome : FrameOutcome TrapReason) :
    FrameContinuationContext.fromCheckpointedWorkingPair values outcome =
      ({
        stateCheckpoint := values.checkpoint.state
        effectCheckpoint := values.checkpoint.effects
        effectWorking := values.working.2
        result := ⟨values.working.1, outcome⟩
      } : FrameContinuationContext RollbackState TraceState TrapReason) := by
  rfl

private inductive Reason where
  | marker
  | other

private def checkpointState_variant2 : WorldState := stateWith checkpointValue
private def workingState_variant : WorldState := stateWith workingValue

private def checkpointEffects : FrameEffectJournal Nat (List Nat) :=
  ⟨10, [1]⟩

private def workingEffects_variant : FrameEffectJournal Nat (List Nat) :=
  ⟨20, [1, 2]⟩

private def values : FrameCheckpointedWorkingPair Nat (List Nat) :=
  ⟨⟨checkpointState_variant2, checkpointEffects⟩, (workingState_variant, workingEffects_variant)⟩

private def outcome : FrameOutcome Reason :=
  .returned [0x12, 0xff].toByteArray

private def context : FrameContinuationContext Nat (List Nat) Reason :=
  FrameContinuationContext.fromCheckpointedWorkingPair values outcome

private example :
    (context.stateCheckpoint, context.effectCheckpoint, context.effectWorking) =
      (checkpointState_variant2, checkpointEffects, workingEffects_variant) := by
  rfl

private example :
    context.result =
      ⟨workingState_variant, FrameOutcome.returned [0x12, 0xff].toByteArray⟩ := by
  rfl

end Tests
end

section
-- leanmerge: from Solcore.Test.FrameContinuationContextResolutionContinuationCoherence
/-! Compile-only regressions for branch/byte erasure coherence. -/

set_option autoImplicit false

namespace Tests

open Solcore.ContractRuntime

universe u v w x y

private example
    {RollbackState : Type u} {TraceState : Type v}
    {TrapReason : Type w} {Next : Type x}
    (context : FrameContinuationContext RollbackState TraceState TrapReason)
    (next :
      (WorldState × FrameEffectJournal RollbackState TraceState) →
        Option Next) :
    context.resolve.continue?
        (fun selected _ => next selected)
        (fun selected _ => next selected) =
      context.continue? next := by
  exact FrameContinuationContext.resolve_continue?_ignoreBranchAndBytes
    context next

private example
    {RollbackState : Type u} {TraceState : Type v}
    {TrapReason : Type w} {MappedTrapReason : Type x}
    {Next : Type y}
    (mapReason : TrapReason → MappedTrapReason)
    (context : FrameContinuationContext RollbackState TraceState TrapReason)
    (next :
      (WorldState × FrameEffectJournal RollbackState TraceState) →
        Option Next) :
    (context.mapTrapReason mapReason).resolve.continue?
        (fun selected _ => next selected)
        (fun selected _ => next selected) =
      context.continue? next := by
  rw [FrameContinuationContext.resolve_continue?_ignoreBranchAndBytes]
  exact FrameContinuationContext.continue?_mapTrapReason
    mapReason context next

end Tests
end

section
-- leanmerge: from Solcore.Test.FrameContinuationContextResolveTrapReasonMap
/-! Compile-only regressions for resolution naturality. -/

set_option autoImplicit false

namespace Tests

open Solcore.ContractRuntime

universe u v w x y

private example
    {RollbackState : Type u} {TraceState : Type v}
    {TrapReason : Type w} {MappedTrapReason : Type x}
    (mapReason : TrapReason → MappedTrapReason)
    (context : FrameContinuationContext RollbackState TraceState TrapReason) :
    (context.mapTrapReason mapReason).resolve =
      context.resolve.mapTrapReason mapReason := by
  simp

private example
    {RollbackState : Type u} {TraceState : Type v}
    {TrapReason : Type w} {IntermediateTrapReason : Type x}
    {MappedTrapReason : Type y}
    (first : TrapReason → IntermediateTrapReason)
    (second : IntermediateTrapReason → MappedTrapReason)
    (context : FrameContinuationContext RollbackState TraceState TrapReason) :
    ((context.mapTrapReason first).mapTrapReason second).resolve =
      context.resolve.mapTrapReason
        (fun reason => second (first reason)) := by
  simp

end Tests
end

section
-- leanmerge: from Solcore.Test.FrameContinuationContextTrapReasonMap
/-! Definition-only tests for continuation-context trap-reason mapping. -/

set_option autoImplicit false

namespace Tests

open Solcore
open Solcore.ContractRuntime

private inductive LocalTrapReason where
  | marker
  | other

private inductive MappedTrapReason where
  | mapped
  | other

private def mapReason : LocalTrapReason → MappedTrapReason
  | .marker => .mapped
  | .other => .other

private def returnCheckpointValue : Core.Word := ⟨0x10, by decide⟩
private def returnWorkingValue : Core.Word := ⟨0x11, by decide⟩
private def revertCheckpointValue : Core.Word := ⟨0x20, by decide⟩
private def revertWorkingValue : Core.Word := ⟨0x21, by decide⟩
private def trapCheckpointValue : Core.Word := ⟨0x30, by decide⟩
private def trapWorkingValue : Core.Word := ⟨0x31, by decide⟩

private def returnEffectCheckpoint : FrameEffectJournal Nat Nat := ⟨10, 100⟩
private def returnEffectWorking : FrameEffectJournal Nat Nat := ⟨11, 101⟩
private def revertEffectCheckpoint : FrameEffectJournal Nat Nat := ⟨20, 200⟩
private def revertEffectWorking : FrameEffectJournal Nat Nat := ⟨21, 201⟩
private def trapEffectCheckpoint : FrameEffectJournal Nat Nat := ⟨30, 300⟩
private def trapEffectWorking : FrameEffectJournal Nat Nat := ⟨31, 301⟩

private def returnBytes : Bytes :=
  [0x12, 0x00].toByteArray

private def revertBytes : Bytes :=
  [0x34, 0xff].toByteArray

private def contextWith_variant
    (checkpointValue workingValue : Core.Word)
    (effectCheckpoint effectWorking : FrameEffectJournal Nat Nat)
    (outcome : FrameOutcome LocalTrapReason) :
    FrameContinuationContext Nat Nat LocalTrapReason :=
  ⟨stateWith_variant checkpointValue, effectCheckpoint, effectWorking,
    ⟨stateWith_variant workingValue, outcome⟩⟩

private def matchesReturned :
    FrameContinuationContext Nat Nat MappedTrapReason → Bool
  | ⟨checkpoint, effectCheckpoint, effectWorking,
      ⟨working, .returned data⟩⟩ =>
      observedValue? checkpoint == some returnCheckpointValue &&
        effectCheckpoint.rollback == 10 && effectCheckpoint.trace == 100 &&
        effectWorking.rollback == 11 && effectWorking.trace == 101 &&
        observedValue? working == some returnWorkingValue && data == returnBytes
  | _ => false

private def matchesReverted :
    FrameContinuationContext Nat Nat MappedTrapReason → Bool
  | ⟨checkpoint, effectCheckpoint, effectWorking,
      ⟨working, .reverted data⟩⟩ =>
      observedValue? checkpoint == some revertCheckpointValue &&
        effectCheckpoint.rollback == 20 && effectCheckpoint.trace == 200 &&
        effectWorking.rollback == 21 && effectWorking.trace == 201 &&
        observedValue? working == some revertWorkingValue && data == revertBytes
  | _ => false

private def matchesMappedTrap :
    FrameContinuationContext Nat Nat MappedTrapReason → Bool
  | ⟨checkpoint, effectCheckpoint, effectWorking,
      ⟨working, .trapped .mapped⟩⟩ =>
      observedValue? checkpoint == some trapCheckpointValue &&
        effectCheckpoint.rollback == 30 && effectCheckpoint.trace == 300 &&
        effectWorking.rollback == 31 && effectWorking.trace == 301 &&
        observedValue? working == some trapWorkingValue
  | _ => false

def testFrameContinuationContextTrapReasonMap : IO Unit := do
  assertTrue
    (matchesReturned
      (FrameContinuationContext.mapTrapReason mapReason
        (contextWith_variant returnCheckpointValue returnWorkingValue
          returnEffectCheckpoint returnEffectWorking (.returned returnBytes))))
    "return mapping must preserve every context field and exact bytes"

  assertTrue
    (matchesReverted
      (FrameContinuationContext.mapTrapReason mapReason
        (contextWith_variant revertCheckpointValue revertWorkingValue
          revertEffectCheckpoint revertEffectWorking (.reverted revertBytes))))
    "revert mapping must preserve distinct context fields and exact bytes"

  assertTrue
    (matchesMappedTrap
      (FrameContinuationContext.mapTrapReason mapReason
        (contextWith_variant trapCheckpointValue trapWorkingValue
          trapEffectCheckpoint trapEffectWorking (.trapped .marker))))
    "trap mapping must preserve every context field and map the exact reason"

end Tests
end

section
-- leanmerge: from Solcore.Test.FrameContinuationContextWithTracePrefix
/-! Definition-only regressions for frame contexts with trace-prefix evidence. -/

set_option autoImplicit false

namespace Tests

open Solcore.ContractRuntime

private inductive ContextTraceEvent where
  | entered
  | completed

private inductive ContextTraceReason where
  | marker

private def checkpointTrace : FrameTrace ContextTraceEvent :=
  FrameTrace.record FrameTrace.empty .entered

private def completionFragment : FrameTrace ContextTraceEvent :=
  FrameTrace.record FrameTrace.empty .completed

private def baseContext :
    FrameContinuationContext Nat (FrameTrace ContextTraceEvent)
      ContextTraceReason :=
  ⟨WorldState.empty, ⟨10, checkpointTrace⟩,
    ⟨20, FrameTrace.append checkpointTrace completionFragment⟩,
    ⟨WorldState.empty, .trapped .marker⟩⟩

private def contextWithTracePrefix :
    FrameContinuationContextWithTracePrefix Nat ContextTraceEvent
      ContextTraceReason :=
  ⟨baseContext, ⟨completionFragment, rfl⟩⟩

private example :
    FrameContinuationContextWithTracePrefix Nat ContextTraceEvent
      ContextTraceReason :=
  ⟨baseContext, ⟨completionFragment, rfl⟩⟩

private example :
    FrameTrace.IsPrefixOf
      contextWithTracePrefix.effectCheckpoint.trace
      contextWithTracePrefix.effectWorking.trace :=
  contextWithTracePrefix.tracePrefix

private example :
    contextWithTracePrefix.resolve =
      contextWithTracePrefix.toFrameContinuationContext.resolve := by
  rfl

end Tests
end

section
-- leanmerge: from Solcore.Test.FrameContinuationContextWithTracePrefixTrapReasonMap
/-! Definition-only compile regressions for trace-prefixed reason mapping. -/

set_option autoImplicit false

namespace Tests

open Solcore
open Solcore.ContractRuntime

universe u v w x

private example
    {RollbackState : Type u} {Event : Type v}
    {TrapReason : Type w} {MappedTrapReason : Type x}
    (mapReason : TrapReason → MappedTrapReason)
    (context :
      FrameContinuationContext RollbackState (FrameTrace Event) TrapReason)
    (tracePrefix :
      FrameTrace.IsPrefixOf
        context.effectCheckpoint.trace context.effectWorking.trace) :
    FrameContinuationContextWithTracePrefix.mapTrapReason mapReason
        (⟨context, tracePrefix⟩ :
          FrameContinuationContextWithTracePrefix
            RollbackState Event TrapReason) =
      (⟨context.mapTrapReason mapReason, tracePrefix⟩ :
        FrameContinuationContextWithTracePrefix
          RollbackState Event MappedTrapReason) := by
  rfl

private example
    {RollbackState : Type u} {Event : Type v}
    {TrapReason : Type w} {MappedTrapReason : Type x}
    (mapReason : TrapReason → MappedTrapReason)
    (context :
      FrameContinuationContextWithTracePrefix
        RollbackState Event TrapReason) :
    FrameTrace.IsPrefixOf
      context.effectCheckpoint.trace context.effectWorking.trace :=
  (context.mapTrapReason mapReason).tracePrefix

private inductive SourceReason where
  | marker
  | other

private inductive TargetReason where
  | mapped
  | other

private def mapReason_variant : SourceReason → TargetReason
  | .marker => .mapped
  | .other => .other

private inductive Event where
  | checkpoint
  | working

private def checkpointTrace_variant : FrameTrace Event :=
  FrameTrace.record FrameTrace.empty .checkpoint

private def suffix : FrameTrace Event :=
  FrameTrace.record FrameTrace.empty .working

private def workingTrace : FrameTrace Event :=
  FrameTrace.append checkpointTrace_variant suffix

private def checkpointJournal : FrameEffectJournal Nat (FrameTrace Event) :=
  ⟨10, checkpointTrace_variant⟩

private def workingJournal : FrameEffectJournal Nat (FrameTrace Event) :=
  ⟨20, workingTrace⟩

private def concreteContext :
    FrameContinuationContextWithTracePrefix Nat Event SourceReason :=
  ⟨⟨stateWith_variant checkpointValue_variant3, checkpointJournal, workingJournal,
      ⟨stateWith_variant workingValue_variant, .trapped .marker⟩⟩,
    ⟨suffix, rfl⟩⟩

private example :
    (concreteContext.mapTrapReason mapReason_variant).toFrameContinuationContext =
      (⟨stateWith_variant checkpointValue_variant3, checkpointJournal, workingJournal,
        ⟨stateWith_variant workingValue_variant, FrameOutcome.trapped .mapped⟩⟩ :
        FrameContinuationContext Nat (FrameTrace Event) TargetReason) := by
  rfl

end Tests
end

section
-- leanmerge: from Solcore.Test.FrameEffectJournal
/-! Executable tests for rollback-scoped and surviving effect snapshots. -/

set_option autoImplicit false

namespace Tests

open Solcore.ContractRuntime

private inductive JournalTrapReason where
  | invalidOperation

private def parentCheckpoint : FrameEffectJournal Nat Nat :=
  ⟨10, 100⟩

private def childCheckpoint : FrameEffectJournal Nat Nat :=
  ⟨20, 200⟩

private def childWorking : FrameEffectJournal Nat Nat :=
  ⟨30, 300⟩

private def matches?
    (journal? : Option (FrameEffectJournal Nat Nat))
    (rollback trace : Nat) : Bool :=
  match journal? with
  | some journal => journal.rollback == rollback && journal.trace == trace
  | none => false

def testFrameEffectJournal : IO Unit := do
  let returnData := [0x12, 0].toByteArray
  let revertData := [].toByteArray
  let returned : FrameOutcome JournalTrapReason := .returned returnData
  let reverted : FrameOutcome JournalTrapReason := .reverted revertData
  let trapped : FrameOutcome JournalTrapReason := .trapped .invalidOperation
  assertTrue
    (matches? (FrameEffectJournal.resolved?
      parentCheckpoint childWorking returned) 30 300)
    "a returned frame must keep both working rollback and trace snapshots"
  assertTrue
    (matches? (FrameEffectJournal.resolved?
      parentCheckpoint childWorking reverted) 10 300)
    "a reverted frame must restore checkpoint rollback while keeping working trace"
  assertTrue
    (FrameEffectJournal.resolved? parentCheckpoint childWorking trapped).isNone
    "a trapped frame must leave effect-journal disposition unresolved"
  let childReturned :=
    FrameEffectJournal.resolved? childCheckpoint childWorking returned
  let childReturnThenParentRevert := childReturned.bind fun childResolved =>
    FrameEffectJournal.resolved? parentCheckpoint childResolved reverted
  assertTrue (matches? childReturnThenParentRevert 10 300)
    "a parent revert must roll back a returned child while preserving its trace"
  let childReverted :=
    FrameEffectJournal.resolved? childCheckpoint childWorking reverted
  let childRevertThenParentRevert := childReverted.bind fun childResolved =>
    FrameEffectJournal.resolved? parentCheckpoint childResolved reverted
  assertTrue (matches? childRevertThenParentRevert 10 300)
    "child and parent reverts must restore parent rollback and preserve child trace"

end Tests
end

section
-- leanmerge: from Solcore.Test.FrameOutcome
/-! Executable boundary tests for internal contract-frame halt outcomes. -/

set_option autoImplicit false

namespace Tests

open Solcore.ContractRuntime

private inductive TestTrapReason where
  | invalidOperation
  | resourceLimit
  deriving BEq, DecidableEq

private def bytes (values : List UInt8) : ByteArray :=
  values.toByteArray

def testFrameOutcome : IO Unit := do
  let empty := bytes []
  let padded := bytes [0, 0x12, 0]
  let returnedEmpty : FrameOutcome TestTrapReason := .returned empty
  let returnedPadded : FrameOutcome TestTrapReason := .returned padded
  let revertedEmpty : FrameOutcome TestTrapReason := .reverted empty
  let revertedPadded : FrameOutcome TestTrapReason := .reverted padded
  let trappedInvalid : FrameOutcome TestTrapReason :=
    .trapped .invalidOperation
  let trappedLimit : FrameOutcome TestTrapReason :=
    .trapped .resourceLimit

  assertTrue
    (returnedEmpty.kind == .returned &&
      revertedEmpty.kind == .reverted &&
      trappedInvalid.kind == .trapped)
    "each frame outcome must report its own halt kind"
  assertTrue
    (returnedEmpty.returndata? == some empty &&
      returnedEmpty.returndata? != none)
    "an empty successful payload must remain some empty bytes, not absence"
  assertTrue
    (returnedEmpty.revertdata?.isNone && returnedEmpty.trapReason?.isNone)
    "a returned outcome must expose neither revert data nor a trap reason"
  assertTrue (returnedPadded.returndata? == some padded)
    "returned data must retain leading and trailing zero octets"
  assertTrue
    (revertedEmpty.revertdata? == some empty &&
      revertedEmpty.revertdata? != none)
    "an empty revert payload must remain some empty bytes, not absence"
  assertTrue
    (revertedEmpty.returndata?.isNone && revertedEmpty.trapReason?.isNone)
    "a reverted outcome must expose neither return data nor a trap reason"
  assertTrue (revertedPadded.revertdata? == some padded)
    "revert data must retain leading and trailing zero octets"
  assertTrue
    (trappedInvalid.trapReason? == some .invalidOperation &&
      trappedLimit.trapReason? == some .resourceLimit &&
      trappedInvalid != trappedLimit)
    "trap reasons must survive projection without merging distinct reasons"
  assertTrue
    (trappedInvalid.returndata?.isNone && trappedInvalid.revertdata?.isNone)
    "a trapped outcome must expose neither return data nor revert data"
  assertTrue
    (returnedEmpty != revertedEmpty &&
      returnedEmpty != trappedInvalid &&
      revertedEmpty != trappedInvalid)
    "returned, reverted, and trapped outcomes must remain distinct constructors"

end Tests
end

section
-- leanmerge: from Solcore.Test.FrameOutcomeTrapReasonMap
/-! Definition-only tests for heterogeneous frame trap-reason mapping. -/

set_option autoImplicit false

namespace Tests

open Solcore.ContractRuntime

private def matchesReturned_variant : FrameOutcome MappedTrapReason → Bool
  | .returned data => data == returnBytes
  | _ => false

private def matchesReverted_variant : FrameOutcome MappedTrapReason → Bool
  | .reverted data => data == revertBytes
  | _ => false

private def matchesMappedTrap_variant : FrameOutcome MappedTrapReason → Bool
  | .trapped .mapped => true
  | _ => false

def testFrameOutcomeTrapReasonMap : IO Unit := do
  assertTrue
    (matchesReturned_variant
      (FrameOutcome.mapTrapReason mapReason
        (FrameOutcome.returned (TrapReason := LocalTrapReason) returnBytes)))
    "return bytes must survive trap-reason mapping"

  assertTrue
    (matchesReverted_variant
      (FrameOutcome.mapTrapReason mapReason
        (FrameOutcome.reverted (TrapReason := LocalTrapReason) revertBytes)))
    "revert bytes must survive trap-reason mapping"

  assertTrue
    (matchesMappedTrap_variant
      (FrameOutcome.mapTrapReason mapReason
        (FrameOutcome.trapped LocalTrapReason.marker)))
    "a trapped reason must map to the exact target constructor"

end Tests
end

section
-- leanmerge: from Solcore.Test.FrameResolutionResult
/-! Executable tests for total frame resolution. -/

set_option autoImplicit false

namespace Tests

open Solcore
open Solcore.ContractRuntime

private inductive ResolutionReason where
  | marker

private def contextWith_variant2
    (outcome : FrameOutcome ResolutionReason) :
    FrameContinuationContext Nat Nat ResolutionReason :=
  ⟨stateCheckpoint, effectCheckpoint, effectWorking,
    ⟨workingWorld, outcome⟩⟩

private def matchesReturn? :
    FrameResolutionResult Nat Nat ResolutionReason → Bool
  | .returned state effects data =>
      observedValue? state == some workingValue_variant &&
        effects.rollback == 20 && effects.trace == 200 &&
        data == [0x12].toByteArray
  | _ => false

private def matchesRevert? :
    FrameResolutionResult Nat Nat ResolutionReason → Bool
  | .reverted state effects data =>
      observedValue? state == some checkpointValue_variant3 &&
        effects.rollback == 10 && effects.trace == 200 &&
        data == [0x34].toByteArray
  | _ => false

private def matchesTrap? :
    FrameResolutionResult Nat Nat ResolutionReason → Bool
  | .trapped .marker => true
  | _ => false

def testFrameResolutionResult : IO Unit := do
  assertTrue
    (matchesReturn? (contextWith_variant2 (.returned [0x12].toByteArray)).resolve)
    "return resolution must preserve working state, effects, and payload"

  assertTrue
    (matchesRevert? (contextWith_variant2 (.reverted [0x34].toByteArray)).resolve)
    "revert resolution must select checkpoint rollback and working trace"

  assertTrue
    (matchesTrap? (contextWith_variant2 (.trapped .marker)).resolve)
    "trap resolution must preserve only the concrete reason"

end Tests
end

section
-- leanmerge: from Solcore.Test.FrameResolutionResultContinuation
/-! Executable branch and payload tests for frame resolution continuation. -/

set_option autoImplicit false

namespace Tests

open Solcore
open Solcore.ContractRuntime

private def returnedValue : Core.Word := ⟨0x56, by decide⟩
private def revertedValue : Core.Word := ⟨0x78, by decide⟩

private def returnedState : WorldState := stateWith returnedValue
private def revertedState : WorldState := stateWith revertedValue

private def returnedEffects : FrameEffectJournal Nat (List Nat) :=
  ⟨10, [1]⟩

private def revertedEffects : FrameEffectJournal Nat (List Nat) :=
  ⟨20, [2, 3]⟩

private def returnedBytes : Bytes := [0, 0x12].toByteArray
private def revertedBytes : Bytes := [0x34, 0xff].toByteArray

private def observedValue_variant? (state : WorldState) : Option Core.Word := do
  let account ← state.account? address
  account.storageValue? slot

private def onReturned
    (selected : WorldState × FrameEffectJournal Nat (List Nat))
    (data : Bytes) : Option Nat :=
  if observedValue_variant? selected.1 == some returnedValue &&
      selected.2.rollback == 10 && selected.2.trace == [1] &&
      data == returnedBytes then
    some 11
  else
    some 91

private def onReverted
    (selected : WorldState × FrameEffectJournal Nat (List Nat))
    (data : Bytes) : Option Nat :=
  if observedValue_variant? selected.1 == some revertedValue &&
      selected.2.rollback == 20 && selected.2.trace == [2, 3] &&
      data == revertedBytes then
    some 22
  else
    some 92

def testFrameResolutionResultContinuation : IO Unit := do
  let returned : FrameResolutionResult Nat (List Nat) Reason :=
    .returned returnedState returnedEffects returnedBytes
  assertTrue
    (returned.continue? onReturned onReverted == some 11)
    "return continuation must receive exact state, effects, and bytes"

  let reverted : FrameResolutionResult Nat (List Nat) Reason :=
    .reverted revertedState revertedEffects revertedBytes
  assertTrue
    (reverted.continue? onReturned onReverted == some 22)
    "revert continuation must receive exact state, effects, and bytes"

  let trapped : FrameResolutionResult Nat (List Nat) Reason := .trapped .marker
  assertTrue
    ((trapped.continue? onReturned onReverted).isNone)
    "trap continuation must select neither non-trapping callback"

end Tests
end

section
-- leanmerge: from Solcore.Test.FrameResolutionResultContinueTrapReasonMap
/-! Compile-only regressions for result-continuation reason-map invariance. -/

set_option autoImplicit false

namespace Tests

open Solcore.ContractRuntime

universe u v w x y z

private example
    {RollbackState : Type u} {TraceState : Type v}
    {TrapReason : Type w} {MappedTrapReason : Type x}
    {Next : Type y}
    (mapReason : TrapReason → MappedTrapReason)
    (result : FrameResolutionResult RollbackState TraceState TrapReason)
    (onReturned onReverted :
      (WorldState × FrameEffectJournal RollbackState TraceState) →
        Bytes → Option Next) :
    (result.mapTrapReason mapReason).continue?
        onReturned onReverted =
      result.continue? onReturned onReverted := by
  simp

private example
    {RollbackState : Type u} {TraceState : Type v}
    {TrapReason : Type w} {IntermediateTrapReason : Type x}
    {MappedTrapReason : Type y} {Next : Type z}
    (first : TrapReason → IntermediateTrapReason)
    (second : IntermediateTrapReason → MappedTrapReason)
    (result : FrameResolutionResult RollbackState TraceState TrapReason)
    (onReturned onReverted :
      (WorldState × FrameEffectJournal RollbackState TraceState) →
        Bytes → Option Next) :
    ((result.mapTrapReason first).mapTrapReason second).continue?
        onReturned onReverted =
      result.continue? onReturned onReverted := by
  simp

end Tests
end

section
-- leanmerge: from Solcore.Test.FrameResolutionResultTrapReasonMap
/-! Definition-only tests for total-resolution trap-reason mapping. -/

set_option autoImplicit false

namespace Tests

open Solcore
open Solcore.ContractRuntime

private def returnStateValue : Core.Word := ⟨0xaa, by decide⟩
private def revertStateValue : Core.Word := ⟨0xbb, by decide⟩

private def returnEffects : FrameEffectJournal Nat Nat := ⟨10, 100⟩
private def revertEffects : FrameEffectJournal Nat Nat := ⟨20, 200⟩

private def matchesReturned_variant2 :
    FrameResolutionResult Nat Nat MappedTrapReason → Bool
  | .returned state effects data =>
      observedValue? state == some returnStateValue &&
        effects.rollback == 10 && effects.trace == 100 && data == returnBytes
  | _ => false

private def matchesReverted_variant2 :
    FrameResolutionResult Nat Nat MappedTrapReason → Bool
  | .reverted state effects data =>
      observedValue? state == some revertStateValue &&
        effects.rollback == 20 && effects.trace == 200 && data == revertBytes
  | _ => false

private def matchesMappedTrap_variant2 :
    FrameResolutionResult Nat Nat MappedTrapReason → Bool
  | .trapped .mapped => true
  | _ => false

def testFrameResolutionResultTrapReasonMap : IO Unit := do
  assertTrue
    (matchesReturned_variant2
      (FrameResolutionResult.mapTrapReason mapReason
        (FrameResolutionResult.returned
          (TrapReason := LocalTrapReason)
          (stateWith_variant returnStateValue) returnEffects returnBytes)))
    "return mapping must preserve exact state, effects, and bytes"

  assertTrue
    (matchesReverted_variant2
      (FrameResolutionResult.mapTrapReason mapReason
        (FrameResolutionResult.reverted
          (TrapReason := LocalTrapReason)
          (stateWith_variant revertStateValue) revertEffects revertBytes)))
    "revert mapping must preserve distinct state, effects, and bytes"

  assertTrue
    (matchesMappedTrap_variant2
      (FrameResolutionResult.mapTrapReason mapReason
        (FrameResolutionResult.trapped
          (RollbackState := Nat) (TraceState := Nat) LocalTrapReason.marker)))
    "trap mapping must produce the exact target reason"

end Tests
end

section
-- leanmerge: from Solcore.Test.FrameRunContinuation
/-! Executable tests for caller-owned frame continuation. -/

set_option autoImplicit false

namespace Tests

open Solcore
open Solcore.ContractRuntime

private inductive ContinuationReason where
  | marker

private def isMarker_variant? : FrameOutcome ContinuationReason → Bool
  | .trapped .marker => true
  | _ => false

def testFrameRunContinuation : IO Unit := do
  let returned : FrameRunResult ContinuationReason :=
    ⟨workingWorld, .returned [0x12].toByteArray⟩
  let returnedObserved := returned.continueWithResolvedStateAndEffects?
    stateCheckpoint effectCheckpoint effectWorking observeSelected
  assertTrue
    (returnedObserved == some (some workingValue_variant, 20, 200))
    "return must continue with working state, rollback, and trace"

  let reverted : FrameRunResult ContinuationReason :=
    ⟨workingWorld, .reverted [].toByteArray⟩
  let revertedObserved := reverted.continueWithResolvedStateAndEffects?
    stateCheckpoint effectCheckpoint effectWorking observeSelected
  assertTrue
    (revertedObserved == some (some checkpointValue_variant3, 10, 200))
    "revert must continue with checkpoint state and rollback plus working trace"

  let trapped : FrameRunResult ContinuationReason :=
    ⟨workingWorld, .trapped .marker⟩
  let trappedObserved := trapped.continueWithResolvedStateAndEffects?
    stateCheckpoint effectCheckpoint effectWorking observeSelected
  assertTrue
    (isMarker_variant? trapped.outcome && trappedObserved.isNone)
    "trap must preserve its concrete input and skip the sentinel continuation"

end Tests
end

section
-- leanmerge: from Solcore.Test.FrameRunEffectComposition
/-! Executable tests for synchronized child-frame composition. -/

set_option autoImplicit false

namespace Tests

open Solcore
open Solcore.ContractRuntime

private inductive CompositionTrapReason where
  | marker

private def parentStateCheckpoint : WorldState := stateWith_variant ⟨0xaa, by decide⟩
private def childStateCheckpoint : WorldState := stateWith_variant ⟨0xbb, by decide⟩
private def childStateWorking : WorldState := stateWith_variant ⟨0xcc, by decide⟩

private def parentEffectCheckpoint : FrameEffectJournal Nat Nat := ⟨10, 100⟩
private def childEffectCheckpoint : FrameEffectJournal Nat Nat := ⟨20, 200⟩
private def childEffectWorking : FrameEffectJournal Nat Nat := ⟨30, 300⟩

private def matches_variant?
    (resolved? : Option (WorldState × FrameEffectJournal Nat Nat))
    (value : Core.Word) (rollback trace : Nat) : Bool :=
  match resolved? with
  | some resolved =>
      observedValue? resolved.1 == some value &&
        resolved.2.rollback == rollback && resolved.2.trace == trace
  | none => false

private def parentRevertAfter?
    (childResolved? : Option (WorldState × FrameEffectJournal Nat Nat)) :
    Option (WorldState × FrameEffectJournal Nat Nat) :=
  childResolved?.bind fun childResolved =>
    let parentResult : FrameRunResult CompositionTrapReason :=
      ⟨childResolved.1, .reverted [].toByteArray⟩
    parentResult.resolvedWorldStateAndEffects?
      parentStateCheckpoint parentEffectCheckpoint childResolved.2

def testFrameRunEffectComposition : IO Unit := do
  let childReturned : FrameRunResult CompositionTrapReason :=
    ⟨childStateWorking, .returned [0x12].toByteArray⟩
  let returnedIntermediate := childReturned.resolvedWorldStateAndEffects?
    childStateCheckpoint childEffectCheckpoint childEffectWorking
  assertTrue
    (matches_variant? returnedIntermediate ⟨0xcc, by decide⟩ 30 300 &&
      matches_variant? (parentRevertAfter? returnedIntermediate) ⟨0xaa, by decide⟩ 10 300)
    "returned child must be adopted before parent revert restores parent rollback and preserves child trace"

  let childReverted : FrameRunResult CompositionTrapReason :=
    ⟨childStateWorking, .reverted [].toByteArray⟩
  let revertedIntermediate := childReverted.resolvedWorldStateAndEffects?
    childStateCheckpoint childEffectCheckpoint childEffectWorking
  assertTrue
    (matches_variant? revertedIntermediate ⟨0xbb, by decide⟩ 20 300 &&
      matches_variant? (parentRevertAfter? revertedIntermediate) ⟨0xaa, by decide⟩ 10 300)
    "reverted child must restore its checkpoint before parent revert restores the parent checkpoint and preserves child trace"

end Tests
end

section
-- leanmerge: from Solcore.Test.FrameRunEffectContinuation
/-! Executable tests for resolved synchronized frame continuations. -/

set_option autoImplicit false

namespace Tests

open Solcore
open Solcore.ContractRuntime

private inductive ContinuationTrapReason where
  | marker

def testFrameRunEffectContinuation : IO Unit := do
  let returned : FrameRunResult ContinuationTrapReason :=
    ⟨workingWorld, .returned [0x12].toByteArray⟩
  let returnedObserved :=
    (returned.resolvedWorldStateAndEffects?
      stateCheckpoint effectCheckpoint effectWorking).bind observeSelected
  assertTrue
    (returnedObserved == some (some workingValue_variant, 20, 200))
    "return continuation must receive working state, rollback, and trace"

  let reverted : FrameRunResult ContinuationTrapReason :=
    ⟨workingWorld, .reverted [].toByteArray⟩
  let revertedObserved :=
    (reverted.resolvedWorldStateAndEffects?
      stateCheckpoint effectCheckpoint effectWorking).bind observeSelected
  assertTrue
    (revertedObserved == some (some checkpointValue_variant3, 10, 200))
    "revert continuation must receive checkpoint state and rollback with working trace"

end Tests
end

section
-- leanmerge: from Solcore.Test.FrameRunEffectResolution
/-! Executable tests for synchronized frame state and effect resolution. -/

set_option autoImplicit false

namespace Tests

open Solcore
open Solcore.ContractRuntime

private inductive RunEffectTrapReason where
  | invalidOperation

def testFrameRunEffectResolution : IO Unit := do
  let returned : FrameRunResult RunEffectTrapReason :=
    ⟨workingWorld, .returned [0x12, 0].toByteArray⟩
  let reverted : FrameRunResult RunEffectTrapReason :=
    ⟨workingWorld, .reverted [].toByteArray⟩
  let trapped : FrameRunResult RunEffectTrapReason :=
    ⟨workingWorld, .trapped .invalidOperation⟩
  assertTrue
    (matches_variant? (returned.resolvedWorldStateAndEffects?
      stateCheckpoint effectCheckpoint effectWorking) workingValue_variant 20 200)
    "return must keep both working state and working effect snapshots"
  assertTrue
    (matches_variant? (reverted.resolvedWorldStateAndEffects?
      stateCheckpoint effectCheckpoint effectWorking) checkpointValue_variant3 10 200)
    "revert must restore checkpoint state and rollback while preserving trace"
  assertTrue
    ((trapped.resolvedWorldStateAndEffects?
      stateCheckpoint effectCheckpoint effectWorking).isNone)
    "trap must leave synchronized state and effect resolution open"

end Tests
end

section
-- leanmerge: from Solcore.Test.FrameRunEffectTrapPropagation
/-! Executable test for unresolved trap propagation through Option bind. -/

set_option autoImplicit false

namespace Tests

open Solcore.ContractRuntime

private inductive TrapPropagationReason where
  | fault

private def isFault? : FrameOutcome TrapPropagationReason → Bool
  | .trapped .fault => true
  | _ => false

def testFrameRunEffectTrapPropagation : IO Unit := do
  let trapped : FrameRunResult TrapPropagationReason :=
    ⟨WorldState.empty, .trapped .fault⟩
  let checkpoint : FrameEffectJournal Nat Nat := ⟨10, 100⟩
  let working : FrameEffectJournal Nat Nat := ⟨20, 200⟩
  let unresolved := trapped.resolvedWorldStateAndEffects?
    WorldState.empty checkpoint working
  let continued : Option Nat := unresolved.bind fun _ => some 7
  assertTrue
    (isFault? trapped.outcome && unresolved.isNone && continued.isNone)
    "concrete trap input must resolve to none and skip the sentinel continuation"

end Tests
end

section
-- leanmerge: from Solcore.Test.FrameRunResult
/-! Executable boundary tests for state-and-outcome frame results. -/

set_option autoImplicit false

namespace Tests

open Solcore
open Solcore.ContractRuntime

private inductive RunTrapReason where
  | invalidOperation
  deriving BEq, DecidableEq

private def checkpoint_variant6 : WorldState := stateWith_variant checkpointValue_variant3
private def working_variant : WorldState := stateWith_variant workingValue_variant

private def observedValue_variant2? (state? : Option WorldState) : Option Core.Word := do
  let state ← state?
  let account ← state.account? address_variant
  account.storageValue? slot_variant2

def testFrameRunResult : IO Unit := do
  let returnData := [0x12, 0].toByteArray
  let revertData := [].toByteArray
  let returned : FrameRunResult RunTrapReason := {
    working := working_variant
    outcome := .returned returnData
  }
  let reverted : FrameRunResult RunTrapReason := {
    working := working_variant
    outcome := .reverted revertData
  }
  let trapped : FrameRunResult RunTrapReason := {
    working := working_variant
    outcome := .trapped .invalidOperation
  }
  assertTrue
    (observedValue_variant2? (returned.resolvedWorldState? checkpoint_variant6) == some workingValue_variant &&
      observedValue_variant2? (some returned.working) == some workingValue_variant &&
      returned.outcome.returndata? == some returnData)
    "a returned result must expose its nonempty data and select its working state"
  assertTrue
    (observedValue_variant2? (reverted.resolvedWorldState? checkpoint_variant6) == some checkpointValue_variant3 &&
      observedValue_variant2? (some reverted.working) == some workingValue_variant &&
      reverted.outcome.revertdata? == some revertData &&
      reverted.outcome.revertdata? != none)
    "a reverted result must retain working state and empty data but resolve to checkpoint"
  assertTrue
    ((trapped.resolvedWorldState? checkpoint_variant6).isNone &&
      observedValue_variant2? (some trapped.working) == some workingValue_variant &&
      trapped.outcome.trapReason? == some .invalidOperation)
    "a trapped result must retain working state and its reason while resolution stays open"

end Tests
end

section
-- leanmerge: from Solcore.Test.FrameRunResultTrapReasonMap
/-! Definition-only tests for frame-run trap-reason mapping. -/

set_option autoImplicit false

namespace Tests

open Solcore
open Solcore.ContractRuntime

private def returnWorkingValue_variant : Core.Word := ⟨0xaa, by decide⟩
private def revertWorkingValue_variant : Core.Word := ⟨0xbb, by decide⟩
private def trapWorkingValue_variant : Core.Word := ⟨0xcc, by decide⟩

private def matchesReturned_variant3 : FrameRunResult MappedTrapReason → Bool
  | ⟨state, .returned data⟩ =>
      observedValue? state == some returnWorkingValue_variant && data == returnBytes
  | _ => false

private def matchesReverted_variant3 : FrameRunResult MappedTrapReason → Bool
  | ⟨state, .reverted data⟩ =>
      observedValue? state == some revertWorkingValue_variant && data == revertBytes
  | _ => false

private def matchesMappedTrap_variant3 : FrameRunResult MappedTrapReason → Bool
  | ⟨state, .trapped .mapped⟩ =>
      observedValue? state == some trapWorkingValue_variant
  | _ => false

def testFrameRunResultTrapReasonMap : IO Unit := do
  assertTrue
    (matchesReturned_variant3
      (FrameRunResult.mapTrapReason mapReason
        (⟨stateWith_variant returnWorkingValue_variant, .returned returnBytes⟩ :
          FrameRunResult LocalTrapReason)))
    "return mapping must preserve its working state and exact bytes"

  assertTrue
    (matchesReverted_variant3
      (FrameRunResult.mapTrapReason mapReason
        (⟨stateWith_variant revertWorkingValue_variant, .reverted revertBytes⟩ :
          FrameRunResult LocalTrapReason)))
    "revert mapping must preserve its distinct working state and exact bytes"

  assertTrue
    (matchesMappedTrap_variant3
      (FrameRunResult.mapTrapReason mapReason
        ⟨stateWith_variant trapWorkingValue_variant, .trapped LocalTrapReason.marker⟩))
    "trap mapping must preserve its working state and map the exact reason"

end Tests
end

section
-- leanmerge: from Solcore.Test.FrameStateResolution
/-! Executable tests for resolving frame outcomes against state snapshots. -/

set_option autoImplicit false

namespace Tests

open Solcore
open Solcore.ContractRuntime

private inductive TestTrapReason_variant where
  | invalidOperation

def testFrameStateResolution : IO Unit := do
  let returned : FrameOutcome TestTrapReason_variant :=
    .returned [0x12, 0].toByteArray
  let reverted : FrameOutcome TestTrapReason_variant :=
    .reverted [].toByteArray
  let trapped : FrameOutcome TestTrapReason_variant :=
    .trapped .invalidOperation
  assertTrue
    (observedValue_variant2? (returned.resolvedWorldState? checkpoint_variant6 working_variant) ==
      some workingValue_variant)
    "a returned frame with nonempty data must select the working state"
  assertTrue
    (observedValue_variant2? (reverted.resolvedWorldState? checkpoint_variant6 working_variant) ==
      some checkpointValue_variant3)
    "a reverted frame with empty data must select the checkpoint state"
  assertTrue (trapped.resolvedWorldState? checkpoint_variant6 working_variant).isNone
    "a trapped frame with a concrete reason must leave state resolution open"

end Tests
end

section
-- leanmerge: from Solcore.Test.FrameTrace
/-! Executable tests for finite chronological frame traces. -/

set_option autoImplicit false

namespace Tests

open Solcore.ContractRuntime

private inductive TraceEvent where
  | entered
  | child
  | finished

private def matchesEmpty : List TraceEvent → Bool
  | [] => true
  | _ => false

private def matchesEntered : List TraceEvent → Bool
  | [.entered] => true
  | _ => false

private def matchesRepeated : List TraceEvent → Bool
  | [.entered, .child, .child] => true
  | _ => false

private def matchesAppended : List TraceEvent → Bool
  | [.entered, .child, .finished] => true
  | _ => false

private def matchesCombined : List TraceEvent → Bool
  | [.entered, .child, .child, .finished] => true
  | _ => false

private def empty : FrameTrace TraceEvent :=
  FrameTrace.empty

private def entered : FrameTrace TraceEvent :=
  empty.record .entered

private def repeated : FrameTrace TraceEvent :=
  (entered.record .child).record .child

private def later : FrameTrace TraceEvent :=
  (FrameTrace.empty.record .child).record .finished

def testFrameTrace : IO Unit := do
  assertTrue
    (matchesEmpty empty.toList)
    "an empty frame trace must expose no events"

  assertTrue
    (matchesEntered entered.toList)
    "record must place one event at the chronological tail"

  assertTrue
    (matchesRepeated repeated.toList)
    "record must preserve order and duplicate events"

  let journal : FrameEffectJournal Nat (FrameTrace TraceEvent) :=
    ⟨7, entered.append later⟩
  assertTrue
    (journal.rollback == 7 && matchesAppended journal.trace.toList)
    "append must place the earlier journal trace before the later fragment"

  let emptyLeft := FrameTrace.append FrameTrace.empty repeated
  let emptyRight := FrameTrace.append repeated FrameTrace.empty
  assertTrue
    (matchesRepeated emptyLeft.toList && matchesRepeated emptyRight.toList)
    "empty must be a left and right append identity"

  let first := empty.record .entered
  let second := (FrameTrace.empty.record .child).record .child
  let third := FrameTrace.empty.record .finished
  let leftAssociated := (first.append second).append third
  let rightAssociated := first.append (second.append third)
  assertTrue
    (matchesCombined leftAssociated.toList &&
      matchesCombined rightAssociated.toList)
    "three trace fragments must preserve order under either association"

end Tests
end

section
-- leanmerge: from Solcore.Test.FrameTraceExtension
/-! Definition-only tests for indexed incremental frame-trace extension. -/

set_option autoImplicit false

namespace Tests

open Solcore.ContractRuntime

private inductive ExtensionEvent where
  | entered
  | child

private inductive ExtensionReason where
  | marker

private def matchesEntered_variant : List ExtensionEvent → Bool
  | [.entered] => true
  | _ => false

private def matchesChild : List ExtensionEvent → Bool
  | [.entered, .child] => true
  | _ => false

private def matchesRepeated_variant : List ExtensionEvent → Bool
  | [.entered, .child, .child] => true
  | _ => false

private def earlierTrace : FrameTrace ExtensionEvent :=
  FrameTrace.record FrameTrace.empty .entered

private def extension : FrameTrace.ExtensionFrom earlierTrace :=
  FrameTrace.ExtensionFrom.start earlierTrace

private def recorded : FrameTrace.ExtensionFrom earlierTrace :=
  extension.record .child

private def repeated_variant : FrameTrace.ExtensionFrom earlierTrace :=
  recorded.record .child

private def baseContext_variant :
    FrameContinuationContext Nat (FrameTrace ExtensionEvent)
      ExtensionReason :=
  ⟨WorldState.empty, ⟨10, earlierTrace⟩, ⟨20, recorded.toTrace⟩,
    ⟨WorldState.empty, .trapped .marker⟩⟩

private example :
    FrameContinuationContextWithTracePrefix Nat ExtensionEvent
      ExtensionReason :=
  ⟨baseContext_variant, recorded.earlier_isPrefixOf_toTrace⟩

def testFrameTraceExtension : IO Unit := do
  assertTrue
    (matchesEntered_variant extension.toTrace.toList)
    "start must retain a nonempty earlier trace exactly once"

  assertTrue
    (matchesChild recorded.toTrace.toList)
    "record must place one event after the fixed earlier trace"

  assertTrue
    (matchesRepeated_variant repeated_variant.toTrace.toList)
    "record must preserve chronological duplicates"

end Tests
end

section
-- leanmerge: from Solcore.Test.FrameTracePrefix
/-! Definition-only compile regressions for concrete frame-trace prefixes. -/

set_option autoImplicit false

namespace Tests

open Solcore.ContractRuntime

private inductive PrefixEvent where
  | entered
  | completed

private def enteredTrace : FrameTrace PrefixEvent :=
  FrameTrace.record FrameTrace.empty .entered

private def completedTrace : FrameTrace PrefixEvent :=
  FrameTrace.record FrameTrace.empty .completed

private example :
    FrameTrace.IsPrefixOf FrameTrace.empty enteredTrace :=
  ⟨enteredTrace, rfl⟩

private example :
    FrameTrace.IsPrefixOf enteredTrace enteredTrace :=
  ⟨FrameTrace.empty, rfl⟩

private example :
    FrameTrace.IsPrefixOf enteredTrace
      (FrameTrace.append enteredTrace completedTrace) :=
  ⟨completedTrace, rfl⟩

private example :
    FrameTrace.IsPrefixOf enteredTrace
      (FrameTrace.append
        (FrameTrace.append enteredTrace completedTrace)
        enteredTrace) :=
  ⟨FrameTrace.append completedTrace enteredTrace, rfl⟩

end Tests
end
