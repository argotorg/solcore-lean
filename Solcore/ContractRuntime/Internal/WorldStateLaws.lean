import Solcore.ContractRuntime.WorldState
import Solcore.Core.Host
import Solcore.Core.HostRunner

/-!
# Laws of accounts and world state

Account fields under each update, conditional storage reads, and code lookup. The laws that unfold
private fields are in `WorldState` itself.
-/

section
-- leanmerge: from Solcore.ContractRuntime.CheckedHostCoreProgram
/-! Checker-accepted Core programs under the fixed host capability context. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime

namespace CheckedHostCoreProgram

@[simp] theorem ofProgram?_of_checked
    (program : Core.Program)
    (checked : program.checkHost = true) :
    ofProgram? program = some ⟨program, checked⟩ := by
  simp [ofProgram?, checked]

@[simp] theorem ofProgram?_of_rejected
    (program : Core.Program)
    (rejected : program.checkHost = false) :
    ofProgram? program = none := by
  simp [ofProgram?, rejected]

end CheckedHostCoreProgram

end Solcore.ContractRuntime

/-!
## Consolidated module: `Solcore.ContractRuntime.CheckedHostCoreProgramExecution`
-/

/-! Interactive execution for programs checked in the fixed host context. -/

set_option autoImplicit false

/-!
## Consolidated module: `Solcore.ContractRuntime.CheckedHostCoreProgramProperties`
-/

/-! Admission and initial-state typing for checker-accepted host-aware Core code. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.CheckedHostCoreProgram

/-- The fixed runtime capability environment realizes the context used by the
host checker. -/
theorem initialState_hasType
    (code : CheckedHostCoreProgram) :
    Core.HostStateHasType
      (Core.State.initial code.program.body Core.hostEnvironment)
      code.program.resultType code.program.dataDefinitions :=
  .eval .nil
    (Core.hostEnvironment_hasTypes [] code.program.dataDefinitions)
    (Core.Program.checkHost_sound code.checked) .nil

/-- Every finite host-aware run has a typed non-fault result. -/
theorem runStateful_hasType
    (code : CheckedHostCoreProgram)
    (fuel : Nat) :
    Core.HostRunResult.HasType (code.runStateful fuel)
      code.program.resultType code.program.dataDefinitions := by
  simpa [runStateful, Core.Program.runHostStateful] using
    Core.hostRun_hasType fuel code.initialState_hasType

theorem runStateful_ne_fault
    (code : CheckedHostCoreProgram)
    (fuel : Nat)
    (error : Core.MachineFault)
    (faultState : Core.State) :
    code.runStateful fuel ≠ .fault error faultState := by
  simpa [runStateful, Core.Program.runHostStateful] using
    Core.hostRun_never_faults
      (fuel := fuel) (faultState := faultState) (error := error)
      code.initialState_hasType

theorem runStateful_done_hasType
    (code : CheckedHostCoreProgram)
    {fuel : Nat} {value : Core.Value} {store : Core.Store}
    (result : code.runStateful fuel = .done value store) :
    ∃ world,
      Core.HostStoreHasTypes world store code.program.dataDefinitions ∧
        Core.HostRuntimeValueHasType world value code.program.resultType
          code.program.dataDefinitions := by
  apply Core.hostRun_done_hasType code.initialState_hasType
  simpa [runStateful, Core.Program.runHostStateful] using result

theorem runStateful_outOfFuel_hasType
    (code : CheckedHostCoreProgram)
    {fuel : Nat} {state : Core.State}
    (result : code.runStateful fuel = .outOfFuel state) :
    Core.HostStateHasType state code.program.resultType
      code.program.dataDefinitions := by
  apply Core.hostRun_outOfFuel_hasType code.initialState_hasType
  simpa [runStateful, Core.Program.runHostStateful] using result

theorem runStateful_suspended_hasType
    (code : CheckedHostCoreProgram)
    {fuel remainingFuel : Nat} {suspension : Core.HostSuspension}
    (result : code.runStateful fuel = .suspended suspension remainingFuel) :
    Core.HostSuspensionHasType suspension code.program.resultType
      code.program.dataDefinitions := by
  apply Core.hostRun_suspended_hasType code.initialState_hasType
  simpa [runStateful, Core.Program.runHostStateful] using result

end Solcore.ContractRuntime.CheckedHostCoreProgram
end

section
-- leanmerge: from Solcore.ContractRuntime.Account
/-! Account code, balance, nonce, and sparse-storage laws. -/

/-!
## Consolidated module: `Solcore.ContractRuntime.AccountCodeProperties`
-/

/-! Checked-code observations and storage preservation for Account. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.Account

@[simp] theorem code?_empty : Account.empty.code? = none := by
  rfl

@[simp] theorem code?_withCode
    (account : Account)
    (code : CheckedHostCoreProgram) :
    (account.withCode code).code? = some code := by
  rfl

@[simp] theorem storageValue?_withCode
    (account : Account)
    (code : CheckedHostCoreProgram)
    (slot : Core.Word) :
    (account.withCode code).storageValue? slot = account.storageValue? slot := by
  rfl

@[simp] theorem code?_storageWrite
    (account : Account)
    (slot value : Core.Word) :
    (account.storageWrite slot value).code? = account.code? := by
  by_cases zero : value = Core.Word.zero
  · simp [storageWrite, code?, zero]
  · simp [storageWrite, code?, zero]

end Solcore.ContractRuntime.Account

/-!
## Consolidated module: `Solcore.ContractRuntime.AccountBalanceProperties`
-/

/-! Balance observations and preservation laws for Account updates. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.Account

@[simp] theorem balance_empty : Account.empty.balance = Core.Word.zero := by
  rfl

@[simp] theorem balance_withBalance
    (account : Account)
    (balance : Core.Word) :
    (account.withBalance balance).balance = balance := by
  rfl

@[simp] theorem storageValue?_withBalance
    (account : Account)
    (balance : Core.Word)
    (slot : Core.Word) :
    (account.withBalance balance).storageValue? slot =
      account.storageValue? slot := by
  rfl

@[simp] theorem code?_withBalance
    (account : Account)
    (balance : Core.Word) :
    (account.withBalance balance).code? = account.code? := by
  rfl

@[simp] theorem balance_withCode
    (account : Account)
    (code : CheckedHostCoreProgram) :
    (account.withCode code).balance = account.balance := by
  rfl

@[simp] theorem balance_storageWrite
    (account : Account)
    (slot value : Core.Word) :
    (account.storageWrite slot value).balance = account.balance := by
  by_cases zero : value = Core.Word.zero
  · simp [storageWrite, balance, zero]
  · simp [storageWrite, balance, zero]

end Solcore.ContractRuntime.Account

/-!
## Consolidated module: `Solcore.ContractRuntime.AccountNonceProperties`
-/

/-! Nonce observations and preservation laws for Account updates. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.Account

@[simp] theorem nonce_empty : Account.empty.nonce = Core.Word.zero := by
  rfl

@[simp] theorem nonce_withNonce
    (account : Account)
    (nonce : Core.Word) :
    (account.withNonce nonce).nonce = nonce := by
  rfl

@[simp] theorem storageValue?_withNonce
    (account : Account)
    (nonce slot : Core.Word) :
    (account.withNonce nonce).storageValue? slot =
      account.storageValue? slot := by
  rfl

@[simp] theorem code?_withNonce
    (account : Account)
    (nonce : Core.Word) :
    (account.withNonce nonce).code? = account.code? := by
  rfl

@[simp] theorem balance_withNonce
    (account : Account)
    (nonce : Core.Word) :
    (account.withNonce nonce).balance = account.balance := by
  rfl

@[simp] theorem nonce_withBalance
    (account : Account)
    (balance : Core.Word) :
    (account.withBalance balance).nonce = account.nonce := by
  rfl

@[simp] theorem nonce_withCode
    (account : Account)
    (code : CheckedHostCoreProgram) :
    (account.withCode code).nonce = account.nonce := by
  rfl

@[simp] theorem nonce_storageWrite
    (account : Account)
    (slot value : Core.Word) :
    (account.storageWrite slot value).nonce = account.nonce := by
  by_cases zero : value = Core.Word.zero
  · simp [storageWrite, nonce, zero]
  · simp [storageWrite, nonce, zero]

end Solcore.ContractRuntime.Account

/-!
## Consolidated module: `Solcore.ContractRuntime.AccountNonceIncrement`
-/

/-! Checked, non-wrapping account nonce increment. -/

set_option autoImplicit false

/-!
## Consolidated module: `Solcore.ContractRuntime.AccountNonceIncrementProperties`
-/

/-! Exact arithmetic and payload laws for checked nonce increment. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.Account

theorem incrementNonce?_isSome_iff (account : Account) :
    account.incrementNonce?.isSome ↔
      account.nonce.val + 1 < Core.wordModulus := by
  unfold incrementNonce? Core.Word.ofNat?
  split <;> simp_all

theorem incrementNonce?_eq_none_iff (account : Account) :
    account.incrementNonce? = none ↔
      Core.wordModulus ≤ account.nonce.val + 1 := by
  simp [incrementNonce?, Core.Word.ofNat?, Nat.not_lt]

theorem incrementNonce?_success_exact
    (account next : Account)
    (success : account.incrementNonce? = some next) :
    next.nonce.val = account.nonce.val + 1 := by
  unfold incrementNonce? Core.Word.ofNat? at success
  split at success
  · injection success with equal
    subst next
    simp
  · contradiction

@[simp] theorem incrementNonce?_maximum (account : Account) :
    (account.withNonce Core.Word.maximum).incrementNonce? = none := by
  apply (incrementNonce?_eq_none_iff _).2
  change Core.wordModulus ≤ (Core.wordModulus - 1) + 1
  omega

theorem incrementNonce?_preserves_payload
    (account next : Account)
    (success : account.incrementNonce? = some next) :
    next.balance = account.balance ∧
      next.code? = account.code? ∧
      ∀ slot, next.storageValue? slot = account.storageValue? slot := by
  unfold incrementNonce? Core.Word.ofNat? at success
  split at success
  · injection success with equal
    subst next
    simp
  · contradiction

theorem incrementNonce?_success_iff (account : Account) :
    (∃ next, account.incrementNonce? = some next ∧
      next.nonce.val = account.nonce.val + 1) ↔
      account.nonce.val + 1 < Core.wordModulus := by
  constructor
  · rintro ⟨next, success, _⟩
    exact (incrementNonce?_isSome_iff account).1 (by simp [success])
  · intro inBounds
    let nextNonce : Core.Word := ⟨account.nonce.val + 1, inBounds⟩
    refine ⟨account.withNonce nextNonce, ?_, ?_⟩
    · simp [incrementNonce?, Core.Word.ofNat?, inBounds, nextNonce]
    · simp [nextNonce]

end Solcore.ContractRuntime.Account

/-!
## Consolidated module: `Solcore.ContractRuntime.AccountStorageWriteSparsePreservationProperties`
-/

/-! Distinct-slot sparse-storage preservation for Account writes. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime

/-- A storage write preserves the optional sparse entry at every other slot. -/
theorem Account.storageValue?_storageWrite_other
    (account : Account)
    (writtenSlot value otherSlot : Core.Word)
    (different : otherSlot ≠ writtenSlot) :
    (account.storageWrite writtenSlot value).storageValue? otherSlot =
      account.storageValue? otherSlot := by
  by_cases zero : value = Core.Word.zero
  · simp [Account.storageWrite, Account.storageValue?, zero, different]
  · simp [Account.storageWrite, Account.storageValue?, zero, different]

end Solcore.ContractRuntime
end

section
-- leanmerge: from Solcore.ContractRuntime.WorldStateStorageRead
/-! Conditional storage reads over explicit WorldState account presence. -/

set_option autoImplicit false

/-!
## Consolidated module: `Solcore.ContractRuntime.WorldStateStorageReadProperties`
-/

/-! Branch laws for conditional WorldState storage reads. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime

/-- Reading storage from an absent Account remains unavailable. -/
@[simp] theorem WorldState.readStorage?_of_absent
    (state : WorldState)
    (address : Address)
    (slot : Core.Word)
    (absent : state.account? address = none) :
    state.readStorage? address slot = none := by
  simp [WorldState.readStorage?, absent]

/-- Reading from a present Account delegates to its zero-default slot read. -/
@[simp] theorem WorldState.readStorage?_of_present
    (state : WorldState)
    (address : Address)
    (account : Account)
    (slot : Core.Word)
    (present : state.account? address = some account) :
    state.readStorage? address slot = some (account.storageRead slot) := by
  simp [WorldState.readStorage?, present]

end Solcore.ContractRuntime

/-!
## Consolidated module: `Solcore.ContractRuntime.WorldStateStorageReadWriteProperties`
-/

/-! Stage-preserving observations of conditional WorldState storage writes. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime

/-- Reading the written slot observes the new value after a successful write. -/
@[simp] theorem WorldState.readStorage?_writeStorage?_same
    (state : WorldState) (address : Address)
    (slot value : Core.Word) :
    (state.writeStorage? address slot value).map
        (fun next => next.readStorage? address slot) =
      (state.account? address).map (fun _ => some value) := by
  cases present : state.account? address with
  | none =>
      rw [WorldState.writeStorage?_of_absent state address slot value present]
      simp
  | some account =>
      have written :
          state.writeStorage? address slot value =
            some (state.putAccount address
              (account.storageWrite slot value)) := by
        simp [WorldState.writeStorage?, present]
      rw [written]
      simp only [Option.map_some]
      rw [WorldState.readStorage?_of_present
        (state.putAccount address (account.storageWrite slot value))
        address (account.storageWrite slot value) slot
        (WorldState.account?_putAccount_same state address
          (account.storageWrite slot value))]
      rw [Account.storageRead_storageWrite_same]

/-- Writing another slot preserves the selected slot read. -/
@[simp] theorem WorldState.readStorage?_writeStorage?_other_slot
    (state : WorldState) (address : Address)
    (writtenSlot value readSlot : Core.Word)
    (different : readSlot ≠ writtenSlot) :
    (state.writeStorage? address writtenSlot value).map
        (fun next => next.readStorage? address readSlot) =
      (state.account? address).map
        (fun _ => state.readStorage? address readSlot) := by
  cases present : state.account? address with
  | none =>
      rw [WorldState.writeStorage?_of_absent state address writtenSlot value
        present]
      simp
  | some account =>
      have written :
          state.writeStorage? address writtenSlot value =
            some (state.putAccount address
              (account.storageWrite writtenSlot value)) := by
        simp [WorldState.writeStorage?, present]
      rw [written]
      simp only [Option.map_some]
      rw [WorldState.readStorage?_of_present
        (state.putAccount address (account.storageWrite writtenSlot value))
        address (account.storageWrite writtenSlot value) readSlot
        (WorldState.account?_putAccount_same state address
          (account.storageWrite writtenSlot value))]
      rw [Account.storageRead_storageWrite_other account writtenSlot value
        readSlot different]
      simp [present]

/-- Writing another address preserves the selected address read. -/
@[simp] theorem WorldState.readStorage?_writeStorage?_other_address
    (state : WorldState) (writtenAddress readAddress : Address)
    (writtenSlot value readSlot : Core.Word)
    (different : readAddress ≠ writtenAddress) :
    (state.writeStorage? writtenAddress writtenSlot value).map
        (fun next => next.readStorage? readAddress readSlot) =
      (state.account? writtenAddress).map
        (fun _ => state.readStorage? readAddress readSlot) := by
  cases present : state.account? writtenAddress with
  | none =>
      rw [WorldState.writeStorage?_of_absent state writtenAddress writtenSlot
        value present]
      simp
  | some account =>
      have written :
          state.writeStorage? writtenAddress writtenSlot value =
            some (state.putAccount writtenAddress
              (account.storageWrite writtenSlot value)) := by
        simp [WorldState.writeStorage?, present]
      have readPreserved :
          (state.putAccount writtenAddress
            (account.storageWrite writtenSlot value)).readStorage?
              readAddress readSlot =
            state.readStorage? readAddress readSlot := by
        simp only [WorldState.readStorage?]
        rw [WorldState.account?_putAccount_other state writtenAddress
          readAddress (account.storageWrite writtenSlot value) different]
      rw [written]
      simp only [Option.map_some]
      rw [readPreserved]

end Solcore.ContractRuntime
end

section
-- leanmerge: from Solcore.ContractRuntime.WorldStateCode
/-! Address-selected checked code lookup in explicit WorldState. -/

set_option autoImplicit false

/-!
## Consolidated module: `Solcore.ContractRuntime.WorldStateCodeExecution`
-/

/-! Address-selected execution until the first host boundary. -/

set_option autoImplicit false

/-!
## Consolidated module: `Solcore.ContractRuntime.WorldStateCodeProperties`
-/

/-! Lookup branches and finite-run safety for selected host-aware code. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.WorldState

@[simp] theorem code?_of_absent
    (state : WorldState)
    (codeAddress : Address)
    (absent : state.account? codeAddress = none) :
    state.code? codeAddress = none := by
  simp [code?, absent]

@[simp] theorem code?_of_account_without_code
    (state : WorldState)
    (codeAddress : Address)
    (account : Account)
    (present : state.account? codeAddress = some account)
    (withoutCode : account.code? = none) :
    state.code? codeAddress = none := by
  simp [code?, present, withoutCode]

@[simp] theorem code?_of_present
    (state : WorldState)
    (codeAddress : Address)
    (account : Account)
    (code : CheckedHostCoreProgram)
    (accountPresent : state.account? codeAddress = some account)
    (codePresent : account.code? = some code) :
    state.code? codeAddress = some code := by
  simp [code?, accountPresent, codePresent]

@[simp] theorem runCode?_of_absent
    (state : WorldState)
    (codeAddress : Address)
    (fuel : Nat)
    (absent : state.account? codeAddress = none) :
    state.runCode? codeAddress fuel = none := by
  simp [runCode?, code?, absent]

@[simp] theorem runCode?_of_account_without_code
    (state : WorldState)
    (codeAddress : Address)
    (account : Account)
    (fuel : Nat)
    (present : state.account? codeAddress = some account)
    (withoutCode : account.code? = none) :
    state.runCode? codeAddress fuel = none := by
  simp [runCode?, code?, present, withoutCode]

@[simp] theorem runCode?_of_present
    (state : WorldState)
    (codeAddress : Address)
    (account : Account)
    (code : CheckedHostCoreProgram)
    (fuel : Nat)
    (accountPresent : state.account? codeAddress = some account)
    (codePresent : account.code? = some code) :
    state.runCode? codeAddress fuel = some (code.runStateful fuel) := by
  simp [runCode?, code?, accountPresent, codePresent]

/-- Address-selected host-checked execution cannot return a machine fault. -/
theorem runCode?_ne_some_fault
    (state : WorldState)
    (codeAddress : Address)
    (fuel : Nat)
    (error : Core.MachineFault)
    (faultState : Core.State) :
    state.runCode? codeAddress fuel ≠ some (.fault error faultState) := by
  unfold runCode?
  cases selected : state.code? codeAddress with
  | none => simp
  | some code =>
      intro same
      exact code.runStateful_ne_fault fuel error faultState
        (Option.some.inj same)

end Solcore.ContractRuntime.WorldState

/-!
## Consolidated module: `Solcore.ContractRuntime.WorldStateCodeWriteProperties`
-/

/-! Exact laws for replacing checked code on one present Account. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.WorldState

@[simp] theorem writeCode?_of_absent
    (state : WorldState) (address : Address)
    (code : CheckedHostCoreProgram)
    (absent : state.account? address = none) :
    state.writeCode? address code = none := by
  simp [writeCode?, absent]

@[simp] theorem writeCode?_of_present
    (state : WorldState) (address : Address)
    (account : Account) (code : CheckedHostCoreProgram)
    (present : state.account? address = some account) :
    state.writeCode? address code =
      some (state.putAccount address (account.withCode code)) := by
  simp [writeCode?, present]

theorem account?_writeCode?_same
    (state : WorldState) (address : Address)
    (account : Account) (code : CheckedHostCoreProgram)
    (present : state.account? address = some account) :
    (state.writeCode? address code).bind
        (fun next => next.account? address) =
      some (account.withCode code) := by
  rw [writeCode?_of_present state address account code present]
  exact account?_putAccount_same state address (account.withCode code)

theorem code?_writeCode?_same
    (state : WorldState) (address : Address)
    (account : Account) (code : CheckedHostCoreProgram)
    (present : state.account? address = some account) :
    (state.writeCode? address code).bind
        (fun next => next.code? address) = some code := by
  rw [writeCode?_of_present state address account code present]
  simp only [Option.bind_some]
  apply code?_of_present
  · exact account?_putAccount_same _ _ _
  · exact Account.code?_withCode _ _

theorem account?_writeCode?_other
    (state : WorldState) (address other : Address)
    (account : Account) (code : CheckedHostCoreProgram)
    (present : state.account? address = some account)
    (different : other ≠ address) :
    (state.writeCode? address code).bind
        (fun next => next.account? other) = state.account? other := by
  rw [writeCode?_of_present state address account code present]
  exact account?_putAccount_other state address other
    (account.withCode code) different

theorem writeCode?_preserves_payload
    (state : WorldState) (address : Address)
    (account : Account) (code : CheckedHostCoreProgram)
    (present : state.account? address = some account) :
    (state.writeCode? address code).bind (fun next =>
        (next.account? address).map fun updated =>
          (updated.balance, updated.nonce,
            fun slot => updated.storageValue? slot)) =
      some (account.balance, account.nonce,
        fun slot => account.storageValue? slot) := by
  rw [writeCode?_of_present state address account code present]
  simp only [Option.bind_some, account?_putAccount_same, Option.map_some]
  simp

end Solcore.ContractRuntime.WorldState
end
