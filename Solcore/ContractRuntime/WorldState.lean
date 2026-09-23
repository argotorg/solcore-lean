import Solcore.ContractRuntime.RuntimeScalars
import Solcore.ContractRuntime.CheckedHostCoreProgram

set_option autoImplicit false

namespace Solcore.ContractRuntime

/-- Account code and sparse storage whose lookup never returns a stored zero. -/
structure Account where private mk ::
  private storage : Core.Word → Option Core.Word
  private storage_nonzero :
    ∀ slot value, storage slot = some value → value ≠ Core.Word.zero
  private code : Option CheckedHostCoreProgram
  private balanceValue : Core.Word
  private nonceValue : Core.Word

/-- Semantic lookup for an explicitly present or absent account. -/
structure WorldState where private mk ::
  private accounts : Address → Option Account

namespace Account

/-- The present account with neither code nor stored values. -/
def empty : Account :=
  ⟨fun _ => none, by simp, none, Core.Word.zero, Core.Word.zero⟩

/-- Observe the account's exact unsigned 256-bit balance. -/
def balance (account : Account) : Core.Word :=
  account.balanceValue

/-- Observe the exact unsigned 256-bit creation nonce. -/
def nonce (account : Account) : Core.Word :=
  account.nonceValue

/-- Replace the balance while preserving storage and checked code. -/
def withBalance
    (account : Account)
    (balance : Core.Word) : Account :=
  ⟨account.storage, account.storage_nonzero, account.code, balance,
    account.nonceValue⟩

/-- Replace the creation nonce while preserving storage, code, and balance. -/
def withNonce
    (account : Account)
    (nonce : Core.Word) : Account :=
  ⟨account.storage, account.storage_nonzero, account.code,
    account.balanceValue, nonce⟩

/-- Observe the host-checker-accepted code associated with this Account. -/
def code? (account : Account) : Option CheckedHostCoreProgram :=
  account.code

/-- Associate checker-accepted code while preserving the complete storage. -/
def withCode
    (account : Account)
    (code : CheckedHostCoreProgram) : Account :=
  ⟨account.storage, account.storage_nonzero, some code,
    account.balanceValue, account.nonceValue⟩

/-- Observe whether a semantic nonzero storage value exists. -/
def storageValue?
    (account : Account)
    (slot : Core.Word) : Option Core.Word :=
  account.storage slot

/-- Read a missing storage slot as zero. -/
def storageRead (account : Account) (slot : Core.Word) : Core.Word :=
  (account.storageValue? slot).getD Core.Word.zero

/-- Store nonzero values and delete the selected value when writing zero. -/
def storageWrite
    (account : Account)
    (slot value : Core.Word) : Account :=
  if zero : value = Core.Word.zero then
    ⟨fun current => if current = slot then none else account.storage current,
      by
        intro current stored present
        split at present
        · contradiction
        · exact account.storage_nonzero current stored present,
      account.code,
      account.balanceValue,
      account.nonceValue⟩
  else
    ⟨fun current => if current = slot then some value else account.storage current,
      by
        intro current stored present
        split at present
        · intro stored_zero
          exact zero ((Option.some.inj present).trans stored_zero)
        · exact account.storage_nonzero current stored present,
      account.code,
      account.balanceValue,
      account.nonceValue⟩

end Account

namespace WorldState

/-- The world state in which every account is absent. -/
def empty : WorldState :=
  ⟨fun _ => none⟩

/-- Look up an account without conflating absence with an empty account. -/
def account?
    (state : WorldState)
    (address : Address) : Option Account :=
  state.accounts address

/-- Insert or replace an explicitly present account. -/
def putAccount
    (state : WorldState)
    (address : Address)
    (account : Account) : WorldState :=
  ⟨fun current => if current = address then some account
    else state.accounts current⟩

/-- Update storage only when the addressed account exists. -/
def writeStorage?
    (state : WorldState)
    (address : Address)
    (slot value : Core.Word) : Option WorldState := do
  let account ← state.account? address
  some (state.putAccount address (account.storageWrite slot value))

/-- Observe a balance without conflating an absent account with zero balance. -/
def balance?
    (state : WorldState)
    (address : Address) : Option Core.Word := do
  let account ← state.account? address
  some account.balance

/-- Replace a balance only when the addressed account exists. -/
def writeBalance?
    (state : WorldState)
    (address : Address)
    (balance : Core.Word) : Option WorldState := do
  let account ← state.account? address
  some (state.putAccount address (account.withBalance balance))

/-- Observe a nonce without conflating an absent account with nonce zero. -/
def nonce?
    (state : WorldState)
    (address : Address) : Option Core.Word := do
  let account ← state.account? address
  some account.nonce

/-- Replace a nonce only when the addressed account exists. -/
def writeNonce?
    (state : WorldState)
    (address : Address)
    (nonce : Core.Word) : Option WorldState := do
  let account ← state.account? address
  some (state.putAccount address (account.withNonce nonce))

/-- Replace checked code only when the addressed account exists. -/
def writeCode?
    (state : WorldState)
    (address : Address)
    (code : CheckedHostCoreProgram) : Option WorldState := do
  let account ← state.account? address
  some (state.putAccount address (account.withCode code))

end WorldState

end Solcore.ContractRuntime

/-!
## Consolidated module: `Solcore.ContractRuntime.WorldStateProperties`
-/

set_option autoImplicit false

namespace Solcore.ContractRuntime

theorem WorldState.account?_empty (address : Address) :
    WorldState.empty.account? address = none := by
  rfl

theorem WorldState.account?_putAccount_same
    (state : WorldState)
    (address : Address)
    (account : Account) :
    (state.putAccount address account).account? address = some account := by
  simp [WorldState.putAccount, WorldState.account?]

theorem WorldState.account?_putAccount_other
    (state : WorldState)
    (address other : Address)
    (account : Account)
    (different : other ≠ address) :
    (state.putAccount address account).account? other =
      state.account? other := by
  simp [WorldState.putAccount, WorldState.account?, different]

theorem Account.storageValue?_empty (slot : Core.Word) :
    Account.empty.storageValue? slot = none := by
  rfl

theorem Account.storageRead_empty (slot : Core.Word) :
    Account.empty.storageRead slot = Core.Word.zero := by
  rfl

theorem Account.storageRead_storageWrite_same
    (account : Account)
    (slot value : Core.Word) :
    (account.storageWrite slot value).storageRead slot = value := by
  by_cases zero : value = Core.Word.zero
  · simp [Account.storageWrite, Account.storageRead,
      Account.storageValue?, zero]
  · simp [Account.storageWrite, Account.storageRead,
      Account.storageValue?, zero]

theorem Account.storageValue?_storageWrite_zero
    (account : Account)
    (slot : Core.Word) :
    (account.storageWrite slot Core.Word.zero).storageValue? slot = none := by
  simp [Account.storageWrite, Account.storageValue?]

theorem Account.storageValue?_storageWrite_nonzero
    (account : Account)
    (slot value : Core.Word)
    (nonzero : value ≠ Core.Word.zero) :
    (account.storageWrite slot value).storageValue? slot = some value := by
  simp [Account.storageWrite, Account.storageValue?, nonzero]

theorem Account.storageRead_storageWrite_other
    (account : Account)
    (slot value other : Core.Word)
    (different : other ≠ slot) :
    (account.storageWrite slot value).storageRead other =
      account.storageRead other := by
  by_cases zero : value = Core.Word.zero
  · simp [Account.storageWrite, Account.storageRead,
      Account.storageValue?, zero, different]
  · simp [Account.storageWrite, Account.storageRead,
      Account.storageValue?, zero, different]

theorem WorldState.writeStorage?_of_absent
    (state : WorldState)
    (address : Address)
    (slot value : Core.Word)
    (absent : state.account? address = none) :
    state.writeStorage? address slot value = none := by
  simp [WorldState.writeStorage?, absent]

theorem WorldState.account?_writeStorage?_same
    (state : WorldState)
    (address : Address)
    (account : Account)
    (slot value : Core.Word)
    (present : state.account? address = some account) :
    (state.writeStorage? address slot value).bind
        (fun next => next.account? address) =
      some (account.storageWrite slot value) := by
  rw [show state.writeStorage? address slot value =
      some (state.putAccount address (account.storageWrite slot value)) by
    simp [WorldState.writeStorage?, present]]
  simp [WorldState.account?_putAccount_same]

theorem WorldState.account?_writeStorage?_other
    (state : WorldState)
    (address other : Address)
    (account : Account)
    (slot value : Core.Word)
    (present : state.account? address = some account)
    (different : other ≠ address) :
    (state.writeStorage? address slot value).bind
        (fun next => next.account? other) =
      state.account? other := by
  rw [show state.writeStorage? address slot value =
      some (state.putAccount address (account.storageWrite slot value)) by
    simp [WorldState.writeStorage?, present]]
  simpa using WorldState.account?_putAccount_other state address other
    (account.storageWrite slot value) different

end Solcore.ContractRuntime

/-!
## Consolidated module: `Solcore.ContractRuntime.WorldStateExtensionalityProperties`
-/

set_option autoImplicit false

namespace Solcore.ContractRuntime

@[ext] theorem Account.ext
    {left right : Account}
    (sameStorage : ∀ slot,
      left.storageValue? slot = right.storageValue? slot)
    (sameCode : left.code? = right.code?)
    (sameBalance : left.balance = right.balance)
    (sameNonce : left.nonce = right.nonce) :
    left = right := by
  cases left
  cases right
  simp only [Account.storageValue?] at sameStorage
  simp only [Account.code?] at sameCode
  simp only [Account.balance] at sameBalance
  simp only [Account.nonce] at sameNonce
  congr
  funext slot
  exact sameStorage slot

@[ext] theorem WorldState.ext
    {left right : WorldState}
    (same : ∀ address,
      left.account? address = right.account? address) :
    left = right := by
  cases left
  cases right
  simp only [WorldState.account?] at same
  congr
  funext address
  exact same address

end Solcore.ContractRuntime

/-!
## Consolidated module: `Solcore.ContractRuntime.WorldStateUpdateAlgebraProperties`
-/

set_option autoImplicit false

namespace Solcore.ContractRuntime

@[simp] theorem Account.storageWrite_overwrite
    (account : Account)
    (slot first second : Core.Word) :
    (account.storageWrite slot first).storageWrite slot second =
      account.storageWrite slot second := by
  apply Account.ext
  · intro current
    by_cases firstZero : first = Core.Word.zero
    <;> by_cases secondZero : second = Core.Word.zero
    <;> by_cases selected : current = slot
    <;> simp [Account.storageWrite, Account.storageValue?, firstZero,
      secondZero, selected]
  · by_cases firstZero : first = Core.Word.zero
    <;> by_cases secondZero : second = Core.Word.zero
    <;> simp [Account.storageWrite, Account.code?, firstZero, secondZero]
  · by_cases firstZero : first = Core.Word.zero
    <;> by_cases secondZero : second = Core.Word.zero
    <;> simp [Account.storageWrite, Account.balance, firstZero, secondZero]
  · by_cases firstZero : first = Core.Word.zero
    <;> by_cases secondZero : second = Core.Word.zero
    <;> simp [Account.storageWrite, Account.nonce, firstZero, secondZero]

theorem Account.storageWrite_commute
    (account : Account)
    (leftSlot leftValue rightSlot rightValue : Core.Word)
    (different : leftSlot ≠ rightSlot) :
    (account.storageWrite leftSlot leftValue).storageWrite
        rightSlot rightValue =
      (account.storageWrite rightSlot rightValue).storageWrite
        leftSlot leftValue := by
  have reverse : rightSlot ≠ leftSlot := Ne.symm different
  apply Account.ext
  · intro current
    by_cases leftZero : leftValue = Core.Word.zero
    <;> by_cases rightZero : rightValue = Core.Word.zero
    <;> by_cases atLeft : current = leftSlot
    <;> by_cases atRight : current = rightSlot
    <;> simp [Account.storageWrite, Account.storageValue?, leftZero, rightZero,
      atLeft, atRight, different, reverse]
  · by_cases leftZero : leftValue = Core.Word.zero
    <;> by_cases rightZero : rightValue = Core.Word.zero
    <;> simp [Account.storageWrite, Account.code?, leftZero, rightZero]
  · by_cases leftZero : leftValue = Core.Word.zero
    <;> by_cases rightZero : rightValue = Core.Word.zero
    <;> simp [Account.storageWrite, Account.balance, leftZero, rightZero]
  · by_cases leftZero : leftValue = Core.Word.zero
    <;> by_cases rightZero : rightValue = Core.Word.zero
    <;> simp [Account.storageWrite, Account.nonce, leftZero, rightZero]

@[simp] theorem WorldState.putAccount_overwrite
    (state : WorldState)
    (address : Address)
    (first second : Account) :
    (state.putAccount address first).putAccount address second =
      state.putAccount address second := by
  apply WorldState.ext
  intro current
  by_cases selected : current = address
  <;> simp [WorldState.putAccount, WorldState.account?, selected]

theorem WorldState.putAccount_commute
    (state : WorldState)
    (leftAddress rightAddress : Address)
    (leftAccount rightAccount : Account)
    (different : leftAddress ≠ rightAddress) :
    (state.putAccount leftAddress leftAccount).putAccount
        rightAddress rightAccount =
      (state.putAccount rightAddress rightAccount).putAccount
        leftAddress leftAccount := by
  have reverse : rightAddress ≠ leftAddress := Ne.symm different
  apply WorldState.ext
  intro current
  by_cases atLeft : current = leftAddress
  <;> by_cases atRight : current = rightAddress
  <;> simp [WorldState.putAccount, WorldState.account?, atLeft, atRight,
    different, reverse]

end Solcore.ContractRuntime

/-!
## Consolidated module: `Solcore.ContractRuntime.WorldStateStorageWriteAlgebraProperties`
-/

set_option autoImplicit false

namespace Solcore.ContractRuntime

private theorem WorldState.writeStorage?_of_present
    (state : WorldState)
    (address : Address)
    (account : Account)
    (slot value : Core.Word)
    (present : state.account? address = some account) :
    state.writeStorage? address slot value =
      some (state.putAccount address (account.storageWrite slot value)) := by
  simp [WorldState.writeStorage?, present]

@[simp] theorem WorldState.writeStorage?_overwrite
    (state : WorldState)
    (address : Address)
    (slot first second : Core.Word) :
    (state.writeStorage? address slot first).bind
        (fun next => next.writeStorage? address slot second) =
      state.writeStorage? address slot second := by
  cases present : state.account? address with
  | none =>
      rw [WorldState.writeStorage?_of_absent state address slot first present]
      rw [WorldState.writeStorage?_of_absent state address slot second present]
      rfl
  | some account =>
      rw [WorldState.writeStorage?_of_present state address account slot first
        present]
      simp only [Option.bind_some]
      rw [WorldState.writeStorage?_of_present
        (state.putAccount address (account.storageWrite slot first)) address
        (account.storageWrite slot first) slot second
        (WorldState.account?_putAccount_same state address
          (account.storageWrite slot first))]
      rw [WorldState.writeStorage?_of_present state address account slot second
        present]
      simp

theorem WorldState.writeStorage?_commute_slots
    (state : WorldState)
    (address : Address)
    (leftSlot leftValue rightSlot rightValue : Core.Word)
    (different : leftSlot ≠ rightSlot) :
    (state.writeStorage? address leftSlot leftValue).bind
        (fun next => next.writeStorage? address rightSlot rightValue) =
      (state.writeStorage? address rightSlot rightValue).bind
        (fun next => next.writeStorage? address leftSlot leftValue) := by
  cases present : state.account? address with
  | none =>
      rw [WorldState.writeStorage?_of_absent state address leftSlot leftValue
        present]
      rw [WorldState.writeStorage?_of_absent state address rightSlot rightValue
        present]
      rfl
  | some account =>
      rw [WorldState.writeStorage?_of_present state address account leftSlot
        leftValue present]
      rw [WorldState.writeStorage?_of_present state address account rightSlot
        rightValue present]
      simp only [Option.bind_some]
      rw [WorldState.writeStorage?_of_present
        (state.putAccount address (account.storageWrite leftSlot leftValue))
        address (account.storageWrite leftSlot leftValue) rightSlot rightValue
        (WorldState.account?_putAccount_same state address
          (account.storageWrite leftSlot leftValue))]
      rw [WorldState.writeStorage?_of_present
        (state.putAccount address (account.storageWrite rightSlot rightValue))
        address (account.storageWrite rightSlot rightValue) leftSlot leftValue
        (WorldState.account?_putAccount_same state address
          (account.storageWrite rightSlot rightValue))]
      rw [Account.storageWrite_commute account leftSlot leftValue rightSlot
        rightValue different]
      simp

theorem WorldState.writeStorage?_commute_addresses
    (state : WorldState)
    (leftAddress rightAddress : Address)
    (leftSlot leftValue rightSlot rightValue : Core.Word)
    (different : leftAddress ≠ rightAddress) :
    (state.writeStorage? leftAddress leftSlot leftValue).bind
        (fun next =>
          next.writeStorage? rightAddress rightSlot rightValue) =
      (state.writeStorage? rightAddress rightSlot rightValue).bind
        (fun next =>
          next.writeStorage? leftAddress leftSlot leftValue) := by
  have reverse : rightAddress ≠ leftAddress := Ne.symm different
  cases leftPresent : state.account? leftAddress with
  | none =>
      rw [WorldState.writeStorage?_of_absent state leftAddress leftSlot
        leftValue leftPresent]
      simp only [Option.bind_none]
      cases rightPresent : state.account? rightAddress with
      | none =>
          rw [WorldState.writeStorage?_of_absent state rightAddress rightSlot
            rightValue rightPresent]
          rfl
      | some rightAccount =>
          rw [WorldState.writeStorage?_of_present state rightAddress
            rightAccount rightSlot rightValue rightPresent]
          simp only [Option.bind_some]
          have leftAfter :
              (state.putAccount rightAddress
                (rightAccount.storageWrite rightSlot rightValue)).account?
                  leftAddress = none := by
            rw [WorldState.account?_putAccount_other state rightAddress
              leftAddress (rightAccount.storageWrite rightSlot rightValue)
              different]
            exact leftPresent
          rw [WorldState.writeStorage?_of_absent
            (state.putAccount rightAddress
              (rightAccount.storageWrite rightSlot rightValue))
            leftAddress leftSlot leftValue leftAfter]
  | some leftAccount =>
      cases rightPresent : state.account? rightAddress with
      | none =>
          rw [WorldState.writeStorage?_of_present state leftAddress leftAccount
            leftSlot leftValue leftPresent]
          simp only [Option.bind_some]
          have rightAfter :
              (state.putAccount leftAddress
                (leftAccount.storageWrite leftSlot leftValue)).account?
                  rightAddress = none := by
            rw [WorldState.account?_putAccount_other state leftAddress
              rightAddress (leftAccount.storageWrite leftSlot leftValue)
              reverse]
            exact rightPresent
          rw [WorldState.writeStorage?_of_absent
            (state.putAccount leftAddress
              (leftAccount.storageWrite leftSlot leftValue))
            rightAddress rightSlot rightValue rightAfter]
          rw [WorldState.writeStorage?_of_absent state rightAddress rightSlot
            rightValue rightPresent]
          rfl
      | some rightAccount =>
          rw [WorldState.writeStorage?_of_present state leftAddress leftAccount
            leftSlot leftValue leftPresent]
          rw [WorldState.writeStorage?_of_present state rightAddress
            rightAccount rightSlot rightValue rightPresent]
          simp only [Option.bind_some]
          have rightAfter :
              (state.putAccount leftAddress
                (leftAccount.storageWrite leftSlot leftValue)).account?
                  rightAddress = some rightAccount := by
            rw [WorldState.account?_putAccount_other state leftAddress
              rightAddress (leftAccount.storageWrite leftSlot leftValue)
              reverse]
            exact rightPresent
          have leftAfter :
              (state.putAccount rightAddress
                (rightAccount.storageWrite rightSlot rightValue)).account?
                  leftAddress = some leftAccount := by
            rw [WorldState.account?_putAccount_other state rightAddress
              leftAddress (rightAccount.storageWrite rightSlot rightValue)
              different]
            exact leftPresent
          rw [WorldState.writeStorage?_of_present
            (state.putAccount leftAddress
              (leftAccount.storageWrite leftSlot leftValue))
            rightAddress rightAccount rightSlot rightValue rightAfter]
          rw [WorldState.writeStorage?_of_present
            (state.putAccount rightAddress
              (rightAccount.storageWrite rightSlot rightValue))
            leftAddress leftAccount leftSlot leftValue leftAfter]
          exact congrArg some (WorldState.putAccount_commute state leftAddress
            rightAddress (leftAccount.storageWrite leftSlot leftValue)
            (rightAccount.storageWrite rightSlot rightValue) different)

theorem WorldState.writeStorage?_zero_deletes
    (state : WorldState) (address : Address)
    (account : Account) (slot : Core.Word)
    (present : state.account? address = some account) :
    ∃ next,
      state.writeStorage? address slot Core.Word.zero = some next ∧
      next.account? address =
        some (account.storageWrite slot Core.Word.zero) ∧
      (account.storageWrite slot Core.Word.zero).storageValue? slot = none := by
  refine ⟨state.putAccount address
      (account.storageWrite slot Core.Word.zero), ?_, ?_, ?_⟩
  · exact WorldState.writeStorage?_of_present state address account slot
      Core.Word.zero present
  · exact WorldState.account?_putAccount_same state address
      (account.storageWrite slot Core.Word.zero)
  · exact Account.storageValue?_storageWrite_zero account slot

end Solcore.ContractRuntime
