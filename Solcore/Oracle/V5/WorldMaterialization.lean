import Solcore.Oracle.V5.Input
import Solcore.ContractRuntime.AccountNonceProperties
import Solcore.ContractRuntime.AccountStorageWriteSparsePreservationProperties
import Solcore.ContractRuntime.WorldStateBalanceProperties
import Solcore.ContractRuntime.WorldStateNonceProperties
import Solcore.ContractRuntime.WorldState

/-! Canonical validation and materialization of the finite Oracle v5 world. -/

set_option autoImplicit false

namespace Solcore.Oracle.V5

open Solcore.ContractRuntime

/-- Closed failures produced while validating the finite initial world. -/
inductive WorldMaterializationError where
  | duplicateAccount (address : Address)
  | duplicateStorageSlot (address : Address) (slot : Core.Word)
  | zeroStorageValue (address : Address) (slot : Core.Word)
  | danglingContract (address : Address) (id : String)
  deriving Repr, BEq, DecidableEq

namespace WorldMaterialization

private def accountLE (left right : AccountInput) : Bool :=
  (compare left.address.val right.address.val).isLE

/-- Canonical world order is increasing unsigned Address value. -/
def canonicalAccounts (accounts : List AccountInput) : List AccountInput :=
  accounts.mergeSort accountLE

private def storageLE (left right : StorageInput) : Bool :=
  (compare left.slot.val right.slot.val).isLE

/-- Canonical Account storage order is increasing unsigned slot value. -/
def canonicalStorage (storage : List StorageInput) : List StorageInput :=
  storage.mergeSort storageLE

/-- Select the unique canonical input Account for an Address, when present. -/
def accountInput?
    (world : WorldInput)
    (address : Address) : Option AccountInput :=
  (canonicalAccounts world.accounts).find?
    (fun account => decide (account.address = address))

private def firstDuplicateAccount? :
    List AccountInput → Option Address
  | []
  | [_] => none
  | first :: second :: rest =>
      if first.address = second.address then
        some first.address
      else
        firstDuplicateAccount? (second :: rest)

private def firstDuplicateSlot?
    (address : Address) :
    List StorageInput → Option (Address × Core.Word)
  | []
  | [_] => none
  | first :: second :: rest =>
      if first.slot = second.slot then
        some (address, first.slot)
      else
        firstDuplicateSlot? address (second :: rest)

private def firstDuplicateStorage? :
    List AccountInput → Option (Address × Core.Word)
  | [] => none
  | account :: rest =>
      match firstDuplicateSlot? account.address
          (canonicalStorage account.storage) with
      | some duplicate => some duplicate
      | none => firstDuplicateStorage? rest

private def firstZeroStorage? :
    List AccountInput → Option (Address × Core.Word)
  | [] => none
  | account :: rest =>
      match (canonicalStorage account.storage).find?
          (fun entry => decide (entry.value = Core.Word.zero)) with
      | some entry => some (account.address, entry.slot)
      | none => firstZeroStorage? rest

private def firstDanglingCode?
    (resolveCode : String → Option CheckedHostCoreProgram) :
    List AccountInput → Option (Address × String)
  | [] => none
  | account :: rest =>
      match account.code with
      | some id =>
          if (resolveCode id).isSome then
            firstDanglingCode? resolveCode rest
          else
            some (account.address, id)
      | none => firstDanglingCode? resolveCode rest

/--
Validate semantic world constraints in the v5 precedence order and return the
canonical Account list. No semantic state is constructed on rejection.
-/
def validateWith
    (resolveCode : String → Option CheckedHostCoreProgram)
    (world : WorldInput) :
    Except WorldMaterializationError (List AccountInput) :=
  let accounts := canonicalAccounts world.accounts
  match firstDuplicateAccount? accounts with
  | some address => .error (.duplicateAccount address)
  | none =>
      match firstDuplicateStorage? accounts with
      | some (address, slot) =>
          .error (.duplicateStorageSlot address slot)
      | none =>
          match firstZeroStorage? accounts with
          | some (address, slot) =>
              .error (.zeroStorageValue address slot)
          | none =>
              match firstDanglingCode? resolveCode accounts with
              | some (address, id) =>
                  .error (.danglingContract address id)
              | none => .ok accounts

private def buildStorage
    (account : Account)
    (storage : List StorageInput) : Account :=
  storage.foldl
    (fun current entry => current.storageWrite entry.slot entry.value)
    account

private def observeStorageStep
    (slot : Core.Word)
    (current : Option Core.Word)
    (entry : StorageInput) : Option Core.Word :=
  if entry.slot = slot then
    if entry.value = Core.Word.zero then none else some entry.value
  else
    current

/-- Exact sparse-slot observation produced by canonical Account construction. -/
def storageValueOf
    (input : AccountInput)
    (slot : Core.Word) : Option Core.Word :=
  (canonicalStorage input.storage).foldl
    (observeStorageStep slot) none

private def buildAccount
    (resolveCode : String → Option CheckedHostCoreProgram)
    (input : AccountInput) :
    Except WorldMaterializationError Account :=
  let account :=
    buildStorage
      ((Account.empty.withBalance input.balance).withNonce input.nonce)
      (canonicalStorage input.storage)
  match input.code with
  | none => .ok account
  | some id =>
      match resolveCode id with
      | some code => .ok (account.withCode code)
      | none => .error (.danglingContract input.address id)

/-- Canonical semantic Account produced from one finite input entry. -/
def accountOfInputWith?
    (resolveCode : String → Option CheckedHostCoreProgram)
    (input : AccountInput) : Option Account :=
  (buildAccount resolveCode input).toOption

private def buildWorld
    (resolveCode : String → Option CheckedHostCoreProgram) :
    List AccountInput →
      Except WorldMaterializationError WorldState
  | [] => .ok WorldState.empty
  | account :: rest => do
      let state ← buildWorld resolveCode rest
      let materialized ← buildAccount resolveCode account
      .ok (state.putAccount account.address materialized)

/--
Validate and materialize the exact finite initial state using only the public
`Account` and `WorldState` constructors. Explicit empty Accounts remain present.
-/
def materializeWith
    (resolveCode : String → Option CheckedHostCoreProgram)
    (world : WorldInput) :
    Except WorldMaterializationError WorldState := do
  let accounts ← validateWith resolveCode world
  buildWorld resolveCode accounts

private theorem storageValue?_buildStorage
    (account : Account)
    (storage : List StorageInput)
    (slot : Core.Word) :
    (buildStorage account storage).storageValue? slot =
      storage.foldl (observeStorageStep slot)
        (account.storageValue? slot) := by
  unfold buildStorage
  induction storage generalizing account with
  | nil => rfl
  | cons entry rest inductionHypothesis =>
      simp only [List.foldl_cons]
      rw [inductionHypothesis]
      congr 1
      by_cases same : entry.slot = slot
      · subst slot
        by_cases zero : entry.value = Core.Word.zero
        · simpa [observeStorageStep, zero] using
            Account.storageValue?_storageWrite_zero account entry.slot
        · simp [observeStorageStep, zero,
            Account.storageValue?_storageWrite_nonzero]
      · have different : slot ≠ entry.slot := by
          exact fun equal => same equal.symm
        simp [observeStorageStep, same,
          Account.storageValue?_storageWrite_other, different]

private theorem balance_buildStorage
    (account : Account)
    (storage : List StorageInput) :
    (buildStorage account storage).balance = account.balance := by
  unfold buildStorage
  induction storage generalizing account with
  | nil => rfl
  | cons entry rest inductionHypothesis =>
      simp only [List.foldl_cons]
      rw [inductionHypothesis]
      exact Account.balance_storageWrite account entry.slot entry.value

private theorem nonce_buildStorage
    (account : Account)
    (storage : List StorageInput) :
    (buildStorage account storage).nonce = account.nonce := by
  unfold buildStorage
  induction storage generalizing account with
  | nil => rfl
  | cons entry rest inductionHypothesis =>
      simp only [List.foldl_cons]
      rw [inductionHypothesis]
      exact Account.nonce_storageWrite account entry.slot entry.value

private theorem code?_buildStorage
    (account : Account)
    (storage : List StorageInput) :
    (buildStorage account storage).code? = account.code? := by
  unfold buildStorage
  induction storage generalizing account with
  | nil => rfl
  | cons entry rest inductionHypothesis =>
      simp only [List.foldl_cons]
      rw [inductionHypothesis]
      exact Account.code?_storageWrite account entry.slot entry.value

private theorem validateWith_ok_eq_canonicalAccounts
    (resolveCode : String → Option CheckedHostCoreProgram)
    (world : WorldInput)
    (accounts : List AccountInput)
    (accepted : validateWith resolveCode world = .ok accounts) :
    accounts = canonicalAccounts world.accounts := by
  unfold validateWith at accepted
  dsimp only at accepted
  repeat first | split at accepted | simp_all

private theorem buildWorld_eq_ok_of_materializeWith
    (resolveCode : String → Option CheckedHostCoreProgram)
    (world : WorldInput)
    (state : WorldState)
    (success : materializeWith resolveCode world = .ok state) :
    buildWorld resolveCode (canonicalAccounts world.accounts) = .ok state := by
  cases validated : validateWith resolveCode world with
  | error failure =>
      unfold materializeWith at success
      simp only [validated, bind, Except.bind] at success
      cases success
  | ok accounts =>
      have canonical := validateWith_ok_eq_canonicalAccounts
        resolveCode world accounts validated
      subst accounts
      unfold materializeWith at success
      simpa only [validated, bind, Except.bind] using success

private theorem account?_buildWorld
    (resolveCode : String → Option CheckedHostCoreProgram)
    (accounts : List AccountInput)
    (state : WorldState)
    (built : buildWorld resolveCode accounts = .ok state)
    (address : Address) :
    state.account? address =
      (accounts.find? (fun account =>
        decide (account.address = address))).bind
          (accountOfInputWith? resolveCode) := by
  induction accounts generalizing state with
  | nil =>
      simp only [buildWorld, Except.ok.injEq] at built
      subst state
      simp [WorldState.account?_empty]
  | cons input rest inductionHypothesis =>
      cases restBuilt : buildWorld resolveCode rest with
      | error failure =>
          unfold buildWorld at built
          simp only [restBuilt, bind, Except.bind] at built
          cases built
      | ok restState =>
          cases accountBuilt : buildAccount resolveCode input with
          | error failure =>
              unfold buildWorld at built
              simp only [restBuilt, accountBuilt, bind, Except.bind] at built
              cases built
          | ok account =>
              have stateEq :
                  restState.putAccount input.address account = state := by
                apply Except.ok.inj
                simpa only [buildWorld, restBuilt, accountBuilt, bind,
                  Except.bind] using built
              subst state
              by_cases same : input.address = address
              · subst address
                simp [WorldState.account?_putAccount_same,
                  accountOfInputWith?, accountBuilt, Except.toOption]
              · have different : address ≠ input.address := by
                  exact fun equal => same equal.symm
                simp [same,
                  WorldState.account?_putAccount_other _ _ _ _ different,
                  inductionHypothesis restState restBuilt]

private theorem buildAccount_ok_of_mem_buildWorld
    (resolveCode : String → Option CheckedHostCoreProgram)
    (accounts : List AccountInput)
    (state : WorldState)
    (built : buildWorld resolveCode accounts = .ok state)
    (input : AccountInput)
    (member : input ∈ accounts) :
    ∃ account, buildAccount resolveCode input = .ok account := by
  induction accounts generalizing state with
  | nil => simp at member
  | cons first rest inductionHypothesis =>
      cases restBuilt : buildWorld resolveCode rest with
      | error failure =>
          unfold buildWorld at built
          simp only [restBuilt, bind, Except.bind] at built
          cases built
      | ok restState =>
          cases firstBuilt : buildAccount resolveCode first with
          | error failure =>
              unfold buildWorld at built
              simp only [restBuilt, firstBuilt, bind, Except.bind] at built
              cases built
          | ok account =>
              have stateEq :
                  restState.putAccount first.address account = state := by
                apply Except.ok.inj
                simpa only [buildWorld, restBuilt, firstBuilt, bind,
                  Except.bind] using built
              have cases : input = first ∨ input ∈ rest := by
                simpa using member
              rcases cases with equal | tailMember
              · subst input
                exact ⟨account, firstBuilt⟩
              · exact inductionHypothesis restState restBuilt tailMember

private theorem balance_buildAccount
    (resolveCode : String → Option CheckedHostCoreProgram)
    (input : AccountInput)
    (account : Account)
    (built : buildAccount resolveCode input = .ok account) :
    account.balance = input.balance := by
  rcases input with ⟨address, balance, nonce, storage, codeId⟩
  cases codeId with
  | none =>
      simp only [buildAccount, Except.ok.injEq] at built
      subst account
      simp [balance_buildStorage]
  | some id =>
      cases resolved : resolveCode id with
      | none => simp [buildAccount, resolved] at built
      | some code =>
          simp only [buildAccount, resolved, Except.ok.injEq] at built
          subst account
          simp [balance_buildStorage]

private theorem nonce_buildAccount
    (resolveCode : String → Option CheckedHostCoreProgram)
    (input : AccountInput)
    (account : Account)
    (built : buildAccount resolveCode input = .ok account) :
    account.nonce = input.nonce := by
  rcases input with ⟨address, balance, nonce, storage, codeId⟩
  cases codeId with
  | none =>
      simp only [buildAccount, Except.ok.injEq] at built
      subst account
      simp [nonce_buildStorage]
  | some id =>
      cases resolved : resolveCode id with
      | none => simp [buildAccount, resolved] at built
      | some code =>
          simp only [buildAccount, resolved, Except.ok.injEq] at built
          subst account
          simp [nonce_buildStorage]

private theorem storageValue?_buildAccount
    (resolveCode : String → Option CheckedHostCoreProgram)
    (input : AccountInput)
    (account : Account)
    (built : buildAccount resolveCode input = .ok account)
    (slot : Core.Word) :
    account.storageValue? slot = storageValueOf input slot := by
  rcases input with ⟨address, balance, nonce, storage, codeId⟩
  cases codeId with
  | none =>
      simp only [buildAccount, Except.ok.injEq] at built
      subst account
      simp [storageValueOf, storageValue?_buildStorage,
        Account.storageValue?_empty]
  | some id =>
      cases resolved : resolveCode id with
      | none => simp [buildAccount, resolved] at built
      | some code =>
          simp only [buildAccount, resolved, Except.ok.injEq] at built
          subst account
          simp [storageValueOf, storageValue?_buildStorage,
            Account.storageValue?_empty]

private theorem code?_buildAccount
    (resolveCode : String → Option CheckedHostCoreProgram)
    (input : AccountInput)
    (account : Account)
    (built : buildAccount resolveCode input = .ok account) :
    account.code? = input.code.bind resolveCode := by
  rcases input with ⟨address, balance, nonce, storage, codeId⟩
  cases codeId with
  | none =>
      simp only [buildAccount, Except.ok.injEq] at built
      subst account
      simp [code?_buildStorage]
  | some id =>
      cases resolved : resolveCode id with
      | none => simp [buildAccount, resolved] at built
      | some code =>
          simp only [buildAccount, resolved, Except.ok.injEq] at built
          subst account
          simp [resolved]

private theorem exists_buildAccount_eq_ok_of_input
    (resolveCode : String → Option CheckedHostCoreProgram)
    (world : WorldInput)
    (state : WorldState)
    (success : materializeWith resolveCode world = .ok state)
    (address : Address)
    (input : AccountInput)
    (selected : accountInput? world address = some input) :
    ∃ account, buildAccount resolveCode input = .ok account := by
  have member : input ∈ canonicalAccounts world.accounts := by
    exact List.mem_of_find?_eq_some selected
  exact buildAccount_ok_of_mem_buildWorld resolveCode
    (canonicalAccounts world.accounts) state
    (buildWorld_eq_ok_of_materializeWith resolveCode world state success)
    input member

/--
Every successful finite-world materialization has exactly the Account selected
by the canonical input lookup, and no Account at any other Address.
-/
theorem account?_of_materializeWith
    (resolveCode : String → Option CheckedHostCoreProgram)
    (world : WorldInput)
    (state : WorldState)
    (success : materializeWith resolveCode world = .ok state)
    (address : Address) :
    state.account? address =
      (accountInput? world address).bind
        (accountOfInputWith? resolveCode) := by
  exact account?_buildWorld resolveCode
    (canonicalAccounts world.accounts) state
    (buildWorld_eq_ok_of_materializeWith resolveCode world state success)
    address

/-- Every canonical input selected after acceptance constructed one Account. -/
theorem exists_accountOfInputWith?_eq_some
    (resolveCode : String → Option CheckedHostCoreProgram)
    (world : WorldInput)
    (state : WorldState)
    (success : materializeWith resolveCode world = .ok state)
    (address : Address)
    (input : AccountInput)
    (selected : accountInput? world address = some input) :
    ∃ account, accountOfInputWith? resolveCode input = some account := by
  rcases exists_buildAccount_eq_ok_of_input resolveCode world state success
      address input selected with ⟨account, built⟩
  exact ⟨account, by simp [accountOfInputWith?, built, Except.toOption]⟩

/-- A successful materialization contains no Account outside its finite input. -/
theorem account?_eq_none_of_input_absent
    (resolveCode : String → Option CheckedHostCoreProgram)
    (world : WorldInput)
    (state : WorldState)
    (success : materializeWith resolveCode world = .ok state)
    (address : Address)
    (absent : accountInput? world address = none) :
    state.account? address = none := by
  rw [account?_of_materializeWith resolveCode world state success address,
    absent]
  rfl

/-- Every selected input Account preserves its exact balance. -/
theorem balance?_of_input
    (resolveCode : String → Option CheckedHostCoreProgram)
    (world : WorldInput)
    (state : WorldState)
    (success : materializeWith resolveCode world = .ok state)
    (address : Address)
    (input : AccountInput)
    (selected : accountInput? world address = some input) :
    state.balance? address = some input.balance := by
  rcases exists_buildAccount_eq_ok_of_input resolveCode world state success
      address input selected with ⟨account, built⟩
  have accountBuilt :
      accountOfInputWith? resolveCode input = some account := by
    simp [accountOfInputWith?, built, Except.toOption]
  rw [WorldState.balance?,
    account?_of_materializeWith resolveCode world state success address,
    selected]
  simp only [Option.bind_some]
  rw [accountBuilt]
  exact congrArg some (balance_buildAccount resolveCode input account built)

/-- Every selected input Account preserves its exact creation nonce. -/
theorem nonce?_of_input
    (resolveCode : String → Option CheckedHostCoreProgram)
    (world : WorldInput)
    (state : WorldState)
    (success : materializeWith resolveCode world = .ok state)
    (address : Address)
    (input : AccountInput)
    (selected : accountInput? world address = some input) :
    state.nonce? address = some input.nonce := by
  rcases exists_buildAccount_eq_ok_of_input resolveCode world state success
      address input selected with ⟨account, built⟩
  have accountBuilt :
      accountOfInputWith? resolveCode input = some account := by
    simp [accountOfInputWith?, built, Except.toOption]
  rw [WorldState.nonce?,
    account?_of_materializeWith resolveCode world state success address,
    selected]
  simp only [Option.bind_some]
  rw [accountBuilt]
  exact congrArg some (nonce_buildAccount resolveCode input account built)

/-- Every selected input Account has exactly the sparse storage it supplied. -/
theorem storageValue?_of_input
    (resolveCode : String → Option CheckedHostCoreProgram)
    (world : WorldInput)
    (state : WorldState)
    (success : materializeWith resolveCode world = .ok state)
    (address : Address)
    (input : AccountInput)
    (selected : accountInput? world address = some input)
    (slot : Core.Word) :
    (state.account? address).bind
        (fun account => account.storageValue? slot) =
      storageValueOf input slot := by
  rcases exists_buildAccount_eq_ok_of_input resolveCode world state success
      address input selected with ⟨account, built⟩
  have accountBuilt :
      accountOfInputWith? resolveCode input = some account := by
    simp [accountOfInputWith?, built, Except.toOption]
  rw [account?_of_materializeWith resolveCode world state success address,
    selected]
  simp only [Option.bind_some]
  rw [accountBuilt]
  exact storageValue?_buildAccount resolveCode input account built slot

/-- Checked code is present exactly when the selected input names its source. -/
theorem code?_of_input
    (resolveCode : String → Option CheckedHostCoreProgram)
    (world : WorldInput)
    (state : WorldState)
    (success : materializeWith resolveCode world = .ok state)
    (address : Address)
    (input : AccountInput)
    (selected : accountInput? world address = some input) :
    (state.account? address).bind Account.code? =
      input.code.bind resolveCode := by
  rcases exists_buildAccount_eq_ok_of_input resolveCode world state success
      address input selected with ⟨account, built⟩
  have accountBuilt :
      accountOfInputWith? resolveCode input = some account := by
    simp [accountOfInputWith?, built, Except.toOption]
  rw [account?_of_materializeWith resolveCode world state success address,
    selected]
  simp only [Option.bind_some]
  rw [accountBuilt]
  exact code?_buildAccount resolveCode input account built

end WorldMaterialization

end Solcore.Oracle.V5
