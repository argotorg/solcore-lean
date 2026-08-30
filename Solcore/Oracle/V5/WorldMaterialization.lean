import Solcore.Oracle.V5.Input
import Solcore.Semantics.WorldState

/-! Canonical validation and materialization of the finite Oracle v5 world. -/

set_option autoImplicit false

namespace Solcore.Oracle.V5

open Solcore.Semantics

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

end WorldMaterialization

end Solcore.Oracle.V5
