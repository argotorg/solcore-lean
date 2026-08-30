import Solcore.Semantics.WorldStateNonceProperties

/-! Compile-time and executable regressions for account creation nonces. -/

set_option autoImplicit false

namespace Tests

open Solcore
open Solcore.Semantics

example : Account.empty.nonce = Core.Word.zero :=
  Account.nonce_empty

example (account : Account) (nonce : Core.Word) :
    (account.withNonce nonce).nonce = nonce :=
  Account.nonce_withNonce account nonce

example (account : Account) (nonce slot : Core.Word) :
    (account.withNonce nonce).storageValue? slot =
      account.storageValue? slot :=
  Account.storageValue?_withNonce account nonce slot

example (account : Account) (nonce : Core.Word) :
    (account.withNonce nonce).code? = account.code? :=
  Account.code?_withNonce account nonce

example (account : Account) (nonce : Core.Word) :
    (account.withNonce nonce).balance = account.balance :=
  Account.balance_withNonce account nonce

example (account : Account) (balance : Core.Word) :
    (account.withBalance balance).nonce = account.nonce :=
  Account.nonce_withBalance account balance

example (account : Account) (code : CheckedHostCoreProgram) :
    (account.withCode code).nonce = account.nonce :=
  Account.nonce_withCode account code

example (account : Account) (slot value : Core.Word) :
    (account.storageWrite slot value).nonce = account.nonce :=
  Account.nonce_storageWrite account slot value

example (address : Address) :
    WorldState.empty.nonce? address = none :=
  WorldState.nonce?_empty address

example (state : WorldState) (address : Address) (account : Account) :
    (state.putAccount address account).nonce? address =
      some account.nonce :=
  WorldState.nonce?_putAccount_same state address account

example (state : WorldState) (address other : Address) (account : Account)
    (different : other ≠ address) :
    (state.putAccount address account).nonce? other = state.nonce? other :=
  WorldState.nonce?_putAccount_other state address other account different

example (state : WorldState) (address : Address) (nonce : Core.Word)
    (absent : state.account? address = none) :
    state.writeNonce? address nonce = none :=
  WorldState.writeNonce?_of_absent state address nonce absent

example (state : WorldState) (address : Address) (account : Account)
    (nonce : Core.Word) (present : state.account? address = some account) :
    state.writeNonce? address nonce =
      some (state.putAccount address (account.withNonce nonce)) :=
  WorldState.writeNonce?_of_present state address account nonce present

example (state : WorldState) (address : Address) (account : Account)
    (nonce : Core.Word) (present : state.account? address = some account) :
    (state.writeNonce? address nonce).bind
        (fun next => next.account? address) =
      some (account.withNonce nonce) :=
  WorldState.account?_writeNonce?_same state address account nonce present

example (state : WorldState) (address : Address) (account : Account)
    (nonce : Core.Word) (present : state.account? address = some account) :
    (state.writeNonce? address nonce).bind
        (fun next => next.nonce? address) = some nonce :=
  WorldState.nonce?_writeNonce?_same state address account nonce present

example (state : WorldState) (address other : Address) (account : Account)
    (nonce : Core.Word) (present : state.account? address = some account)
    (different : other ≠ address) :
    (state.writeNonce? address nonce).bind
        (fun next => next.account? other) = state.account? other :=
  WorldState.account?_writeNonce?_other state address other account nonce
    present different

example (state : WorldState) (address : Address) (account : Account)
    (nonce : Core.Word) (present : state.account? address = some account) :
    (state.writeNonce? address nonce).bind (fun next =>
        (next.account? address).map fun updated =>
          (updated.code?, updated.balance,
            fun slot => updated.storageValue? slot)) =
      some (account.code?, account.balance,
        fun slot => account.storageValue? slot) :=
  WorldState.writeNonce?_preserves_payload state address account nonce present

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do
    throw (IO.userError message)

private def addressA : Address := ⟨0, by decide⟩
private def addressB : Address := ⟨1, by decide⟩
private def nonceA : Core.Word := ⟨23, by decide⟩
private def balanceA : Core.Word := ⟨41, by decide⟩
private def slotA : Core.Word := ⟨7, by decide⟩
private def storedA : Core.Word := ⟨99, by decide⟩
private def otherNonce : Core.Word := ⟨5, by decide⟩

def testWorldStateNonce : IO Unit := do
  assertTrue (Account.empty.nonce == Core.Word.zero)
    "an empty present account must start with nonce zero"
  assertTrue (WorldState.empty.nonce? addressA == none)
    "an absent account must not be reported as a zero-nonce account"
  assertTrue (WorldState.empty.writeNonce? addressA nonceA).isNone
    "writing nonce must not create an absent account"
  let account :=
    (Account.empty.storageWrite slotA storedA).withBalance balanceA
  let world :=
    (WorldState.empty.putAccount addressA account).putAccount addressB
      (Account.empty.withNonce otherNonce)
  assertTrue (world.nonce? addressA == some Core.Word.zero)
    "a present account must expose its initial zero nonce"
  assertTrue
    (match world.writeNonce? addressA nonceA with
      | none => false
      | some updated =>
          match updated.account? addressA with
          | none => false
          | some changed =>
              changed.nonce == nonceA &&
                changed.balance == balanceA &&
                changed.storageValue? slotA == some storedA &&
                changed.code?.isNone &&
                updated.nonce? addressB == some otherNonce)
    "nonce replacement must preserve presence, payload, and other accounts"
  assertTrue
    (match world.writeNonce? addressA Core.Word.zero with
      | none => false
      | some updated => updated.account? addressA |>.isSome)
    "writing nonce zero must preserve explicit account presence"

end Tests
