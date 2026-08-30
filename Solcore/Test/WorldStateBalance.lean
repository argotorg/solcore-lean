import Solcore.Semantics.WorldStateBalanceProperties

/-! Compile-time and executable regressions for account balances. -/

set_option autoImplicit false

namespace Tests

open Solcore
open Solcore.Semantics

example : Account.empty.balance = Core.Word.zero :=
  Account.balance_empty

example (account : Account) (balance : Core.Word) :
    (account.withBalance balance).balance = balance :=
  Account.balance_withBalance account balance

example (account : Account) (balance slot : Core.Word) :
    (account.withBalance balance).storageValue? slot =
      account.storageValue? slot :=
  Account.storageValue?_withBalance account balance slot

example (account : Account) (balance : Core.Word) :
    (account.withBalance balance).code? = account.code? :=
  Account.code?_withBalance account balance

example (account : Account) (code : CheckedHostCoreProgram) :
    (account.withCode code).balance = account.balance :=
  Account.balance_withCode account code

example (account : Account) (slot value : Core.Word) :
    (account.storageWrite slot value).balance = account.balance :=
  Account.balance_storageWrite account slot value

example (address : Address) :
    WorldState.empty.balance? address = none :=
  WorldState.balance?_empty address

example (state : WorldState) (address : Address) (account : Account) :
    (state.putAccount address account).balance? address =
      some account.balance :=
  WorldState.balance?_putAccount_same state address account

example (state : WorldState) (address other : Address) (account : Account)
    (different : other ≠ address) :
    (state.putAccount address account).balance? other =
      state.balance? other :=
  WorldState.balance?_putAccount_other state address other account different

example (state : WorldState) (address : Address) (balance : Core.Word)
    (absent : state.account? address = none) :
    state.writeBalance? address balance = none :=
  WorldState.writeBalance?_of_absent state address balance absent

example (state : WorldState) (address : Address) (account : Account)
    (balance : Core.Word) (present : state.account? address = some account) :
    state.writeBalance? address balance =
      some (state.putAccount address (account.withBalance balance)) :=
  WorldState.writeBalance?_of_present state address account balance present

example (state : WorldState) (address : Address) (account : Account)
    (balance : Core.Word) (present : state.account? address = some account) :
    (state.writeBalance? address balance).bind
        (fun next => next.balance? address) = some balance :=
  WorldState.balance?_writeBalance?_same state address account balance present

example (state : WorldState) (address other : Address) (account : Account)
    (balance : Core.Word) (present : state.account? address = some account)
    (different : other ≠ address) :
    (state.writeBalance? address balance).bind
        (fun next => next.account? other) = state.account? other :=
  WorldState.account?_writeBalance?_other state address other account balance
    present different

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do
    throw (IO.userError message)

private def addressA : Address := ⟨0, by decide⟩
private def addressB : Address := ⟨1, by decide⟩
private def balanceA : Core.Word := ⟨17, by decide⟩

def testWorldStateBalance : IO Unit := do
  assertTrue (WorldState.empty.balance? addressA == none)
    "an absent account must not be reported as a zero-balance account"
  let present :=
    WorldState.empty.putAccount addressA
      (Account.empty.withBalance balanceA)
  assertTrue (present.balance? addressA == some balanceA)
    "a present account must expose its exact balance"
  assertTrue (present.writeBalance? addressB balanceA).isNone
    "writing balance must not create an absent account"
  assertTrue
    (match present.writeBalance? addressA Core.Word.zero with
      | some updated =>
          updated.balance? addressA == some Core.Word.zero &&
            (updated.account? addressB).isNone
      | none => false)
    "balance replacement must preserve presence and unrelated addresses"

end Tests
