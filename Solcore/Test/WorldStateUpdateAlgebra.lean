import Solcore.ContractRuntime.WorldState

/-! Compile-time and executable regressions for WorldState update algebra. -/

set_option autoImplicit false

namespace Tests

open Solcore
open Solcore.ContractRuntime

private theorem compileTimeExtRegression_account
    {left right : Account}
    (sameStorage : ∀ slot,
      left.storageValue? slot = right.storageValue? slot)
    (sameCode : left.code? = right.code?)
    (sameBalance : left.balance = right.balance)
    (sameNonce : left.nonce = right.nonce) :
    left = right :=
  Account.ext sameStorage sameCode sameBalance sameNonce

private theorem compileTimeExtRegression_worldState
    {left right : WorldState}
    (same : ∀ address, left.account? address = right.account? address) :
    left = right :=
  WorldState.ext same

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do
    throw (IO.userError message)

private def addressA : Address := ⟨0, by decide⟩
private def addressB : Address := ⟨1, by decide⟩
private def slotA : Core.Word := ⟨0x11, by decide⟩
private def slotB : Core.Word := ⟨0x22, by decide⟩
private def valueA : Core.Word := ⟨0xaa, by decide⟩
private def valueB : Core.Word := ⟨0xbb, by decide⟩

private def accountA : Account :=
  Account.empty.storageWrite slotA valueA

private def accountB : Account :=
  Account.empty.storageWrite slotB valueB

private def worldValue?
    (state : WorldState) (address : Address) (slot : Core.Word) :
    Option Core.Word := do
  let account ← state.account? address
  account.storageValue? slot

def testWorldStateUpdateAlgebra : IO Unit := do
  let overwrittenAccount := accountA.storageWrite slotA valueB
  assertTrue (overwrittenAccount.storageValue? slotA == some valueB)
    "the last Account write to one slot must replace the earlier value"
  let accountLeftFirst := accountA.storageWrite slotB valueB
  let accountRightFirst := accountB.storageWrite slotA valueA
  assertTrue
    (accountLeftFirst.storageValue? slotA == some valueA &&
      accountLeftFirst.storageValue? slotB == some valueB &&
      accountRightFirst.storageValue? slotA == some valueA &&
      accountRightFirst.storageValue? slotB == some valueB)
    "Account writes to distinct slots must commute under public lookup"
  let overwrittenWorld :=
    (WorldState.empty.putAccount addressA accountA).putAccount addressA accountB
  assertTrue
    (worldValue? overwrittenWorld addressA slotA == none &&
      worldValue? overwrittenWorld addressA slotB == some valueB)
    "the last WorldState put at one address must replace the earlier Account"
  let worldLeftFirst :=
    (WorldState.empty.putAccount addressA accountA).putAccount addressB accountB
  let worldRightFirst :=
    (WorldState.empty.putAccount addressB accountB).putAccount addressA accountA
  assertTrue
    (worldValue? worldLeftFirst addressA slotA == some valueA &&
      worldValue? worldLeftFirst addressB slotB == some valueB &&
      worldValue? worldRightFirst addressA slotA == some valueA &&
      worldValue? worldRightFirst addressB slotB == some valueB)
    "WorldState puts at distinct addresses must commute under public lookup"

end Tests
