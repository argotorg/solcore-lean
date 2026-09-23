import Solcore.ContractRuntime.WorldStateCodeWriteProperties
import Solcore.Test.TopLevelExecutionFixture

/-! External and executable checks for checked-code replacement. -/

set_option autoImplicit false

namespace Tests

open Solcore
open Solcore.ContractRuntime
open TopLevelExecutionFixture

example := WorldState.writeCode?_of_absent
example := WorldState.writeCode?_of_present
example := WorldState.account?_writeCode?_same
example := WorldState.code?_writeCode?_same
example := WorldState.account?_writeCode?_other
example := WorldState.writeCode?_preserves_payload

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do
    throw (IO.userError message)

private def word
    (value : Nat)
    (inBounds : value < Core.wordModulus := by decide) : Core.Word :=
  ⟨value, inBounds⟩

private def target : Address := ⟨0x148, by decide⟩
private def other : Address := ⟨0x149, by decide⟩
private def slot : Core.Word := word 3
private def stored : Core.Word := word 9

private def targetAccount : Account :=
  Account.empty
    |>.withNonce (word 7)
    |>.withBalance (word 11)
    |>.storageWrite slot stored

private def initialWorld : WorldState :=
  WorldState.empty
    |>.putAccount target targetAccount
    |>.putAccount other Account.empty

def testWorldStateCodeWrite : IO Unit := do
  assertTrue (WorldState.empty.writeCode? target contract.code).isNone
    "checked-code replacement must not create an absent Account"
  let updated ←
    match initialWorld.writeCode? target contract.code with
    | none => throw (IO.userError "present Account rejected code replacement")
    | some updated => pure updated
  let account ←
    match updated.account? target with
    | none => throw (IO.userError "code replacement removed its Account")
    | some account => pure account
  assertTrue
    (account.code?.map (fun code => code.program) == some contract.code.program)
    "code replacement did not install the requested checked program"
  assertTrue
    (account.balance == word 11 && account.nonce == word 7 &&
      account.storageValue? slot == some stored)
    "code replacement changed balance, nonce, or storage"
  assertTrue ((updated.account? other).isSome)
    "code replacement changed an unrelated Account"

end Tests
