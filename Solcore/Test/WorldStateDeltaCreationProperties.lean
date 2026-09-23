import Solcore.ContractRuntime.WorldStateDeltaProperties
import Solcore.Test.TopLevelExecutionFixture

/-! External consumers and executable creation-delta checks. -/

set_option autoImplicit false

namespace Tests

open Solcore
open Solcore.ContractRuntime
open TopLevelExecutionFixture

example := WorldStateDelta.nonceEndpoints_exact
example := WorldStateDelta.codeEndpoints_exact
example := WorldStateDelta.createdAccount?_exact
example := WorldStateDelta.nonceEndpoints_identity
example := WorldStateDelta.codeEndpoints_identity
example := WorldStateDelta.createdAccount?_identity
example := WorldStateDelta.nonceChange?_identity

example {initialWorld finalWorld : WorldState}
    (delta : WorldStateDelta initialWorld finalWorld)
    (address : Address) :
    delta.nonceChange? address = none ↔
      (delta.nonceEndpoints address).1 =
        (delta.nonceEndpoints address).2 :=
  WorldStateDelta.nonceChange?_eq_none_iff delta address

example {initialWorld finalWorld : WorldState}
    (delta : WorldStateDelta initialWorld finalWorld)
    (address : Address)
    (before after : Option Core.Word) :
    delta.nonceChange? address = some (before, after) ↔
      (delta.nonceEndpoints address).1 = before ∧
      (delta.nonceEndpoints address).2 = after ∧
      before ≠ after :=
  WorldStateDelta.nonceChange?_eq_some_iff delta address before after

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do
    throw (IO.userError message)

private def word
    (value : Nat)
    (inBounds : value < Core.wordModulus := by decide) : Core.Word :=
  ⟨value, inBounds⟩

private def creator : Address := ⟨0x148, by decide⟩
private def created : Address := ⟨0x149, by decide⟩
private def untouched : Address := ⟨0x14a, by decide⟩
private def slot : Core.Word := word 9
private def stored : Core.Word := word 77

private def creatorAccount : Account :=
  Account.empty.withNonce (word 4) |>.withBalance (word 10)

private def initialWorld : WorldState :=
  WorldState.empty.putAccount creator creatorAccount

private def finalWorld : WorldState :=
  initialWorld
    |>.putAccount creator (creatorAccount.withNonce (word 5))
    |>.putAccount created
      (Account.empty.withCode contract.code |>.storageWrite slot stored
        |>.withBalance (word 3))

private def delta : WorldStateDelta initialWorld finalWorld := .exact

private def createdCodeProgramExact : Bool :=
  match (delta.codeEndpoints created).1, (delta.codeEndpoints created).2 with
  | none, some installed => installed.program == contract.code.program
  | _, _ => false

def testWorldStateDeltaCreation : IO Unit := do
  assertTrue
    (delta.nonceEndpoints creator == (some (word 4), some (word 5)))
    "creation delta must expose the consumed creator nonce"
  assertTrue
    (delta.nonceChange? creator ==
      some (some (word 4), some (word 5)))
    "creation delta must report the exact nonce change"
  assertTrue (delta.createdAccount? created)
    "creation delta must distinguish absent-to-present account creation"
  assertTrue (!delta.createdAccount? creator)
    "updating a present creator must not be reported as account creation"
  assertTrue (!delta.createdAccount? untouched)
    "an untouched absent address must not be reported as created"
  assertTrue createdCodeProgramExact
    "creation delta must expose the installed checked runtime program"
  assertTrue
    (delta.balanceEndpoints created == (none, some (word 3)) &&
      delta.storageEndpoints created slot == (none, some stored))
    "existing delta queries must compose with created-account observations"
  let identity := WorldStateDelta.identity initialWorld
  assertTrue
    (identity.nonceChange? creator == none &&
      !identity.createdAccount? creator)
    "identity delta must report neither nonce change nor account creation"

end Tests
