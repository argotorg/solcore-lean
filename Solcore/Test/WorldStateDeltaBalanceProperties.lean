import Solcore.ContractRuntime.BalanceTransfer
import Solcore.ContractRuntime.WorldStateDeltaProperties

/-! External consumers and runtime checks for balance delta observations. -/

set_option autoImplicit false

namespace Tests

open Solcore
open Solcore.ContractRuntime

example := WorldStateDelta.balanceEndpoints_exact
example := WorldStateDelta.balanceEndpoints_identity
example := WorldStateDelta.balanceChange?_identity
example {initialWorld finalWorld : WorldState}
    (delta : WorldStateDelta initialWorld finalWorld)
    (address : Address) :
    delta.balanceChange? address = none ↔
      (delta.balanceEndpoints address).1 =
        (delta.balanceEndpoints address).2 :=
  WorldStateDelta.balanceChange?_eq_none_iff delta address

example {initialWorld finalWorld : WorldState}
    (delta : WorldStateDelta initialWorld finalWorld)
    (address : Address)
    (before after : Option Core.Word) :
    delta.balanceChange? address = some (before, after) ↔
      (delta.balanceEndpoints address).1 = before ∧
      (delta.balanceEndpoints address).2 = after ∧
      before ≠ after :=
  WorldStateDelta.balanceChange?_eq_some_iff delta address before after

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do
    throw (IO.userError message)

private def sender : Address := ⟨0, by decide⟩
private def recipient : Address := ⟨1, by decide⟩
private def untouched : Address := ⟨2, by decide⟩

private def word
    (value : Nat)
    (inBounds : value < Core.wordModulus := by decide) : Core.Word :=
  ⟨value, inBounds⟩

private def initialWorld : WorldState :=
  (WorldState.empty.putAccount sender
      (Account.empty.withBalance (word 10))).putAccount recipient
    (Account.empty.withBalance (word 3))

def testWorldStateDeltaBalance : IO Unit := do
  let next ←
    match initialWorld.transferBalance sender recipient (word 4) with
    | .ok next => pure next
    | .error _ => throw (IO.userError "balance delta fixture transfer failed")
  let delta : WorldStateDelta initialWorld next := .exact
  assertTrue
    (delta.balanceEndpoints sender ==
      (some (word 10), some (word 6)))
    "balance delta must expose the exact sender debit"
  assertTrue
    (delta.balanceChange? sender ==
      some (some (word 10), some (word 6)))
    "balance change must report a changed sender endpoint"
  assertTrue
    (delta.balanceEndpoints recipient ==
      (some (word 3), some (word 7)))
    "balance delta must expose the exact recipient credit"
  assertTrue
    (delta.balanceChange? untouched == none)
    "balance change must omit an untouched absent account"
  assertTrue
    ((WorldStateDelta.identity initialWorld).balanceChange? sender == none)
    "identity delta must not report a balance change"

end Tests
