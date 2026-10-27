import Solcore.Synthesis.Core.ForwardedCall
import Solcore.Synthesis.Stateful.NestedCallExecution
import Solcore.ContractRuntime.BalancedTopLevelExecution

/-! Original checked-Core execution of the fixed value-forwarding parent/child
protocol. Each transaction transfers its call value from the caller to the
parent through the public balanced runtime before the root runs, and the nested
scheduler transfers the forwarded amount at the child call boundary. Only the
terminal committed world and journal leave an invocation: a child revert keeps
its amount with the parent, and a root revert or trap selects the pre-transfer
checkpoint. Neither refund is performed by this observer, and the caller's
balance is never reported. A rejected top-level transfer is reported as such,
never as a revert. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Stateful.ForwardedCallExecution
open Lean Solcore.Core Solcore.ContractRuntime
open Solcore.Synthesis.Core.ForwardedCall (CheckedPlan)

def historySchema : String := "solcore-lean.forward-history.v2"

/-- One caller, the parent and the child, as for the parent/child call profile. -/
abbrev Bindings := NestedCallExecution.Bindings

structure Transaction where
  id : String
  input : Word
  value : Word
  amount : Word
  deriving BEq

/-- The caller's funds and the parent's endowment in the declared
post-deployment world; the child holds nothing. -/
def callerFunds : Nat := 2 ^ 80
def parentEndowment : Nat := 2 ^ 72

/-- The selector of `run(uint256,uint256,uint256)`, the actual child address,
the input and the forwarded amount. The call value travels with the
invocation, not the data. -/
def inputData (bindings : Bindings) (input amount : Word) : HostStorageDriver.InputData := {
  bytes := ByteArray.mk #[0x24, 0xb9, 0x12, 0xe5] ++
    encodeWordBytesBE (addressToWord bindings.child) ++ encodeWordBytesBE input ++ encodeWordBytesBE amount
  size_lt_wordModulus := by
    simp only [ByteArray.size_append, encodeWordBytesBE_size]
    decide
}

def calldata (bindings : Bindings) (input amount : Word) : String :=
  encodeBytesText (inputData bindings input amount).bytes

def initialWorld (plan : CheckedPlan) (bindings : Bindings) : WorldState :=
  WorldState.empty
    |>.putAccount bindings.caller (Account.empty.withBalance (Word.ofNatModulo callerFunds))
    |>.putAccount bindings.parent
      ((Account.empty.withCode plan.parentContract.code).withBalance (Word.ofNatModulo parentEndowment))
    |>.putAccount bindings.child (Account.empty.withCode plan.childContract.code)

private def outcomeFields : FrameOutcome Word → List (String × Json)
  | .returned bytes => [("status", toJson "returned"), ("output", toJson (encodeBytesText bytes))]
  | .reverted bytes => [("status", toJson "reverted"), ("output", toJson (encodeBytesText bytes))]
  | .trapped reason => [("status", toJson "trapped"), ("reason", toJson (toString reason.val))]

/-- Each transaction resolves the root against the current committed world; the
scheduler resolves the child at its actual call boundary. Local heaps and
transaction journals start fresh, while the selected world persists. -/
def observe (plan : CheckedPlan) (transactions : List Transaction) (bindings : Bindings) (fuel : Nat) : Json := Id.run do
  let registry : CheckedContractRegistry := {
    lookup := fun target => if target = bindings.parent then some plan.parentContract
      else if target = bindings.child then some plan.childContract else none }
  let mut world := initialWorld plan bindings
  let initial := NestedCallExecution.accountsJson world bindings
  let initialWhole := NestedCallExecution.wholeStorageJson world bindings
  let mut rows : Array Json := #[]
  let mut stopped : Option String := none
  for (transaction, index) in transactions.zipIdx do
    if stopped.isNone then
      let prior := world
      let invocation : TopLevelInvocation := {
        target := bindings.parent, caller := bindings.caller, callValue := transaction.value,
        inputData := inputData bindings transaction.input transaction.amount }
      let common := [("id", toJson transaction.id), ("index", toJson index)]
      let unknown := [("committedAccounts", NestedCallExecution.accountsJson prior bindings),
        ("accountStorage", NestedCallExecution.wholeStorageJson prior bindings), ("logs", Json.null)]
      match registry.resolve? prior bindings.parent with
      | none =>
          rows := rows.push (Json.mkObj (common ++ [("status", toJson "resolution-failure")] ++ unknown))
          stopped := some transaction.id
      | some ⟨resolved, installed⟩ =>
          match (BalancedTopLevelExecution.run resolved invocation installed registry fuel).view with
          | .rejected rejected =>
              rows := rows.push (Json.mkObj (common ++ [("status", toJson "transfer-rejected"),
                ("detail", toJson (reprStr rejected.failure))] ++ unknown))
              stopped := some transaction.id
          | .execution execution =>
              match execution.view with
              | .completed terminal =>
                  world := terminal.finalWorld
                  rows := rows.push (Json.mkObj (common ++ outcomeFields terminal.outcome ++ [
                    ("committedAccounts", NestedCallExecution.accountsJson world bindings),
                    ("accountStorage", NestedCallExecution.wholeStorageJson world bindings),
                    ("logs", NestedCallExecution.logsJson terminal.committedJournal)]))
                  match terminal.outcome with
                  | .trapped _ => stopped := some transaction.id
                  | _ => pure ()
              | .outOfFuel _ _ _ =>
                  rows := rows.push (Json.mkObj (common ++ [("status", toJson "out-of-fuel")] ++ unknown))
                  stopped := some transaction.id
  return Json.mkObj [("schema", toJson historySchema), ("bindings", NestedCallExecution.bindingsJson bindings),
    ("fuelPerTransaction", toJson fuel), ("initialAccounts", initial), ("initialAccountStorage", initialWhole),
    ("transactions", .arr rows), ("finalAccounts", NestedCallExecution.accountsJson world bindings),
    ("finalAccountStorage", NestedCallExecution.wholeStorageJson world bindings),
    ("status", toJson (if stopped.isNone then "complete" else "incomplete")),
    ("stoppedAt", stopped.map toJson |>.getD Json.null),
    ("unexecuted", toJson ((transactions.drop rows.size).map (·.id)))]

end Solcore.Synthesis.Stateful.ForwardedCallExecution
