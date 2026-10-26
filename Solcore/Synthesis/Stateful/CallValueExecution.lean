import Solcore.Synthesis.Core.CallValue
import Solcore.Synthesis.Stateful.KeyedStorageExecution
import Solcore.ContractRuntime.BalancedTopLevelExecution

/-! Execute the original checked call-value contract over a persistent account
world with the public balanced runtime. Each invocation transfers its value from
the caller to the contract before the root runs, starts a fresh Core heap and
journal, and only the terminal `finalWorld` becomes the next transaction's
world. A revert or trap selects the pre-transfer checkpoint, so the value is
refunded by `ContractRuntime`, not by this observer. Observations report slots
zero and one and the contract's committed balance; the caller's balance is
never reported. A rejected transfer is reported as such, never as a revert. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Stateful.CallValueExecution
open Lean Solcore.Core Solcore.ContractRuntime
open Solcore.Synthesis.Core.CallValue (CheckedPlan)

def historySchema : String := "solcore-lean.call-value-history.v1"

/-- One caller and one installed contract, as for the storage profiles. -/
abbrev Bindings := StorageExecution.Bindings

structure Transaction where
  id : String
  flags : Word
  input : Word
  value : Word
  deriving BEq

/-- The caller's funds in the declared post-deployment world. -/
def callerFunds : Nat := 2 ^ 80

/-- The selector of `run(uint256,uint256)`, followed by the flags and the input
as two big-endian Words. The value travels with the invocation, not the data. -/
def inputData (flags input : Word) : HostStorageDriver.InputData := {
  bytes := ByteArray.mk #[0x73, 0x57, 0xf5, 0xd2] ++ encodeWordBytesBE flags ++ encodeWordBytesBE input
  size_lt_wordModulus := by
    simp only [ByteArray.size_append, encodeWordBytesBE_size]
    decide
}

def calldata (flags input : Word) : String := encodeBytesText (inputData flags input).bytes

/-- Slot zero holds the step result and slot one the accepted value. -/
def observedSlots : List Word := [Word.ofNatModulo 0, Word.ofNatModulo 1]

/-- The world after an empty payable constructor received `deploymentValue`. -/
def initialWorldForContract (contract : CheckedCoreContract) (deploymentValue : Word)
    (bindings : Bindings) : WorldState :=
  (WorldState.empty.putAccount bindings.caller (Account.empty.withBalance (Word.ofNatModulo callerFunds))).putAccount
    bindings.address ((Account.empty.withCode contract.code).withBalance deploymentValue)

private def worldStorage (world : WorldState) (bindings : Bindings) : Json :=
  match world.account? bindings.address with
  | some account => KeyedStorageExecution.storageJson account observedSlots
  | none => Json.null

private def worldBalance (world : WorldState) (bindings : Bindings) : Json :=
  match world.account? bindings.address with
  | some account => toJson (toString account.balance.val)
  | none => Json.null

private def committed (world : WorldState) (bindings : Bindings) : List (String × Json) :=
  [("committedStorage", worldStorage world bindings), ("committedBalance", worldBalance world bindings)]

private def outcomeFields : FrameOutcome Word → List (String × Json)
  | .returned bytes => [("status", toJson "returned"), ("output", toJson (encodeBytesText bytes))]
  | .reverted bytes => [("status", toJson "reverted"), ("output", toJson (encodeBytesText bytes))]
  | .trapped reason => [("status", toJson "trapped"), ("reason", toJson (toString reason.val))]

/-- Independent original-Core observation. The code registry is resolved again
against each current committed world, so persistence cannot install a different
contract or retain one invocation's local heap. -/
def observeContract (contract : CheckedCoreContract) (deploymentValue : Word)
    (transactions : List Transaction) (bindings : Bindings) (fuel : Nat) : Json := Id.run do
  let registry : CheckedContractRegistry := {
    lookup := fun target => if target = bindings.address then some contract else none }
  let mut world := initialWorldForContract contract deploymentValue bindings
  let initial := world
  let mut rows : Array Json := #[]
  let mut stopped : Option String := none
  for (transaction, index) in transactions.zipIdx do
    if stopped.isNone then
      let prior := world
      let invocation : TopLevelInvocation := {
        target := bindings.address, caller := bindings.caller,
        callValue := transaction.value, inputData := inputData transaction.flags transaction.input }
      let common := [("id", toJson transaction.id), ("index", toJson index)]
      match registry.resolve? prior bindings.address with
      | none =>
          rows := rows.push (Json.mkObj (common ++ [("status", toJson "resolution-failure")] ++ committed prior bindings))
          stopped := some transaction.id
      | some ⟨resolved, installed⟩ =>
          match (BalancedTopLevelExecution.run resolved invocation installed registry fuel).view with
          | .rejected rejected =>
              rows := rows.push (Json.mkObj (common ++ [("status", toJson "transfer-rejected"),
                ("detail", toJson (reprStr rejected.failure))] ++ committed prior bindings))
              stopped := some transaction.id
          | .execution execution =>
              match execution.view with
              | .completed terminal =>
                  world := terminal.finalWorld
                  rows := rows.push (Json.mkObj (common ++ outcomeFields terminal.outcome ++ committed world bindings))
                  match terminal.outcome with
                  | .trapped _ => stopped := some transaction.id
                  | _ => pure ()
              | .outOfFuel _ _ _ =>
                  rows := rows.push (Json.mkObj (common ++ [("status", toJson "out-of-fuel")] ++ committed prior bindings))
                  stopped := some transaction.id
  return Json.mkObj [
    ("schema", toJson historySchema), ("bindings", StorageExecution.bindingsJson bindings),
    ("fuelPerTransaction", toJson fuel), ("observedSlots", KeyedStorageExecution.slotsJson observedSlots),
    ("deploymentValue", toJson (toString deploymentValue.val)),
    ("initialStorage", worldStorage initial bindings), ("initialBalance", worldBalance initial bindings),
    ("initialLogs", toJson ([] : List Json)), ("transactions", .arr rows),
    ("finalStorage", worldStorage world bindings), ("finalBalance", worldBalance world bindings),
    ("status", toJson (if stopped.isNone then "complete" else "incomplete")),
    ("stoppedAt", stopped.map toJson |>.getD Json.null),
    ("unexecuted", toJson ((transactions.drop rows.size).map (·.id)))]

def observe (plan : CheckedPlan) (transactions : List Transaction)
    (bindings : Bindings) (fuel : Nat) : Json :=
  observeContract plan.contract plan.deploymentValue transactions bindings fuel

end Solcore.Synthesis.Stateful.CallValueExecution
