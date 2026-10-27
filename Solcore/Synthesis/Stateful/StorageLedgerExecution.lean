import Solcore.Synthesis.Core.StorageLedger
import Solcore.Synthesis.Stateful.StorageMappingExecution
import Solcore.Synthesis.Stateful.AccountStorage

/-! Execute the original checked sender-keyed ledger over a persistent account
world. Unlike the other storage profiles, each transaction names its own
sender, and original Core invokes it with that caller; the world holds an empty
account for every fixed sender. Each invocation starts a fresh Core heap and
only the public terminal `finalWorld` becomes the next transaction's world.
Observations report exactly the declared slots: the counter and the entry
slots of every transaction's sender and recipient, derived with the separate
`Solcore.Abi.V1.Keccak256`, not with the Core builders the contract runs. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Stateful.StorageLedgerExecution
open Lean Solcore.Core Solcore.ContractRuntime
open Solcore.Synthesis.Core.StorageLedger (CheckedPlan)

def historySchema : String := "solcore-lean.ledger-history.v2"

/-- The deployer and the contract address, exactly as for the storage profiles. -/
abbrev Bindings := StorageExecution.Bindings

/-- Anvil's first three default accounts, in this order; the first deploys. -/
def senders : List Address := [
  ⟨1390849295786071768276380950238675083608645509734, by decide⟩,
  ⟨642829559307850963015472508762062935916233390536, by decide⟩,
  ⟨344073830386746567427978432078835137280280269756, by decide⟩]

structure Transaction where
  id : String
  sender : Address
  flags : Word
  recipient : Word
  amount : Word
  input : Word
  deriving BEq

/-- The selector of `run(uint256,uint256,uint256,uint256)`, followed by the
flags, the recipient, the amount and the input as four big-endian Words. -/
def inputData (flags recipient amount input : Word) : HostStorageDriver.InputData := {
  bytes := ByteArray.mk #[0x15, 0x50, 0x9d, 0x2b] ++ encodeWordBytesBE flags ++ encodeWordBytesBE recipient ++
    encodeWordBytesBE amount ++ encodeWordBytesBE input
  size_lt_wordModulus := by
    simp only [ByteArray.size_append, encodeWordBytesBE_size]
    decide
}

def calldata (flags recipient amount input : Word) : String :=
  encodeBytesText (inputData flags recipient amount input).bytes

/-- The entry slot of a sender: its address as a zero-extended Word, hashed
after the base slot, as the contract's `caller()` key. -/
def senderSlot (sender : Address) : Word :=
  StorageMappingExecution.entrySlot (addressToWord sender)

private def insertSlot (slot : Word) : List Word → List Word
  | [] => [slot]
  | head :: tail =>
      if slot.val < head.val then slot :: head :: tail
      else if slot.val = head.val then head :: tail
      else head :: insertSlot slot tail

/-- The protocol's complete write set: the counter and the entry slots of each
transaction's sender and recipient, in increasing numeric order without
duplicates. -/
def observedSlots (transactions : List Transaction) : List Word :=
  (transactions.flatMap fun tx => [senderSlot tx.sender, StorageMappingExecution.entrySlot tx.recipient]).foldl
    (fun slots slot => insertSlot slot slots)
    [Word.ofNatModulo Solcore.Synthesis.Core.StorageLedger.counterSlot]

/-- The deployer, the contract and an empty account for every fixed sender. -/
def initialWorld (contract : CheckedCoreContract) (bindings : Bindings) : WorldState :=
  senders.foldl (fun world sender =>
      if (world.account? sender).isSome then world else world.putAccount sender Account.empty)
    (StorageExecution.initialWorldForContract contract bindings)

private def worldStorage (world : WorldState) (bindings : Bindings) (slots : List Word) : Json :=
  match world.account? bindings.address with
  | some account => KeyedStorageExecution.storageJson account slots
  | none => Json.null

private def outcomeFields : FrameOutcome Word → List (String × Json)
  | .returned bytes => [("status", toJson "returned"), ("output", toJson (encodeBytesText bytes))]
  | .reverted bytes => [("status", toJson "reverted"), ("output", toJson (encodeBytesText bytes))]
  | .trapped reason => [("status", toJson "trapped"), ("reason", toJson (toString reason.val))]

/-- Independent original-Core observation with each transaction's own caller.
The code registry is resolved again against each current committed world, so
persistence cannot install a different contract or retain one invocation's
local heap. A reverted invocation keeps the prior committed world through the
public runtime, not through this observer. -/
def observeContract (contract : CheckedCoreContract) (transactions : List Transaction)
    (bindings : Bindings) (fuel : Nat) : Json := Id.run do
  let slots := observedSlots transactions
  let registry : CheckedContractRegistry := {
    lookup := fun target => if target = bindings.address then some contract else none }
  let mut world := initialWorld contract bindings
  let initial := worldStorage world bindings slots
  let initialWhole := AccountStorage.contractJson world bindings.address
  let mut rows : Array Json := #[]
  let mut stopped : Option String := none
  for (transaction, index) in transactions.zipIdx do
    if stopped.isNone then
      let prior := world
      let invocation : TopLevelInvocation := {
        target := bindings.address, caller := transaction.sender, callValue := Word.zero,
        inputData := inputData transaction.flags transaction.recipient transaction.amount transaction.input }
      let common := [("id", toJson transaction.id), ("index", toJson index)]
      match registry.resolve? prior bindings.address with
      | none =>
          rows := rows.push (Json.mkObj (common ++ [
            ("status", toJson "resolution-failure"),
            ("committedStorage", worldStorage prior bindings slots),
            ("accountStorage", AccountStorage.contractJson prior bindings.address)]))
          stopped := some transaction.id
      | some ⟨resolved, installed⟩ =>
          match TopLevelExecution.run resolved invocation installed fuel with
          | .completed terminal =>
              world := terminal.finalWorld
              rows := rows.push (Json.mkObj (common ++ outcomeFields terminal.outcome ++ [
                ("committedStorage", worldStorage world bindings slots),
                ("accountStorage", AccountStorage.contractJson world bindings.address)]))
          | .outOfFuel _ _ _ _ _ _ =>
              rows := rows.push (Json.mkObj (common ++ [
                ("status", toJson "out-of-fuel"),
                ("committedStorage", worldStorage prior bindings slots),
                ("accountStorage", AccountStorage.contractJson prior bindings.address)]))
              stopped := some transaction.id
  return Json.mkObj [
    ("schema", toJson historySchema), ("bindings", StorageExecution.bindingsJson bindings),
    ("fuelPerTransaction", toJson fuel), ("observedSlots", KeyedStorageExecution.slotsJson slots),
    ("initialStorage", initial), ("initialAccountStorage", initialWhole), ("transactions", .arr rows),
    ("finalStorage", worldStorage world bindings slots),
    ("finalAccountStorage", AccountStorage.contractJson world bindings.address),
    ("status", toJson (if stopped.isNone then "complete" else "incomplete")),
    ("stoppedAt", stopped.map toJson |>.getD Json.null),
    ("unexecuted", toJson ((transactions.drop rows.size).map (·.id)))]

def observe (plan : CheckedPlan) (transactions : List Transaction)
    (bindings : Bindings) (fuel : Nat) : Json :=
  observeContract plan.contract transactions bindings fuel

end Solcore.Synthesis.Stateful.StorageLedgerExecution
