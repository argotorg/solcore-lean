import Solcore.Synthesis.Core.KeyedStorage
import Solcore.Synthesis.Stateful.StorageExecution
import Solcore.Synthesis.Stateful.AccountStorage

/-! Execute the original checked keyed-storage contract over a persistent
account world. Each invocation starts a fresh Core heap and only the public
terminal `finalWorld` becomes the next transaction's world. Observations report
exactly the declared slots: the counter and every transaction key and wrapping
successor. Each observation also reports the contract's whole committed
storage, enumerated exactly from its account. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Stateful.KeyedStorageExecution
open Lean Solcore.Core Solcore.ContractRuntime
open Solcore.Synthesis.Core.KeyedStorage (CheckedPlan)

def historySchema : String := "solcore-lean.keyed-storage-history.v2"

/-- One caller and one installed contract, exactly as for the two-slot profiles. -/
abbrev Bindings := StorageExecution.Bindings

structure Transaction where
  id : String
  key : Word
  input : Word
  deriving BEq

/-- The selector of `run(uint256,uint256)`, followed by the key and the input
as two big-endian Words. Malformed calldata is outside this profile. -/
def inputData (key input : Word) : HostStorageDriver.InputData := {
  bytes := ByteArray.mk #[0x73, 0x57, 0xf5, 0xd2] ++ encodeWordBytesBE key ++ encodeWordBytesBE input
  size_lt_wordModulus := by
    simp only [ByteArray.size_append, encodeWordBytesBE_size]
    decide
}

def calldata (key input : Word) : String := encodeBytesText (inputData key input).bytes

private def insertSlot (slot : Word) : List Word → List Word
  | [] => [slot]
  | head :: tail =>
      if slot.val < head.val then slot :: head :: tail
      else if slot.val = head.val then head :: tail
      else head :: insertSlot slot tail

/-- The protocol's complete write set: the counter, each key and each key's
wrapping successor, in increasing numeric order without duplicates. -/
def observedSlots (transactions : List Transaction) : List Word :=
  (transactions.flatMap fun tx => [tx.key, tx.key.add (Word.ofNatModulo 1)]).foldl
    (fun slots slot => insertSlot slot slots)
    [Word.ofNatModulo Solcore.Synthesis.Core.KeyedStorage.counterSlot]

def slotsJson (slots : List Word) : Json := toJson (slots.map fun slot => toString slot.val)

def storageJson (account : Account) (slots : List Word) : Json := toJson (slots.map fun slot => Json.mkObj [
  ("slot", toJson (toString slot.val)),
  ("value", toJson (toString (account.storageRead slot).val))])

private def worldStorage (world : WorldState) (bindings : Bindings) (slots : List Word) : Json :=
  match world.account? bindings.address with
  | some account => storageJson account slots
  | none => Json.null

private def outcomeFields : FrameOutcome Word → List (String × Json)
  | .returned bytes => [("status", toJson "returned"), ("output", toJson (encodeBytesText bytes))]
  | .reverted bytes => [("status", toJson "reverted"), ("output", toJson (encodeBytesText bytes))]
  | .trapped reason => [("status", toJson "trapped"), ("reason", toJson (toString reason.val))]

/-- Independent original-Core observation. The code registry is resolved again
against each current committed world, so persistence cannot install a different
contract or retain one invocation's local heap. A reverted invocation keeps the
prior committed world through the public runtime, not through this observer. -/
def observeContract (contract : CheckedCoreContract) (transactions : List Transaction)
    (bindings : Bindings) (fuel : Nat) : Json := Id.run do
  let slots := observedSlots transactions
  let registry : CheckedContractRegistry := {
    lookup := fun target => if target = bindings.address then some contract else none }
  let mut world := StorageExecution.initialWorldForContract contract bindings
  let initial := worldStorage world bindings slots
  let initialWhole := AccountStorage.contractJson world bindings.address
  let mut rows : Array Json := #[]
  let mut stopped : Option String := none
  for (transaction, index) in transactions.zipIdx do
    if stopped.isNone then
      let prior := world
      let invocation : TopLevelInvocation := {
        target := bindings.address, caller := bindings.caller,
        callValue := Word.zero, inputData := inputData transaction.key transaction.input }
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
    ("fuelPerTransaction", toJson fuel), ("observedSlots", slotsJson slots),
    ("initialStorage", initial), ("initialAccountStorage", initialWhole), ("transactions", .arr rows),
    ("finalStorage", worldStorage world bindings slots),
    ("finalAccountStorage", AccountStorage.contractJson world bindings.address),
    ("status", toJson (if stopped.isNone then "complete" else "incomplete")),
    ("stoppedAt", stopped.map toJson |>.getD Json.null),
    ("unexecuted", toJson ((transactions.drop rows.size).map (·.id)))]

def observe (plan : CheckedPlan) (transactions : List Transaction)
    (bindings : Bindings) (fuel : Nat) : Json :=
  observeContract plan.contract transactions bindings fuel

end Solcore.Synthesis.Stateful.KeyedStorageExecution
