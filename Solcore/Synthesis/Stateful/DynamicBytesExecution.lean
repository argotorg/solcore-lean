import Solcore.Synthesis.Core.DynamicBytes
import Solcore.Synthesis.Stateful.StorageExecution
import Solcore.Synthesis.Stateful.AccountStorage

/-! Execute the original checked bytes contract over a persistent account
world. Each invocation starts a fresh Core heap and only the public terminal
`finalWorld` becomes the next transaction's world. Calldata is the canonical
ABI encoding of `(flags, payload)`: the static head, the tail offset 64, the
length, the payload bytes and zero padding to a whole Word. Observations report
the five declared slots and the contract's whole committed storage. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Stateful.DynamicBytesExecution
open Lean Solcore.Core Solcore.ContractRuntime
open Solcore.Synthesis.Core.DynamicBytes (CheckedPlan)

def historySchema : String := "solcore-lean.bytes-history.v2"

/-- One caller and one installed contract, exactly as for the storage profiles. -/
abbrev Bindings := StorageExecution.Bindings

structure Transaction where
  id : String
  flags : Word
  payload : List UInt8
  deriving BEq

/-- Payload bytes padded with zeros to a whole number of Words. -/
def paddedLength (length : Nat) : Nat := (length + 31) / 32 * 32

/-- The selector of `run(uint256,bytes)`, the flags Word, the tail offset 64
relative to the arguments, the length, the payload and its zero padding. -/
def inputBytes (flags : Word) (payload : List UInt8) : ByteArray :=
  ByteArray.mk #[0x22, 0x0e, 0xb9, 0xb6] ++ encodeWordBytesBE flags ++
    encodeWordBytesBE (Word.ofNatModulo 64) ++ encodeWordBytesBE (Word.ofNatModulo payload.length) ++
    ByteArray.mk (payload ++ List.replicate (paddedLength payload.length - payload.length) 0).toArray

/-- Bounded cases are far below the Word-sized calldata limit; the check keeps
the runtime input total without assuming the case boundary. -/
def inputData? (flags : Word) (payload : List UInt8) : Option HostStorageDriver.InputData :=
  let bytes := inputBytes flags payload
  if bounded : bytes.size < wordModulus then some ⟨bytes, bounded⟩ else none

def calldata (flags : Word) (payload : List UInt8) : String := encodeBytesText (inputBytes flags payload)

/-- Slot zero holds the accumulator, slots one and two the per-chunk results,
slot three the running byte count and slot four the last payload byte. -/
def observedSlots : List Word := (List.range 5).map Word.ofNatModulo

def slotsJson : Json := toJson (observedSlots.map fun slot => toString slot.val)

def storageJson (account : Account) : Json := toJson (observedSlots.map fun slot => Json.mkObj [
  ("slot", toJson (toString slot.val)),
  ("value", toJson (toString (account.storageRead slot).val))])

private def worldStorage (world : WorldState) (bindings : Bindings) : Json :=
  match world.account? bindings.address with
  | some account => storageJson account
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
  let registry : CheckedContractRegistry := {
    lookup := fun target => if target = bindings.address then some contract else none }
  let mut world := StorageExecution.initialWorldForContract contract bindings
  let initial := worldStorage world bindings
  let initialWhole := AccountStorage.contractJson world bindings.address
  let mut rows : Array Json := #[]
  let mut stopped : Option String := none
  for (transaction, index) in transactions.zipIdx do
    if stopped.isNone then
      let prior := world
      let common := [("id", toJson transaction.id), ("index", toJson index)]
      match inputData? transaction.flags transaction.payload, registry.resolve? prior bindings.address with
      | none, _ =>
          rows := rows.push (Json.mkObj (common ++ [
            ("status", toJson "input-limit"), ("committedStorage", worldStorage prior bindings),
            ("accountStorage", AccountStorage.contractJson prior bindings.address)]))
          stopped := some transaction.id
      | _, none =>
          rows := rows.push (Json.mkObj (common ++ [
            ("status", toJson "resolution-failure"), ("committedStorage", worldStorage prior bindings),
            ("accountStorage", AccountStorage.contractJson prior bindings.address)]))
          stopped := some transaction.id
      | some input, some ⟨resolved, installed⟩ =>
          let invocation : TopLevelInvocation := {
            target := bindings.address, caller := bindings.caller,
            callValue := Word.zero, inputData := input }
          match TopLevelExecution.run resolved invocation installed fuel with
          | .completed terminal =>
              world := terminal.finalWorld
              rows := rows.push (Json.mkObj (common ++ outcomeFields terminal.outcome ++ [
                ("committedStorage", worldStorage world bindings),
                ("accountStorage", AccountStorage.contractJson world bindings.address)]))
          | .outOfFuel _ _ _ _ _ _ =>
              rows := rows.push (Json.mkObj (common ++ [
                ("status", toJson "out-of-fuel"), ("committedStorage", worldStorage prior bindings),
                ("accountStorage", AccountStorage.contractJson prior bindings.address)]))
              stopped := some transaction.id
  return Json.mkObj [
    ("schema", toJson historySchema), ("bindings", StorageExecution.bindingsJson bindings),
    ("fuelPerTransaction", toJson fuel), ("observedSlots", slotsJson),
    ("initialStorage", initial), ("initialAccountStorage", initialWhole), ("transactions", .arr rows),
    ("finalStorage", worldStorage world bindings),
    ("finalAccountStorage", AccountStorage.contractJson world bindings.address),
    ("status", toJson (if stopped.isNone then "complete" else "incomplete")),
    ("stoppedAt", stopped.map toJson |>.getD Json.null),
    ("unexecuted", toJson ((transactions.drop rows.size).map (·.id)))]

def observe (plan : CheckedPlan) (transactions : List Transaction)
    (bindings : Bindings) (fuel : Nat) : Json :=
  observeContract plan.contract transactions bindings fuel

end Solcore.Synthesis.Stateful.DynamicBytesExecution
