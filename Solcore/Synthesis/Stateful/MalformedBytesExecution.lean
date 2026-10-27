import Solcore.Synthesis.Core.MalformedBytes
import Solcore.Synthesis.Stateful.StdCalldata
import Solcore.Synthesis.Stateful.StorageExecution
import Solcore.Synthesis.Stateful.LongBytesExecution
import Solcore.Synthesis.Stateful.AccountStorage

/-! Execute the original checked malformed-bytes contract over a persistent
account world. A transaction is a canonical `(flags, payload)` call of
`run(uint256,bytes)`, with a payload of at most 256 bytes, together with one
malformation of its calldata; the contract receives the malformed bytes.
`stdDecode` is a second model of the pinned std's dispatcher and `bytes`
decoder, written over the bytes instead of in Core, which prescribes each
transaction's outcome and the payload the body reads. Observations report
slots zero to ten and the contract's whole committed storage. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Stateful.MalformedBytesExecution
open Lean Solcore.Core Solcore.ContractRuntime
open Solcore.Synthesis.Core.MalformedBytes (CheckedPlan)

def historySchema : String := "solcore-lean.malformed-bytes-history.v1"

/-- One caller and one installed contract, exactly as for the storage profiles. -/
abbrev Bindings := StorageExecution.Bindings

/-- How a transaction's calldata departs from the canonical encoding of its
flags and payload: the malformed-calldata kinds, with `length` replacing the
payload length Word, or nonzero padding after a payload that does not fill its
last Word. Padding patterns are `0xff` (0), the ramp `1, 2, 3, ...` (1) or a
single `0x01` in the last padding byte (2). -/
inductive Malformation where
  | none
  | short (bytes : Nat)
  | selector (mask : Nat)
  | truncate (kept : Nat)
  | trailing (count pattern : Nat)
  | offset (value : Word)
  | length (value : Word)
  | padding (pattern : Nat)
  deriving BEq, Repr

structure Transaction where
  id : String
  flags : Word
  payload : List UInt8
  malformation : Malformation
  deriving BEq

def canonicalBytes (tx : Transaction) : ByteArray :=
  DynamicBytesExecution.inputBytes tx.flags tx.payload

/-- The payload starts after the selector, the flags, the tail offset 64 and
the length Word. -/
def payloadStart : Nat := 100

/-- The padding bytes after a payload of `length` bytes. -/
def paddingCount (length : Nat) : Nat := DynamicBytesExecution.paddedLength length - length

/-- The last payload Word with its padding replaced by the pattern. -/
private def paddedWord (payload : List UInt8) (pattern : Nat) : Word :=
  let start := payload.length / 32 * 32
  let count := paddingCount payload.length
  let padding := (List.range count).map fun position =>
    match pattern with
    | 0 => (0xff : UInt8)
    | 1 => (position + 1).toUInt8
    | _ => if position + 1 = count then 1 else 0
  Word.ofNatModulo ((payload.drop start ++ padding).foldl (fun total byte => total * 256 + byte.toNat) 0)

def Malformation.change (payload : List UInt8) : Malformation → StdCalldata.Change
  | .none => .none
  | .short bytes => .short bytes
  | .selector mask => .selector mask
  | .truncate kept => .truncate kept
  | .trailing count pattern => .trailing count pattern
  | .offset value => .word 36 value
  | .length value => .word 68 value
  | .padding pattern => .word (payloadStart + payload.length / 32 * 32) (paddedWord payload pattern)

/-- The calldata a transaction sends. -/
def inputBytes (tx : Transaction) : ByteArray :=
  (tx.malformation.change tx.payload).apply (canonicalBytes tx)

/-- A malformation within its bounds; padding needs a payload that does not
fill its last Word, and one of the three patterns. -/
def Malformation.valid (malformation : Malformation) (payload : List UInt8) (canonicalSize : Nat) : Bool :=
  (match malformation with
    | .padding pattern => pattern < 3 && paddingCount payload.length != 0
    | _ => true) &&
  (malformation.change payload).valid canonicalSize

/-- The pinned std's decision for `run(uint256,bytes)` over raw calldata, with
the flags and the payload it copies into memory: after the dispatch and head
checks, the payload length must not exceed the bytes after its length Word,
and then std's bound `length <= ~0 - 63` holds. The padding is neither
required nor read. Otherwise the rejecting error selector. -/
def stdDecode (input : ByteArray) : Except Nat (Nat × List UInt8) := do
  let (flags, offset) ← StdCalldata.dynamicHead? input Solcore.Synthesis.Core.MalformedBytes.selector
  let length := StdCalldata.wordAt input (4 + offset)
  if length > input.size - (36 + offset) then throw Solcore.Synthesis.Core.StdDispatch.truncatedError
  if length > Solcore.Synthesis.Core.MalformedBytes.maxPayloadLength then
    throw Solcore.Synthesis.Core.StdDispatch.truncatedError
  return (flags, (input.extract (36 + offset) (36 + offset + length)).data.toList)

def stdRejection? (input : ByteArray) : Option Nat :=
  match stdDecode input with
  | .error selector => some selector
  | .ok _ => none

def stdDecoded? (input : ByteArray) : Option (Nat × List UInt8) := (stdDecode input).toOption

def calldata (tx : Transaction) : String := encodeBytesText (inputBytes tx)

def inputData? (tx : Transaction) : Option HostStorageDriver.InputData :=
  let bytes := inputBytes tx
  if bounded : bytes.size < wordModulus then some ⟨bytes, bounded⟩ else none

abbrev observedSlots := LongBytesExecution.observedSlots
abbrev slotsJson := LongBytesExecution.slotsJson

private def worldStorage (world : WorldState) (bindings : Bindings) : Json :=
  match world.account? bindings.address with
  | some account => LongBytesExecution.storageJson account
  | none => Json.null

private def outcomeFields : FrameOutcome Word → List (String × Json)
  | .returned bytes => [("status", toJson "returned"), ("output", toJson (encodeBytesText bytes))]
  | .reverted bytes => [("status", toJson "reverted"), ("output", toJson (encodeBytesText bytes))]
  | .trapped reason => [("status", toJson "trapped"), ("reason", toJson (toString reason.val))]

/-- Independent original-Core observation, as for the long-bytes profile,
with each transaction's malformed calldata as the input. -/
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
      match inputData? transaction, registry.resolve? prior bindings.address with
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

end Solcore.Synthesis.Stateful.MalformedBytesExecution
