import Solcore.Synthesis.Core.MalformedCalldata
import Solcore.Synthesis.Stateful.StorageExecution
import Solcore.Synthesis.Stateful.DynamicArrayExecution
import Solcore.Synthesis.Stateful.AccountStorage

/-! Execute the original checked malformed-calldata contract over a persistent
account world. A transaction is a canonical `(flags, values)` call of
`run(uint256,uint256[])` together with one malformation of its calldata; the
contract receives the malformed bytes. `stdRejection?` is a second model of
the pinned std's dispatcher and decoder, written over the bytes instead of in
Core, which prescribes each transaction's outcome. Observations report slots
zero to four and the contract's whole committed storage. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Stateful.MalformedCalldataExecution
open Lean Solcore.Core Solcore.ContractRuntime
open Solcore.Synthesis.Core.MalformedCalldata (CheckedPlan)

def historySchema : String := "solcore-lean.malformed-calldata-history.v1"

/-- Calldata of every transaction stays within one KiB. -/
def maxCalldata : Nat := 1024

/-- One caller and one installed contract, exactly as for the storage profiles. -/
abbrev Bindings := StorageExecution.Bindings

/-- How a transaction's calldata departs from the canonical encoding of its
flags and values. Patterns of trailing bytes are zeros (0), `0xff` (1) or the
ramp `1, 2, 3, ...` (2). -/
inductive Malformation where
  | none
  | short (bytes : Nat)
  | selector (mask : Nat)
  | truncate (kept : Nat)
  | trailing (count pattern : Nat)
  | offset (value : Word)
  | length (value : Word)
  deriving BEq, Repr

structure Transaction where
  id : String
  flags : Word
  values : List Word
  malformation : Malformation
  deriving BEq

def canonicalBytes (tx : Transaction) : ByteArray :=
  DynamicArrayExecution.inputBytes tx.flags tx.values

/-- The byte at an index, zero past the end; callers read only present bytes. -/
private def byteAt (bytes : ByteArray) (index : Nat) : Nat :=
  (bytes.data[index]?.map UInt8.toNat).getD 0

private def bigEndian (bytes : ByteArray) (offset count : Nat) : Nat :=
  (List.range count).foldl (fun total index => total * 256 + byteAt bytes (offset + index)) 0

private def replaceWord (bytes : ByteArray) (offset : Nat) (value : Word) : ByteArray :=
  bytes.extract 0 offset ++ encodeWordBytesBE value ++ bytes.extract (offset + 32) bytes.size

private def patternByte (pattern position : Nat) : UInt8 :=
  match pattern with
  | 0 => 0
  | 1 => 0xff
  | _ => (position + 1).toUInt8

/-- The calldata a transaction sends. -/
def inputBytes (tx : Transaction) : ByteArray :=
  let canonical := canonicalBytes tx
  match tx.malformation with
  | .none => canonical
  | .short bytes => canonical.extract 0 bytes
  | .selector mask =>
      let changed := (bigEndian canonical 0 4 ^^^ mask) % 2 ^ 32
      ByteArray.mk #[(changed / 2 ^ 24 % 256).toUInt8, (changed / 2 ^ 16 % 256).toUInt8,
        (changed / 2 ^ 8 % 256).toUInt8, (changed % 256).toUInt8] ++ canonical.extract 4 canonical.size
  | .truncate kept => canonical.extract 0 kept
  | .trailing count pattern => canonical ++ ByteArray.mk ((List.range count).map (patternByte pattern)).toArray
  | .offset value => replaceWord canonical 36 value
  | .length value => replaceWord canonical 68 value

/-- A malformation that changes the canonical calldata within its bounds:
selector prefixes, nonzero 32-bit masks, cuts inside the calldata past the
selector, one to 64 trailing bytes, and any replaced Word. -/
def Malformation.valid (malformation : Malformation) (canonicalSize : Nat) : Bool :=
  match malformation with
  | .none => true
  | .short bytes => bytes < 4
  | .selector mask => 0 < mask && mask < 2 ^ 32
  | .truncate kept => 4 ≤ kept && kept < canonicalSize
  | .trailing count pattern => 1 ≤ count && count ≤ 64 && pattern < 3
  | .offset _ | .length _ => true

private def wordAt (bytes : ByteArray) (offset : Nat) : Nat := bigEndian bytes offset 32

/-- The pinned std's decision for `run(uint256,uint256[])` over raw calldata:
the rejecting error selector, or none when the method body runs. Natural
arithmetic cannot wrap, as std's checked word arithmetic does not. -/
def stdRejection? (input : ByteArray) : Option Nat :=
  let size := input.size
  if size < 4 then some Solcore.Synthesis.Core.MalformedCalldata.noSelectorError
  else if bigEndian input 0 4 != Solcore.Synthesis.Core.MalformedCalldata.selector then
    some Solcore.Synthesis.Core.MalformedCalldata.noSelectorError
  else if size < 68 then some Solcore.Synthesis.Core.MalformedCalldata.truncatedError
  else
    let offset := wordAt input 36
    if offset > size - 4 then some Solcore.Synthesis.Core.MalformedCalldata.truncatedError
    else if size - (4 + offset) < 32 then some Solcore.Synthesis.Core.MalformedCalldata.truncatedError
    else
      let length := wordAt input (4 + offset)
      if length > Solcore.Synthesis.Core.MalformedCalldata.maxLength then
        some Solcore.Synthesis.Core.MalformedCalldata.truncatedError
      else if 32 * length > size - (36 + offset) then some Solcore.Synthesis.Core.MalformedCalldata.truncatedError
      else none

/-- The words std decodes when it accepts: flags, length and every element. -/
def stdDecoded? (input : ByteArray) : Option (Nat × List Nat) :=
  if (stdRejection? input).isSome then none
  else
    let offset := wordAt input 36
    let length := wordAt input (4 + offset)
    some (wordAt input 4, (List.range length).map fun index => wordAt input (36 + offset + 32 * index))

def calldata (tx : Transaction) : String := encodeBytesText (inputBytes tx)

def inputData? (tx : Transaction) : Option HostStorageDriver.InputData :=
  let bytes := inputBytes tx
  if bounded : bytes.size < wordModulus then some ⟨bytes, bounded⟩ else none

abbrev observedSlots := DynamicArrayExecution.observedSlots
abbrev slotsJson := DynamicArrayExecution.slotsJson

private def worldStorage (world : WorldState) (bindings : Bindings) : Json :=
  match world.account? bindings.address with
  | some account => DynamicArrayExecution.storageJson account
  | none => Json.null

private def outcomeFields : FrameOutcome Word → List (String × Json)
  | .returned bytes => [("status", toJson "returned"), ("output", toJson (encodeBytesText bytes))]
  | .reverted bytes => [("status", toJson "reverted"), ("output", toJson (encodeBytesText bytes))]
  | .trapped reason => [("status", toJson "trapped"), ("reason", toJson (toString reason.val))]

/-- Independent original-Core observation, as for the dynamic-array profile,
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

end Solcore.Synthesis.Stateful.MalformedCalldataExecution
