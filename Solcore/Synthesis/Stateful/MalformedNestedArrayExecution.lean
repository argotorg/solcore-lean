import Solcore.Synthesis.Core.MalformedNestedArray
import Solcore.Synthesis.Stateful.StdCalldata
import Solcore.Synthesis.Stateful.StorageExecution
import Solcore.Synthesis.Stateful.NestedArrayExecution
import Solcore.Synthesis.Stateful.AccountStorage

/-! Execute the original checked malformed-nested-array contract over a
persistent account world. A transaction is a canonical `(flags, values)` call
of `run(uint256,uint256[][])` together with one malformation of its calldata;
the contract receives the malformed bytes. `stdDecode` is a second model of the
pinned std's dispatcher and lazy decoder, written over the bytes instead of in
Core, which prescribes each transaction's outcome and the Words the body reads.
Observations report slots zero to eight and the contract's whole committed
storage. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Stateful.MalformedNestedArrayExecution
open Lean Solcore.Core Solcore.ContractRuntime
open Solcore.Synthesis.Core.MalformedNestedArray (CheckedPlan)

def historySchema : String := "solcore-lean.malformed-nested-array-history.v1"

/-- One caller and one installed contract, exactly as for the storage profiles. -/
abbrev Bindings := StorageExecution.Bindings

/-- Canonical values have at most four rows of at most three elements, one row
and one element more than the protocol reads. -/
def maxRows : Nat := 4
def maxColumns : Nat := 3

/-- How a transaction's calldata departs from the canonical encoding of its
flags and values: the outer array's malformations, a replaced table Word of
row `row`, or a replaced length Word of row `row`. -/
inductive Malformation where
  | none
  | short (bytes : Nat)
  | selector (mask : Nat)
  | truncate (kept : Nat)
  | trailing (count pattern : Nat)
  | offset (value : Word)
  | length (value : Word)
  | rowOffset (row : Nat) (value : Word)
  | rowLength (row : Nat) (value : Word)
  deriving BEq, Repr

structure Transaction where
  id : String
  flags : Word
  values : List (List Word)
  malformation : Malformation
  deriving BEq

def canonicalBytes (tx : Transaction) : ByteArray :=
  NestedArrayExecution.inputBytes tx.flags tx.values

/-- The canonical offset table starts after the selector, the flags, the head
offset 64 and the outer length. -/
def tableStart : Nat := 100

/-- The byte position of row `row`'s length Word in the canonical encoding. -/
def rowStart (values : List (List Word)) (row : Nat) : Nat :=
  tableStart + (NestedArrayExecution.rowOffsets values).getD row 0

def Malformation.change (values : List (List Word)) : Malformation → StdCalldata.Change
  | .none => .none
  | .short bytes => .short bytes
  | .selector mask => .selector mask
  | .truncate kept => .truncate kept
  | .trailing count pattern => .trailing count pattern
  | .offset value => .word 36 value
  | .length value => .word 68 value
  | .rowOffset row value => .word (tableStart + 32 * row) value
  | .rowLength row value => .word (rowStart values row) value

/-- The calldata a transaction sends. -/
def inputBytes (tx : Transaction) : ByteArray :=
  (tx.malformation.change tx.values).apply (canonicalBytes tx)

/-- A malformation within its bounds; a row malformation names a present row. -/
def Malformation.valid (malformation : Malformation) (values : List (List Word)) (canonicalSize : Nat) : Bool :=
  (match malformation with
    | .rowOffset row _ | .rowLength row _ => row < values.length
    | _ => true) &&
  (malformation.change values).valid canonicalSize

/-- The pinned std's decision for `run(uint256,uint256[][])` over raw calldata,
with the Words the body then reads: the flags, the outer length and the
elements of every row it decodes, rows `i < min(n, 3)` in order. Rows past the
third are never decoded. Otherwise the rejecting error selector. -/
def stdDecode (input : ByteArray) : Except Nat (Nat × Nat × List (List Nat)) := do
  let (flags, offset) ← StdCalldata.dynamicHead? input Solcore.Synthesis.Core.MalformedNestedArray.selector
  let rows ← StdCalldata.arrayAt? input (4 + offset)
  let table := 36 + offset
  let read ← (List.range (min rows Solcore.Synthesis.Core.MalformedNestedArray.readRows)).mapM fun index => do
    let (start, length) ← StdCalldata.rowAt? input table index
    return (List.range length).map fun column => StdCalldata.wordAt input (start + 32 + 32 * column)
  return (flags, rows, read)

def stdRejection? (input : ByteArray) : Option Nat :=
  match stdDecode input with
  | .error selector => some selector
  | .ok _ => none

def stdDecoded? (input : ByteArray) : Option (Nat × Nat × List (List Nat)) := (stdDecode input).toOption

def calldata (tx : Transaction) : String := encodeBytesText (inputBytes tx)

def inputData? (tx : Transaction) : Option HostStorageDriver.InputData :=
  let bytes := inputBytes tx
  if bounded : bytes.size < wordModulus then some ⟨bytes, bounded⟩ else none

abbrev observedSlots := NestedArrayExecution.observedSlots
abbrev slotsJson := NestedArrayExecution.slotsJson

private def worldStorage (world : WorldState) (bindings : Bindings) : Json :=
  match world.account? bindings.address with
  | some account => NestedArrayExecution.storageJson account
  | none => Json.null

private def outcomeFields : FrameOutcome Word → List (String × Json)
  | .returned bytes => [("status", toJson "returned"), ("output", toJson (encodeBytesText bytes))]
  | .reverted bytes => [("status", toJson "reverted"), ("output", toJson (encodeBytesText bytes))]
  | .trapped reason => [("status", toJson "trapped"), ("reason", toJson (toString reason.val))]

/-- Independent original-Core observation, as for the nested-array profile,
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

end Solcore.Synthesis.Stateful.MalformedNestedArrayExecution
