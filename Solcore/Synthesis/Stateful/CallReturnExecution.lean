import Solcore.Synthesis.Core.CallReturn
import Solcore.Synthesis.Stateful.NestedCallExecution
import Solcore.Synthesis.Stateful.StdCalldata

/-! Execute the original checked call-return contracts over an account world.
The parent is installed as its call phase and the child as its contract; each
transaction runs through the public call-and-resume convention, which runs the
call phase, the child and the resume phase through the public top-level runner
and commits as one transaction. Only the convention's committed world becomes
the next transaction's world. Observations report each transaction's whole
return data, the parent's slots 0 to 6, the child's slots 0 and 1, both
balances and both contracts' whole committed storage; no transaction commits a
log.

`decide` is a second model of std's decision on the return data, written over
the bytes instead of in Core: std's `MemoryWordReader` over `raw_call`'s copy,
from 0 with no up-front size check, every read and advance inside the data.
`returnBytes` builds the child's bytes from its Words, and `model` reads both
sources on them, with the step evaluated alone in Core. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Stateful.CallReturnExecution
open Lean Solcore.Core Solcore.ContractRuntime
open Solcore.Synthesis.Core
open Solcore.Synthesis.Core.CallReturn (CheckedPlan Kind Returned Cell Source)
open Solcore.Synthesis.Core.EnumReturn (Constructor Shape)
open Solcore.Synthesis.Core.StdDispatch (truncatedError)

def historySchema : String := "solcore-lean.call-return-history.v1"

/-- The caller, the parent and the child, as for `stateful-calls`. -/
abbrev Bindings := NestedCallExecution.Bindings

abbrev Transaction := StorageExecution.Transaction

/-- The selector of `run(uint256,uint256)`, the bound child and the input. -/
def inputData (bindings : Bindings) (input : Word) : HostStorageDriver.InputData :=
  NestedCallExecution.inputData bindings input

def calldata (bindings : Bindings) (input : Word) : String := encodeBytesText (inputData bindings input).bytes

/-- The caller, the parent installed as its call phase and the child, all with
zero balance and empty storage. -/
def initialWorld (plan : CheckedPlan) (bindings : Bindings) : WorldState :=
  WorldState.empty
    |>.putAccount bindings.caller Account.empty
    |>.putAccount bindings.parent (Account.empty.withCode plan.callContract.code)
    |>.putAccount bindings.child (Account.empty.withCode plan.childContract.code)

/-- The child is the only contract a call resolves. -/
def registry (plan : CheckedPlan) (bindings : Bindings) : CheckedContractRegistry := {
  lookup := fun target => if target = bindings.child then some plan.childContract else none }

def parentSlots : List Word := (List.range CallReturn.parentSlotCount).map Word.ofNatModulo
def childSlots : List Word := (List.range CallReturn.childSlotCount).map Word.ofNatModulo

private def slotsJson (account : Account) (slots : List Word) : Json := toJson (slots.map fun slot => Json.mkObj [
  ("slot", toJson (toString slot.val)), ("value", toJson (toString (account.storageRead slot).val))])

private def accountJson (world : WorldState) (role : String) (address : Address) (slots : List Word) : Json :=
  match world.account? address with
  | none => Json.null
  | some account => Json.mkObj [
      ("role", toJson role), ("address", toJson (toString address.val)),
      ("balance", toJson (toString account.balance.val)), ("storage", slotsJson account slots)]

def accountsJson (world : WorldState) (bindings : Bindings) : Json := toJson [
  accountJson world "parent" bindings.parent parentSlots, accountJson world "child" bindings.child childSlots]

/-- Both contracts' whole committed storage, in role order. -/
def wholeStorageJson (world : WorldState) (bindings : Bindings) : Json :=
  AccountStorage.worldJson world [("parent", bindings.parent), ("child", bindings.child)]

private def outcomeFields : FrameOutcome Word → List (String × Json)
  | .returned bytes => [("status", toJson "returned"), ("output", toJson (encodeBytesText bytes))]
  | .reverted bytes => [("status", toJson "reverted"), ("output", toJson (encodeBytesText bytes))]
  | .trapped reason => [("status", toJson "trapped"), ("reason", toJson (toString reason.val))]

private def stoppedRow (common : List (String × Json)) (status : String) (world : WorldState) (bindings : Bindings) : Json :=
  Json.mkObj (common ++ [("status", toJson status), ("committedAccounts", accountsJson world bindings),
    ("accountStorage", wholeStorageJson world bindings), ("logs", Json.null)])

/-- Each transaction runs through the convention against the current committed
world; local heaps start fresh and only the committed world persists. -/
def observe (plan : CheckedPlan) (transactions : List Transaction) (bindings : Bindings) (fuel : Nat) : Json := Id.run do
  let mut world := initialWorld plan bindings
  let initial := accountsJson world bindings
  let initialWhole := wholeStorageJson world bindings
  let mut rows : Array Json := #[]
  let mut stopped : Option String := none
  for (transaction, index) in transactions.zipIdx do
    if stopped.isNone then
      let common := [("id", toJson transaction.id), ("index", toJson index)]
      match CallResumeExecution.run (registry plan bindings) plan.parent world bindings.parent bindings.caller
          (inputData bindings transaction.input) fuel with
      | .completed outcome finalWorld _ _ =>
          world := finalWorld
          rows := rows.push (Json.mkObj (common ++ outcomeFields outcome ++ [
            ("committedAccounts", accountsJson world bindings), ("accountStorage", wholeStorageJson world bindings),
            ("logs", toJson ([] : List Json))]))
          match outcome with
          | .trapped _ => stopped := some transaction.id
          | _ => pure ()
      | .outOfFuel _ =>
          rows := rows.push (stoppedRow common "out-of-fuel" world bindings)
          stopped := some transaction.id
      | .unresolved _ =>
          rows := rows.push (stoppedRow common "resolution-failure" world bindings)
          stopped := some transaction.id
      | .inputLimit =>
          rows := rows.push (stoppedRow common "input-limit" world bindings)
          stopped := some transaction.id
  return Json.mkObj [("schema", toJson historySchema), ("bindings", NestedCallExecution.bindingsJson bindings),
    ("fuelPerTransaction", toJson fuel), ("initialAccounts", initial), ("initialAccountStorage", initialWhole),
    ("transactions", .arr rows), ("finalAccounts", accountsJson world bindings),
    ("finalAccountStorage", wholeStorageJson world bindings),
    ("status", toJson (if stopped.isNone then "complete" else "incomplete")),
    ("stoppedAt", stopped.map toJson |>.getD Json.null),
    ("unexecuted", toJson ((transactions.drop rows.size).map (·.id)))]

/-! ### The byte-level model -/

/-- The child's values for one call. -/
structure Values where
  r : Word
  c : Word
  x : Word
  o : Word
  d0 : Word
  d1 : Word

def valuesOf (r c x o : Word) : Values :=
  let multiplier := Word.ofNatModulo CallReturn.multiplier
  ⟨r, c, x, o, r * multiplier, Word.ofNatModulo ((c * multiplier).val ^^^ x.val)⟩

private def sourceValue (values : Values) : Source → Word
  | .r => values.r
  | .c => values.c
  | .x => values.x
  | .o => values.o
  | .d0 => values.d0
  | .d1 => values.d1

def cellWord (values : Values) : Cell → Word
  | .const value => value
  | .value source kept =>
      if kept ≥ 32 then sourceValue values source
      else Word.ofNatModulo ((sourceValue values source).val &&& CallReturn.keepMask kept)

/-- The child's return data: its Words cut to the size it returns. -/
def returnBytes (returned : Returned) (values : Values) : ByteArray :=
  let (cells, size) := CallReturn.returnedCells returned
  (cells.foldl (fun bytes cell => bytes ++ encodeWordBytesBE (cellWord values cell)) ByteArray.empty).extract 0 size

private def selectorBytes (selector : Nat) : ByteArray :=
  ByteArray.mk #[(selector / 2 ^ 24 % 256).toUInt8, (selector / 2 ^ 16 % 256).toUInt8,
    (selector / 2 ^ 8 % 256).toUInt8, (selector % 256).toUInt8]

def truncatedData : ByteArray := selectorBytes truncatedError

private def wordAt (data : ByteArray) (offset : Nat) : Word := Word.ofNatModulo (StdCalldata.wordAt data offset)

/-- The payload's zero-padded Word at `offset`, from the bytes that exist, as
std's copy leaves it in memory. -/
private def chunkAt (data : ByteArray) (start length offset : Nat) : Word :=
  let bytes := (data.extract (start + offset) (start + length)).extract 0 32
  Word.ofNatModulo ((bytes.data.toList ++ List.replicate (32 - bytes.size) (0 : UInt8)).foldl
    (fun total byte => total * 256 + byte.toNat) 0)

/-- A `bytes` value whose tail offset Word lies at `head` relative to `base`:
the offset `t <= size - base`, a length Word at `base + t` and a length that
fits after it. Returns the length and its two zero-padded chunks. -/
private def bytesAt (data : ByteArray) (base head : Nat) : Option (Word × Word × Word) :=
  let size := data.size
  if size - base < head + 32 then none
  else
    let tail := StdCalldata.wordAt data (base + head)
    if tail > size - base then none
    else if size - (base + tail) < 32 then none
    else
      let length := StdCalldata.wordAt data (base + tail)
      if length > size - (base + tail + 32) then none
      else
        let start := base + tail + 32
        some (Word.ofNatModulo length, if length > 0 then chunkAt data start length 0 else Word.zero,
          if length > 32 then chunkAt data start length 32 else Word.zero)

/-- The decoded record: the constructor index and four Words. -/
structure Record where
  index : Word
  w0 : Word
  w1 : Word
  w2 : Word
  w3 : Word
  deriving BEq, Repr

def Record.toList (record : Record) : List Word := [record.index, record.w0, record.w1, record.w2, record.w3]

/-- std's revert data for a rejection, or the record. -/
abbrev Decision := Except ByteArray Record

/-- An enum body at `start`: the tag compared with each constructor's tag in
declaration order before any field is read, then the chosen constructor's
fields, each Word required to exist. -/
private def enumAt (shape : Shape) (data : ByteArray) (start : Nat) : Decision :=
  let size := data.size
  let trunc : Decision := .error truncatedData
  if size - start < 32 then trunc
  else
    let found := wordAt data start
    match shape.constructors.zipIdx.find? (fun (constructor, _) => EnumReturn.tag constructor == found) with
    | none => .error ByteArray.empty
    | some (constructor, index) =>
        let i := Word.ofNatModulo (index + 1)
        match constructor.payload with
        | .noWords => pure ⟨i, Word.zero, Word.zero, Word.zero, Word.zero⟩
        | .oneWord => if size - start < 64 then trunc else pure ⟨i, wordAt data (start + 32), Word.zero, Word.zero, Word.zero⟩
        | .twoWords =>
            if size - start < 96 then trunc
            else pure ⟨i, wordAt data (start + 32), wordAt data (start + 64), Word.zero, Word.zero⟩
        | .boundedBytes => match bytesAt data start 32 with
            | some (length, first, second) => pure ⟨i, length, first, second, Word.zero⟩
            | none => trunc

/-- std's decision on the return data as the plan's type: a failure is
`0x08638556`, an unknown tag empty data. -/
def decide (kind : Kind) (data : ByteArray) : Decision :=
  let size := data.size
  let trunc : Decision := .error truncatedData
  match kind with
  | .tuple extra =>
      let count := extra + 2
      if size < 32 * count then trunc
      else pure ⟨Word.zero, wordAt data 0, wordAt data 32, if count > 2 then wordAt data 64 else Word.zero,
        if count > 3 then wordAt data 96 else Word.zero⟩
  | .bytes => match bytesAt data 0 0 with
      | some (length, first, second) => pure ⟨Word.zero, length, first, second, Word.zero⟩
      | none => trunc
  | .enum shape =>
      if shape.dynamic then
        if size < 32 then trunc
        else
          let offset := StdCalldata.wordAt data 0
          if offset > size then trunc else enumAt shape data offset
      else enumAt shape data 0

def stepResult (step : Aggregates.CheckedDAG) (fuel : Nat) (argument : Word) : Option Word :=
  match (step.instantiate argument).toCore.runStateful fuel with
  | .done (.word value) _ => some value
  | _ => none

/-- std's revert data when the transaction's decoding rejects the child's
return data; none when the child reverts or std accepts. -/
def stdRejection? (plan : CheckedPlan) (fuel : Nat) (childSlots : Word × Word) (input : Word) :
    Option (Option ByteArray) := do
  let (o, count) := childSlots
  let r ← stepResult plan.step fuel (input + o)
  if input.val % 2 == 1 then return none
  match decide plan.returned.kind (returnBytes plan.returned (valuesOf r (count + Word.ofNatModulo 1) input o)) with
  | .error data => return some data
  | .ok _ => return none

/-- One modelled transaction: whether it reverts, original Core's output (its
Word, or std's selector Word and the Word zero for a rejection), whether that
output is a rejection, and the parent's and child's committed slots. -/
structure ModelRow where
  reverted : Bool
  output : ByteArray
  rejection : Option ByteArray
  parent : List Word
  child : List Word

/-- The rows the sources prescribe: the pre-call write, the child's step,
writes and odd-`x` revert of 32 bytes, std's decision on its return data, the
parent's writes and sum, and bit 1's revert; a revert keeps every prior slot. -/
def model (plan : CheckedPlan) (fuel : Nat) (transactions : List Transaction) : Option (List ModelRow) := Id.run do
  let mut parent : List Word := List.replicate CallReturn.parentSlotCount Word.zero
  let mut child : List Word := List.replicate CallReturn.childSlotCount Word.zero
  let mut rows : Array ModelRow := #[]
  for transaction in transactions do
    let x := transaction.input
    let o := child.getD 0 Word.zero
    let c := child.getD 1 Word.zero + Word.ofNatModulo 1
    let some r := stepResult plan.step fuel (x + o) | return none
    let accumulator := parent.getD 0 Word.zero + x
    let returned := x.val % 2 == 0
    let data := if returned then returnBytes plan.returned (valuesOf r c x o) else encodeWordBytesBE r
    let decision : Decision :=
      if returned then decide plan.returned.kind data
      else pure ⟨Word.zero, if data.size ≥ 32 then wordAt data 0 else Word.zero, Word.zero, Word.zero, Word.zero⟩
    match decision with
    | .error rejection =>
        let word := if rejection.isEmpty then Word.zero else Word.ofNatModulo truncatedError
        rows := rows.push ⟨true, encodeWordBytesBE word, some rejection, parent, child⟩
    | .ok record =>
        let flag := if returned then Word.ofNatModulo 1 else Word.zero
        let written := [accumulator, flag + Word.ofNatModulo (2 * data.size)] ++ record.toList
        let sum := record.toList.foldl (· + ·) accumulator
        if x.val / 2 % 2 == 1 then
          rows := rows.push ⟨true, encodeWordBytesBE sum, none, parent, child⟩
        else
          parent := written
          if returned then child := [r, c]
          rows := rows.push ⟨false, encodeWordBytesBE sum, none, parent, child⟩
  return some rows.toList

end Solcore.Synthesis.Stateful.CallReturnExecution
