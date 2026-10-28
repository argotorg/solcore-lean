import Solcore.Synthesis.Core.EnumArgument
import Solcore.Synthesis.Stateful.StdCalldata
import Solcore.Synthesis.Stateful.StorageExecution
import Solcore.Synthesis.Stateful.AccountStorage

/-! Execute the original checked enum-argument contract over a persistent
account world. A transaction is a canonical call of
`run(uint256 flags, SynthesizedEnum value)`, a constructor with its field Words
or `bytes` payload, together with one malformation of its calldata; the
contract receives the malformed bytes. `stdDecode` is a second model of the
pinned std's dispatcher and derived enum decoder, written over the bytes
instead of in Core, which prescribes each transaction's outcome and the Words
the body decodes. `model` runs the protocol on its decisions with the step
evaluated alone in Core. Observations report slots zero to four and the
contract's whole committed storage. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Stateful.EnumArgumentExecution
open Lean Solcore.Core Solcore.ContractRuntime
open Solcore.Synthesis.Core
open Solcore.Synthesis.Core.EnumArgument (CheckedPlan Constructor Payload Shape)
open Solcore.Synthesis.Core.StdDispatch (noSelectorError truncatedError)

def historySchema : String := "solcore-lean.enum-argument-history.v1"

/-- One caller and one installed contract, exactly as for the storage profiles. -/
abbrev Bindings := StorageExecution.Bindings

/-- The longest canonical `bytes` payload. -/
def maxLength : Nat := 64

/-- How a transaction's calldata departs from the canonical encoding of its
constructor: the malformed-calldata kinds; an unknown tag, another
constructor's tag, a head offset, the offset zero with the flags replaced by a
constructor's tag, an unread head Word, a `bytes` tail offset or length Word,
or nonzero padding. Padding patterns are `0xff` (0), the ramp `1, 2, 3, ...` (1)
or a single `0x01` in the last padding byte (2). -/
inductive Malformation where
  | none
  | short (bytes : Nat)
  | selector (mask : Nat)
  | truncate (kept : Nat)
  | trailing (count pattern : Nat)
  | tag (value : Word)
  | retag (index : Nat)
  | offset (value : Word)
  | aliased (index : Nat)
  | unused (value : Word)
  | tail (value : Word)
  | length (value : Word)
  | padding (pattern : Nat)
  deriving BEq, Repr

structure Transaction where
  id : String
  flags : Word
  choice : Nat
  first : Word
  second : Word
  length : Nat
  malformation : Malformation
  deriving BEq

/-- The bytes profile's odd constant. -/
def multiplier : Nat := Solcore.Synthesis.Core.BytesReturn.multiplier

/-- A `bytes` payload: the first `length` bytes of `first · K` and
`second · K`. -/
def payload (first second : Word) (length : Nat) : ByteArray :=
  (encodeWordBytesBE (first * Word.ofNatModulo multiplier) ++
    encodeWordBytesBE (second * Word.ofNatModulo multiplier)).extract 0 length

def paddedLength (length : Nat) : Nat := (length + 31) / 32 * 32

private def zeros (count : Nat) : ByteArray := ByteArray.mk (Array.replicate count 0)

/-- Where the body starts: inline at 36 for a static enum, at the canonical
offset 64 past the arguments' start for a dynamic one. -/
def bodyStart (shape : Shape) : Nat := if shape.dynamic then 68 else 36

/-- The chosen constructor, the first for an index outside the shape. -/
def constructorAt (shape : Shape) (index : Nat) : Constructor := shape.constructors.getD index shape.first

def constructor (shape : Shape) (tx : Transaction) : Constructor := constructorAt shape tx.choice

/-- The canonical body: the tag, the fields, zero Words up to the body's head,
then a `bytes` field's length Word and zero-padded payload behind the tail
offset, which is the body's head. -/
def body (shape : Shape) (tx : Transaction) : ByteArray :=
  let chosen := constructor shape tx
  let head := match chosen.payload with
    | .noWords => ByteArray.empty
    | .oneWord => encodeWordBytesBE tx.first
    | .twoWords | .pair => encodeWordBytesBE tx.first ++ encodeWordBytesBE tx.second
    | .bytes => encodeWordBytesBE (Word.ofNatModulo shape.bodyHead)
  let tail := match chosen.payload with
    | .bytes => encodeWordBytesBE (Word.ofNatModulo tx.length) ++ payload tx.first tx.second tx.length ++
        zeros (paddedLength tx.length - tx.length)
    | _ => ByteArray.empty
  encodeWordBytesBE (EnumArgument.tag chosen) ++ head ++
    zeros (shape.bodyHead - 32 - EnumArgument.headSize chosen.payload) ++ tail

private def selectorBytes (selector : Nat) : ByteArray :=
  ByteArray.mk #[(selector / 2 ^ 24 % 256).toUInt8, (selector / 2 ^ 16 % 256).toUInt8,
    (selector / 2 ^ 8 % 256).toUInt8, (selector % 256).toUInt8]

def canonicalBytes (shape : Shape) (tx : Transaction) : ByteArray :=
  selectorBytes shape.selector ++ encodeWordBytesBE tx.flags ++
    (if shape.dynamic then encodeWordBytesBE (Word.ofNatModulo 64) else ByteArray.empty) ++ body shape tx

def canonicalSize (shape : Shape) (tx : Transaction) : Nat := (canonicalBytes shape tx).size

/-- The payload start of a canonical `bytes` constructor. -/
def payloadStart (shape : Shape) : Nat := bodyStart shape + shape.bodyHead + 32

def paddingCount (length : Nat) : Nat := paddedLength length - length

/-- The last payload Word with its padding replaced by the pattern. -/
private def paddedWord (bytes : ByteArray) (length pattern : Nat) : Word :=
  let start := length / 32 * 32
  let count := paddingCount length
  let padding := (List.range count).map fun position =>
    match pattern with
    | 0 => (0xff : UInt8)
    | 1 => (position + 1).toUInt8
    | _ => if position + 1 = count then 1 else 0
  Word.ofNatModulo (((bytes.extract start length).data.toList ++ padding).foldl
    (fun total byte => total * 256 + byte.toNat) 0)

/-- The first head Word a narrower constructor leaves unread. -/
def unusedPosition (shape : Shape) (tx : Transaction) : Nat :=
  bodyStart shape + 32 + EnumArgument.headSize (constructor shape tx).payload

/-- Whether the chosen constructor's head is narrower than the body's head. -/
def hasUnused (shape : Shape) (tx : Transaction) : Bool :=
  32 + EnumArgument.headSize (constructor shape tx).payload < shape.bodyHead

def carriesBytes (shape : Shape) (tx : Transaction) : Bool := (constructor shape tx).payload == .bytes

/-- The calldata a transaction sends. -/
def inputBytes (shape : Shape) (tx : Transaction) : ByteArray :=
  let canonical := canonicalBytes shape tx
  let start := bodyStart shape
  let change : StdCalldata.Change := match tx.malformation with
    | .none => .none
    | .short bytes => .short bytes
    | .selector mask => .selector mask
    | .truncate kept => .truncate kept
    | .trailing count pattern => .trailing count pattern
    | .tag value => .word start value
    | .retag index => .word start (EnumArgument.tag (constructorAt shape index))
    | .offset value => .word 36 value
    | .aliased _ => .word 36 Word.zero
    | .unused value => .word (unusedPosition shape tx) value
    | .tail value => .word (start + 32) value
    | .length value => .word (start + shape.bodyHead) value
    | .padding pattern => .word (payloadStart shape + tx.length / 32 * 32)
        (paddedWord (payload tx.first tx.second tx.length) tx.length pattern)
  let changed := change.apply canonical
  match tx.malformation with
  | .aliased index => StdCalldata.replaceWord changed 4 (EnumArgument.tag (constructorAt shape index))
  | _ => changed

/-- A malformation within its bounds, where it applies: cuts inside the
calldata past the selector, the malformed-calldata bounds, another
constructor's tag, offsets and aliases of a dynamic enum, an unread head Word
of a narrower constructor, and `bytes` changes of a `bytes` constructor, its
padding only when there is some. -/
def Malformation.valid (shape : Shape) (tx : Transaction) : Malformation → Bool
  | .none => true
  | .short bytes => bytes < 4
  | .selector mask => 0 < mask && mask < 2 ^ 32
  | .truncate kept => 4 ≤ kept && kept < canonicalSize shape tx
  | .trailing count pattern => 1 ≤ count && count ≤ 64 && pattern < 3
  | .tag value => !shape.constructors.any (EnumArgument.tag · == value)
  | .retag index => index < shape.constructors.length && index != tx.choice
  | .offset value => shape.dynamic && value.val != 64
  | .aliased index => shape.dynamic && index < shape.constructors.length
  | .unused value => hasUnused shape tx && value != Word.zero
  | .tail value => carriesBytes shape tx && value.val != shape.bodyHead
  | .length value => carriesBytes shape tx && value.val != tx.length
  | .padding pattern => carriesBytes shape tx && paddingCount tx.length != 0 && pattern < 3

/-- The Words std decodes: the flags, the one-based index and the three
protocol Words. -/
structure Decoded where
  flags : Word
  index : Nat
  words : Word × Word × Word
  deriving BEq, Repr

/-- The revert data of a std rejection, or the decoded value. -/
abbrev Decision := Except ByteArray Decoded

private def wordAt (input : ByteArray) (offset : Nat) : Word := Word.ofNatModulo (StdCalldata.wordAt input offset)

/-- The payload's zero-padded Word at `offset`, from the bytes that exist. -/
private def chunkAt (input : ByteArray) (start length offset : Nat) : Word :=
  let bytes := (input.extract (start + offset) (start + length)).extract 0 32
  Word.ofNatModulo ((bytes.data.toList ++ List.replicate (32 - bytes.size) (0 : UInt8)).foldl
    (fun total byte => total * 256 + byte.toNat) 0)

/-- The pinned std's decision for `run(uint256 flags, E value)` over raw
calldata, written from `do_exec`, the bounded calldata reader, `abiSumReader`
and the derived decoder. The fallback reverts with `0x4924aef0`, a missing or
out-of-range read with `0x08638556`, and an unknown tag with empty data; the
tag is compared before any field is read. Natural arithmetic cannot wrap, as
std's checks do not. -/
def stdDecode (shape : Shape) (input : ByteArray) : Decision := do
  let size := input.size
  let fail := fun (error : Nat) => (Except.error (selectorBytes error) : Decision)
  if size < 4 || StdCalldata.bigEndian input 0 4 != shape.selector then fail noSelectorError
  else if size < 4 + shape.argumentsHead then fail truncatedError
  else
    let flags := wordAt input 4
    let start? : Option Nat :=
      if shape.dynamic then
        let offset := StdCalldata.wordAt input 36
        if offset > size - 4 then none else some (4 + offset)
      else some 36
    match start? with
    | none => fail truncatedError
    | some start =>
      if size - start < 32 then fail truncatedError
      else
        let found := wordAt input start
        match (shape.constructors.zipIdx.find? fun (constructor, _) => EnumArgument.tag constructor == found) with
        | none => throw ByteArray.empty
        | some (constructor, index) =>
          let decoded := fun (words : Word × Word × Word) => (pure ⟨flags, index + 1, words⟩ : Decision)
          match constructor.payload with
          | .noWords => decoded (Word.zero, Word.zero, Word.zero)
          | .oneWord =>
              if size - start < 64 then fail truncatedError
              else decoded (wordAt input (start + 32), Word.zero, Word.zero)
          | .twoWords | .pair =>
              if size - start < 96 then fail truncatedError
              else decoded (wordAt input (start + 32), wordAt input (start + 64), Word.zero)
          | .bytes =>
              if size - start < 64 then fail truncatedError
              else
                let tail := StdCalldata.wordAt input (start + 32)
                if tail > size - start then fail truncatedError
                else if size - (start + tail) < 32 then fail truncatedError
                else
                  let length := StdCalldata.wordAt input (start + tail)
                  if length > size - (start + tail + 32) then fail truncatedError
                  else if length > EnumArgument.maxPayloadLength then fail truncatedError
                  else
                    let data := start + tail + 32
                    decoded (Word.ofNatModulo length,
                      if length > 0 then chunkAt input data length 0 else Word.zero,
                      if length > 32 then chunkAt input data length 32 else Word.zero)

/-- std's revert data for a rejected transaction, or none when the body runs. -/
def stdRejection? (shape : Shape) (tx : Transaction) : Option ByteArray :=
  match stdDecode shape (inputBytes shape tx) with
  | .error data => some data
  | .ok _ => none

def calldata (shape : Shape) (tx : Transaction) : String := encodeBytesText (inputBytes shape tx)

def inputData? (shape : Shape) (tx : Transaction) : Option HostStorageDriver.InputData :=
  let bytes := inputBytes shape tx
  if bounded : bytes.size < wordModulus then some ⟨bytes, bounded⟩ else none

/-- Slot zero holds the accumulator, slot one the decoded index and slots two
to four the decoded Words. -/
def observedSlots : List Word := (List.range EnumArgument.slotCount).map Word.ofNatModulo

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

/-- Independent original-Core observation, as for the malformed-calldata
profiles, with each transaction's malformed calldata as the input. -/
def observeContract (contract : CheckedCoreContract) (shape : Shape) (transactions : List Transaction)
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
      match inputData? shape transaction, registry.resolve? prior bindings.address with
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
  observeContract plan.contract plan.shape transactions bindings fuel

/-- The step's own Core result at one argument. -/
def stepResult (step : Aggregates.CheckedDAG) (fuel : Nat) (argument : Word) : Option Word :=
  match (step.instantiate argument).toCore.runStateful fuel with
  | .done (.word value) _ => some value
  | _ => none

/-- One modelled transaction: whether it reverts, its whole output and the
slots it leaves committed. -/
structure ModelRow where
  reverted : Bool
  output : ByteArray
  slots : List Word

/-- std's decision, then the protocol: `r = step(prior + index + w0 + w1 + w2)`,
the five writes, and the flags' parity. A rejection outputs std's revert data
and keeps the prior slots. -/
def modelTransaction (step : Aggregates.CheckedDAG) (shape : Shape) (fuel : Nat)
    (prior : List Word) (transaction : Transaction) : Option ModelRow := do
  match stdDecode shape (inputBytes shape transaction) with
  | .error data => return ⟨true, data, prior⟩
  | .ok decoded =>
      let (w0, w1, w2) := decoded.words
      let index := Word.ofNatModulo decoded.index
      let result ← stepResult step fuel (prior.getD 0 Word.zero + index + w0 + w1 + w2)
      if decoded.flags.val % 2 == 1 then return ⟨true, encodeWordBytesBE result, prior⟩
      return ⟨false, encodeWordBytesBE result, [result, index, w0, w1, w2]⟩

/-- The modelled rows of a whole sequence from empty storage. -/
def model (step : Aggregates.CheckedDAG) (shape : Shape) (fuel : Nat)
    (transactions : List Transaction) : Option (List ModelRow) := Id.run do
  let mut slots : List Word := List.replicate EnumArgument.slotCount Word.zero
  let mut rows : Array ModelRow := #[]
  for transaction in transactions do
    match modelTransaction step shape fuel slots transaction with
    | some row =>
        rows := rows.push row
        slots := row.slots
    | none => return none
  return some rows.toList

end Solcore.Synthesis.Stateful.EnumArgumentExecution
