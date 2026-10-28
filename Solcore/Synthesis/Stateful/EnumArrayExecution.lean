import Solcore.Synthesis.Core.EnumArray
import Solcore.Synthesis.Stateful.EnumArgumentExecution

/-! Execute the original checked enum-array contract over a persistent account
world. A transaction is a canonical call of
`run(uint256 flags, SynthesizedEnum[] items, uint256 first, uint256 second)`:
up to three elements, each a constructor with its field Words or `bytes`
payload, and two indices, together with one malformation of its calldata; the
contract receives the malformed bytes. `stdDecode` is a second model of the
pinned std's dispatcher, lazy calldata-array decoder, `abiArrayGet` and derived
enum decoder, written over the bytes instead of in Core, which prescribes each
transaction's outcome and the Words the body decodes. `model` runs the protocol
on its decisions with the step evaluated alone in Core. Observations report
slots zero to nine and the contract's whole committed storage. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Stateful.EnumArrayExecution
open Lean Solcore.Core Solcore.ContractRuntime
open Solcore.Synthesis.Core
open Solcore.Synthesis.Core.EnumArgument (Constructor Payload Shape)
open Solcore.Synthesis.Core.EnumArray (CheckedPlan outOfBoundsError)
open Solcore.Synthesis.Core.StdDispatch (noSelectorError truncatedError)

def historySchema : String := "solcore-lean.enum-array-history.v1"

/-- One caller and one installed contract, exactly as for the storage profiles. -/
abbrev Bindings := StorageExecution.Bindings

/-- The longest canonical `bytes` payload. -/
abbrev maxLength : Nat := EnumArgumentExecution.maxLength

/-- The most elements a canonical array carries. -/
def maxElements : Nat := 3

/-- A canonical element: a constructor, its field Words and a `bytes` length. -/
structure Element where
  choice : Nat
  a : Word
  b : Word
  length : Nat
  deriving BEq, Repr

/-- How a transaction's calldata departs from the canonical encoding: the
malformed-calldata kinds; the array's offset or length Word; and, for element
`target`, an unknown tag, another constructor's tag, its offset Word in a
dynamic array's table, another element's offset there, an unread head Word, a
`bytes` tail offset or length Word, or nonzero padding. Padding patterns are
`0xff` (0), the ramp `1, 2, 3, ...` (1) or a single `0x01` in the last padding
byte (2). -/
inductive Malformation where
  | none
  | short (bytes : Nat)
  | selector (mask : Nat)
  | truncate (kept : Nat)
  | trailing (count pattern : Nat)
  | offset (value : Word)
  | count (value : Word)
  | tag (target : Nat) (value : Word)
  | retag (target index : Nat)
  | entry (target : Nat) (value : Word)
  | share (target source : Nat)
  | unused (target : Nat) (value : Word)
  | tail (target : Nat) (value : Word)
  | length (target : Nat) (value : Word)
  | padding (target pattern : Nat)
  deriving BEq, Repr

structure Transaction where
  id : String
  flags : Word
  elements : List Element
  first : Word
  second : Word
  malformation : Malformation
  deriving BEq

/-- A `bytes` payload: the first `length` bytes of `a · K` and `b · K`. -/
def payload (element : Element) : ByteArray := EnumArgumentExecution.payload element.a element.b element.length

abbrev paddedLength := EnumArgumentExecution.paddedLength

private def zeros (count : Nat) : ByteArray := ByteArray.mk (Array.replicate count 0)

/-- The chosen constructor, the first for an index outside the shape. -/
def constructorAt (shape : Shape) (index : Nat) : Constructor := shape.constructors.getD index shape.first

def elementConstructor (shape : Shape) (element : Element) : Constructor := constructorAt shape element.choice

/-- The canonical body: the tag, the fields, zero Words up to the body's head,
then a `bytes` field's length Word and zero-padded payload behind the tail
offset, which is the body's head. -/
def body (shape : Shape) (element : Element) : ByteArray :=
  let chosen := elementConstructor shape element
  let head := match chosen.payload with
    | .noWords => ByteArray.empty
    | .oneWord => encodeWordBytesBE element.a
    | .twoWords | .pair => encodeWordBytesBE element.a ++ encodeWordBytesBE element.b
    | .bytes => encodeWordBytesBE (Word.ofNatModulo shape.bodyHead)
  let tail := match chosen.payload with
    | .bytes => encodeWordBytesBE (Word.ofNatModulo element.length) ++ payload element ++
        zeros (paddedLength element.length - element.length)
    | _ => ByteArray.empty
  encodeWordBytesBE (EnumArgument.tag chosen) ++ head ++
    zeros (shape.bodyHead - 32 - EnumArgument.headSize chosen.payload) ++ tail

/-- The canonical array's offset, the arguments' head. -/
def arrayOffset : Nat := EnumArray.argumentsHead

/-- The canonical length Word, right after the head. -/
def lengthPosition : Nat := 4 + arrayOffset

/-- The element region, right after the canonical length Word. -/
def regionStart : Nat := lengthPosition + 32

/-- A dynamic array's table: element `k`'s offset from the region, past the
table and the bodies before it. -/
def tableOffsets (shape : Shape) (tx : Transaction) : List Nat :=
  let sizes := tx.elements.map fun element => (body shape element).size
  (List.range tx.elements.length).map fun index => 32 * tx.elements.length + (sizes.take index).foldl (· + ·) 0

/-- Where element `k`'s canonical body starts. -/
def bodyStart (shape : Shape) (tx : Transaction) (index : Nat) : Nat :=
  if shape.dynamic then regionStart + (tableOffsets shape tx).getD index 0
  else regionStart + index * EnumArray.stride shape

private def selectorBytes (selector : Nat) : ByteArray :=
  ByteArray.mk #[(selector / 2 ^ 24 % 256).toUInt8, (selector / 2 ^ 16 % 256).toUInt8,
    (selector / 2 ^ 8 % 256).toUInt8, (selector % 256).toUInt8]

private def words (values : List Nat) : ByteArray :=
  values.foldl (fun bytes value => bytes ++ encodeWordBytesBE (Word.ofNatModulo value)) ByteArray.empty

/-- The selector, the flags, the array's offset, the two indices, the length,
then a dynamic array's offset table and the bodies in order. -/
def canonicalBytes (shape : Shape) (tx : Transaction) : ByteArray :=
  selectorBytes (EnumArray.selector shape) ++ encodeWordBytesBE tx.flags ++
    encodeWordBytesBE (Word.ofNatModulo arrayOffset) ++ encodeWordBytesBE tx.first ++ encodeWordBytesBE tx.second ++
    encodeWordBytesBE (Word.ofNatModulo tx.elements.length) ++
    (if shape.dynamic then words (tableOffsets shape tx) else ByteArray.empty) ++
    tx.elements.foldl (fun bytes element => bytes ++ body shape element) ByteArray.empty

def canonicalSize (shape : Shape) (tx : Transaction) : Nat := (canonicalBytes shape tx).size

def elementAt? (tx : Transaction) (index : Nat) : Option Element := tx.elements[index]?

/-- The payload start of element `k`, when it carries `bytes`. -/
def payloadStart (shape : Shape) (tx : Transaction) (index : Nat) : Nat :=
  bodyStart shape tx index + shape.bodyHead + 32

abbrev paddingCount := EnumArgumentExecution.paddingCount

/-- The last payload Word of an element with its padding replaced by the
pattern. -/
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

/-- Whether element `k` exists and its constructor's head is narrower than the
body's head. -/
def hasUnused (shape : Shape) (tx : Transaction) (index : Nat) : Bool :=
  match elementAt? tx index with
  | some element => 32 + EnumArgument.headSize (elementConstructor shape element).payload < shape.bodyHead
  | none => false

def carriesBytes (shape : Shape) (tx : Transaction) (index : Nat) : Bool :=
  match elementAt? tx index with
  | some element => (elementConstructor shape element).payload == .bytes
  | none => false

private def elementLength (tx : Transaction) (index : Nat) : Nat := ((elementAt? tx index).map (·.length)).getD 0

/-- The calldata a transaction sends. -/
def inputBytes (shape : Shape) (tx : Transaction) : ByteArray :=
  let start := bodyStart shape tx
  let entryAt := fun (index : Nat) => regionStart + 32 * index
  let change : StdCalldata.Change := match tx.malformation with
    | .none => .none
    | .short bytes => .short bytes
    | .selector mask => .selector mask
    | .truncate kept => .truncate kept
    | .trailing extra pattern => .trailing extra pattern
    | .offset value => .word 36 value
    | .count value => .word lengthPosition value
    | .tag target value => .word (start target) value
    | .retag target index => .word (start target) (EnumArgument.tag (constructorAt shape index))
    | .entry target value => .word (entryAt target) value
    | .share target source => .word (entryAt target) (Word.ofNatModulo ((tableOffsets shape tx).getD source 0))
    | .unused target value =>
        let width := ((elementAt? tx target).map fun element =>
          EnumArgument.headSize (elementConstructor shape element).payload).getD 0
        .word (start target + 32 + width) value
    | .tail target value => .word (start target + 32) value
    | .length target value => .word (start target + shape.bodyHead) value
    | .padding target pattern =>
        let element := (elementAt? tx target).getD ⟨0, Word.zero, Word.zero, 0⟩
        .word (payloadStart shape tx target + element.length / 32 * 32)
          (paddedWord (payload element) element.length pattern)
  change.apply (canonicalBytes shape tx)

/-- A malformation within its bounds, where it applies: cuts inside the
calldata past the selector, the malformed-calldata bounds, another offset or
length, an existing target element, another constructor's tag, table changes
of a dynamic array, an unread head Word of a narrower constructor, and `bytes`
changes of a `bytes` element, its padding only when there is some. -/
def Malformation.valid (shape : Shape) (tx : Transaction) : Malformation → Bool
  | .none => true
  | .short bytes => bytes < 4
  | .selector mask => 0 < mask && mask < 2 ^ 32
  | .truncate kept => 4 ≤ kept && kept < canonicalSize shape tx
  | .trailing extra pattern => 1 ≤ extra && extra ≤ 64 && pattern < 3
  | .offset value => value.val != arrayOffset
  | .count value => value.val != tx.elements.length
  | .tag target value => target < tx.elements.length && !shape.constructors.any (EnumArgument.tag · == value)
  | .retag target index => match elementAt? tx target with
      | some element => index < shape.constructors.length && index != element.choice
      | _ => false
  | .entry target value => shape.dynamic && target < tx.elements.length &&
      value.val != (tableOffsets shape tx).getD target 0
  | .share target source => shape.dynamic && target < tx.elements.length && source < tx.elements.length &&
      source != target
  | .unused target value => hasUnused shape tx target && value != Word.zero
  | .tail target value => carriesBytes shape tx target && value.val != shape.bodyHead
  | .length target value => carriesBytes shape tx target && value.val != elementLength tx target
  | .padding target pattern => carriesBytes shape tx target && paddingCount (elementLength tx target) != 0 &&
      pattern < 3

/-- An element as std decodes it: the one-based index and the three protocol
Words. -/
structure DecodedElement where
  index : Nat
  words : Word × Word × Word
  deriving BEq, Repr

/-- The Words std decodes: the flags, the length and both elements. -/
structure Decoded where
  flags : Word
  length : Word
  first : DecodedElement
  second : DecodedElement
  deriving BEq, Repr

/-- The revert data of a std rejection, or the decoded value. -/
abbrev Decision := Except ByteArray Decoded

private def wordAt (input : ByteArray) (offset : Nat) : Word := Word.ofNatModulo (StdCalldata.wordAt input offset)

/-- The payload's zero-padded Word at `offset`, from the bytes that exist. -/
private def chunkAt (input : ByteArray) (start length offset : Nat) : Word :=
  let bytes := (input.extract (start + offset) (start + length)).extract 0 32
  Word.ofNatModulo ((bytes.data.toList ++ List.replicate (32 - bytes.size) (0 : UInt8)).foldl
    (fun total byte => total * 256 + byte.toNat) 0)

/-- `abiArrayGet` of element `i` of an array whose region `R` follows a length
`L` that std accepted: `i >= L` is out of bounds; a static element's body is at
`R + i s`; a dynamic element's offset `e` at `R + 32 i` must satisfy
`e <= size - R` and its tag Word must exist at `R + e`; then the tag and the
fields as for one enum argument. Natural arithmetic cannot wrap, as std's
checks do not. -/
def decodeElement (shape : Shape) (input : ByteArray) (region length index : Nat) :
    Except ByteArray DecodedElement := do
  let size := input.size
  let fail := fun (error : Nat) => (Except.error (selectorBytes error) : Except ByteArray DecodedElement)
  if index ≥ length then fail outOfBoundsError
  else
    let start? : Option Nat :=
      if shape.dynamic then
        let offset := StdCalldata.wordAt input (region + 32 * index)
        if offset > size - region then none else some (region + offset)
      else some (region + index * EnumArray.stride shape)
    match start? with
    | none => fail truncatedError
    | some start =>
      if size - start < 32 then fail truncatedError
      else
        let found := wordAt input start
        match (shape.constructors.zipIdx.find? fun (constructor, _) => EnumArgument.tag constructor == found) with
        | none => throw ByteArray.empty
        | some (constructor, position) =>
          let decoded := fun (words : Word × Word × Word) =>
            (pure ⟨position + 1, words⟩ : Except ByteArray DecodedElement)
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
                  let count := StdCalldata.wordAt input (start + tail)
                  if count > size - (start + tail + 32) then fail truncatedError
                  else if count > EnumArgument.maxPayloadLength then fail truncatedError
                  else
                    let data := start + tail + 32
                    decoded (Word.ofNatModulo count,
                      if count > 0 then chunkAt input data count 0 else Word.zero,
                      if count > 32 then chunkAt input data count 32 else Word.zero)

/-- The pinned std's decision for `run(uint256 flags, E[] items, uint256 first,
uint256 second)` over raw calldata, written from `do_exec`, the bounded calldata
reader, the lazy calldata-array decoder, `checkArrayHead`, `abiArrayGet` and
the derived decoder. The fallback reverts with `0x4924aef0`, a missing or
out-of-range read with `0x08638556`, an index past the length with
`0x7f52b2bf` and an unknown tag with empty data. The array's head is checked at
dispatch, then `first` and `second` are decoded in turn; unread elements are
never checked. -/
def stdDecode (shape : Shape) (input : ByteArray) : Decision := do
  let size := input.size
  let fail := fun (error : Nat) => (Except.error (selectorBytes error) : Decision)
  let width := EnumArray.stride shape
  if size < 4 || StdCalldata.bigEndian input 0 4 != EnumArray.selector shape then fail noSelectorError
  else if size < 4 + EnumArray.argumentsHead then fail truncatedError
  else
    let offset := StdCalldata.wordAt input 36
    if offset > size - 4 then fail truncatedError
    else
      let position := 4 + offset
      if size - position < 32 then fail truncatedError
      else
        let length := StdCalldata.wordAt input position
        if length > (2 ^ 256 - 1) / width || length * width > size - (position + 32) then fail truncatedError
        else
          let region := position + 32
          let first ← decodeElement shape input region length (StdCalldata.wordAt input 68)
          let second ← decodeElement shape input region length (StdCalldata.wordAt input 100)
          return ⟨wordAt input 4, Word.ofNatModulo length, first, second⟩

/-- std's revert data for a rejected transaction, or none when the body runs. -/
def stdRejection? (shape : Shape) (tx : Transaction) : Option ByteArray :=
  match stdDecode shape (inputBytes shape tx) with
  | .error data => some data
  | .ok _ => none

def calldata (shape : Shape) (tx : Transaction) : String := encodeBytesText (inputBytes shape tx)

def inputData? (shape : Shape) (tx : Transaction) : Option HostStorageDriver.InputData :=
  let bytes := inputBytes shape tx
  if bounded : bytes.size < wordModulus then some ⟨bytes, bounded⟩ else none

/-- Slot zero holds the accumulator, slot one the length and slots two to nine
both decoded elements. -/
def observedSlots : List Word := (List.range EnumArray.slotCount).map Word.ofNatModulo

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

/-- Independent original-Core observation, as for the enum arguments, with each
transaction's malformed calldata as the input. -/
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

/-- One modelled transaction: whether it reverts, its whole output and the
slots it leaves committed. -/
abbrev ModelRow := EnumArgumentExecution.ModelRow

private def elementWords (element : DecodedElement) : List Word :=
  let (w0, w1, w2) := element.words
  [Word.ofNatModulo element.index, w0, w1, w2]

/-- std's decision, then the protocol: `r = step(prior + L + both elements'
index and Words)`, the ten writes, and the flags' parity. A rejection outputs
std's revert data and keeps the prior slots. -/
def modelTransaction (step : Aggregates.CheckedDAG) (shape : Shape) (fuel : Nat)
    (prior : List Word) (transaction : Transaction) : Option ModelRow := do
  match stdDecode shape (inputBytes shape transaction) with
  | .error data => return ⟨true, data, prior⟩
  | .ok decoded =>
      let decodedWords := decoded.length :: elementWords decoded.first ++ elementWords decoded.second
      let result ← EnumArgumentExecution.stepResult step fuel
        (decodedWords.foldl (· + ·) (prior.getD 0 Word.zero))
      if decoded.flags.val % 2 == 1 then return ⟨true, encodeWordBytesBE result, prior⟩
      return ⟨false, encodeWordBytesBE result, result :: decodedWords⟩

/-- The modelled rows of a whole sequence from empty storage. -/
def model (step : Aggregates.CheckedDAG) (shape : Shape) (fuel : Nat)
    (transactions : List Transaction) : Option (List ModelRow) := Id.run do
  let mut slots : List Word := List.replicate EnumArray.slotCount Word.zero
  let mut rows : Array ModelRow := #[]
  for transaction in transactions do
    match modelTransaction step shape fuel slots transaction with
    | some row =>
        rows := rows.push row
        slots := row.slots
    | none => return none
  return some rows.toList

end Solcore.Synthesis.Stateful.EnumArrayExecution
