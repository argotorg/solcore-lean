import Solcore.Synthesis.Core.AggregateDAG
import Solcore.Synthesis.Core.TupleReturn
import Solcore.Synthesis.Core.BytesReturn
import Solcore.Synthesis.Core.EnumReturn
import Solcore.Synthesis.Core.StdDispatch
import Solcore.Core.Wire.Codec.Program
import Solcore.ContractRuntime.CallResumeExecution

/-! Three checked contracts for a parent that calls a child method and decodes
its return data with std. The child `get(uint256 x)` reads `o = slot 0` and
`c = slot 1 + 1`, applies a closed aggregate step `r = step(x + o)`, writes `r`
to slot 0 and `c` to slot 1, and reverts with `r` for an odd `x`. Otherwise it
returns a value built from `r`, `c`, `x`, `o`, `d0 = r·K` and
`d1 = (c·K) xor x`: a static tuple of two to four Words, a `bytes` value of up
to 64 bytes, or a user enum's chosen constructor. Typed, the value goes through
its convention's encoding, which is std's; raw, the child returns the canonical
encoding with one malformation as raw bytes.

The parent is in continuation-passing form for the call-and-resume convention.
Its call phase writes `p + input` to slot 0, `p` the old slot 0, and returns the
target, the child's selector, the input as the argument and the input as its
one kept Word. Its resume phase reads the kept input, the child's status Word
and the return data at base offset 64, takes std's decision on them as std's
`MemoryWordReader` takes `raw_call`'s copy (from 0, with no up-front size check,
every read inside the data), and writes the flag and size, the decoded record
and their sum. A rejection reverts with std's error selector as a Word, or the
Word zero for an unknown tag's empty data; bit 1 of the input reverts with the
sum. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Core.CallReturn

open Solcore.Core (Word)
open Solcore.Core.Wire
open Solcore.ContractRuntime
open Solcore.Synthesis.Core.EnumReturn (Constructor Shape)
open Solcore.Synthesis.Core.StdDispatch (truncatedError)

def childVersion : String := "core-call-return-child-v1"
def parentVersion : String := "core-call-return-parent-v1"

/-- `get(uint256)`, the child's one method. -/
def getSelector : Nat := 0x9507d39a

/-- `run(uint256,uint256)`, the parent's one method. -/
def runSelector : Nat := 0x7357f5d2

/-- The bytes returns' odd multiplier. -/
def multiplier : Nat := BytesReturn.multiplier

/-- The longest `bytes` value. -/
def maxLength : Nat := 64

/-- The Word that stands for an unknown tag's empty revert data. -/
def emptyRevert : Nat := 0

/-- The parent's slots: the accumulator, the flag and size, then the record. -/
def parentSlotCount : Nat := 7

/-- The child's slots: the step result and the call count. -/
def childSlotCount : Nat := 2

private def w (value : Nat) : Word := Word.ofNatModulo value

/-- The child's value: a static tuple of `extra + 2` Words, a `bytes` value,
or a user enum. -/
inductive Kind where
  | tuple (extra : Nat)
  | bytes
  | enum (shape : Shape)
  deriving Repr, BEq, DecidableEq

/-- How raw return data depart from their canonical encoding. -/
inductive Malformation where
  | truncate (kept : Nat)
  | trailing (count pattern : Nat)
  | offset (value : Word)
  | length (value : Word)
  | tag (value : Word)
  | tagCut (value : Word)
  | tail (value : Word)
  | narrow
  deriving Repr, BEq, DecidableEq

/-- The child returns through std's encoder, or raw bytes with one
malformation. -/
inductive Delivery where
  | typed
  | raw (malformation : Malformation)
  deriving Repr, BEq, DecidableEq

/-- What the child returns: the kind, the `bytes` length of the value or of an
enum's `bytes` constructor, the enum's chosen constructor and the delivery. -/
structure Returned where
  kind : Kind
  length : Nat
  choice : Nat
  delivery : Delivery
  deriving Repr, BEq, DecidableEq

/-- The chosen constructor of an enum. -/
def chosen (shape : Shape) (choice : Nat) : Constructor := shape.constructors.getD choice shape.first

namespace Returned

/-- Whether the value carries a `bytes` length Word. -/
def carriesBytes (returned : Returned) : Bool :=
  match returned.kind with
  | .bytes => true
  | .enum shape => (chosen shape returned.choice).payload == .boundedBytes
  | .tuple _ => false

/-- Whether the head holds an offset Word at 0. -/
def hasOffset (returned : Returned) : Bool :=
  match returned.kind with
  | .bytes => true
  | .enum shape => shape.dynamic
  | .tuple _ => false

end Returned

/-! ### The return data as Words -/

/-- A value the child computes. -/
inductive Source where
  | r
  | c
  | x
  | o
  | d0
  | d1
  deriving Repr, BEq, DecidableEq

/-- One Word of the child's return data: a constant, or a value's first
`kept` bytes followed by zeros. -/
inductive Cell where
  | const (value : Word)
  | value (source : Source) (kept : Nat)
  deriving Repr, BEq, DecidableEq

/-- A `bytes` payload's Words: the first `length` bytes of `d0 ‖ d1`. -/
def payloadCells (length : Nat) : List Cell :=
  (if length > 0 then [.value .d0 (min length 32)] else []) ++
    (if length > 32 then [.value .d1 (length - 32)] else [])

/-- The head of an enum's body: the tag Word and the widest constructor's
fields. -/
def bodyHead (shape : Shape) : Nat := CoreContractEntryProfile.enumBodyHeadSize shape.payloads

/-- A constructor's fields in the head; a `bytes` field is its tail offset,
relative to the body. -/
def headCells (head : Nat) : EnumPayload → List Cell
  | .noWords => []
  | .oneWord => [.value .d0 32]
  | .twoWords => [.value .d0 32, .value .d1 32]
  | .boundedBytes => [.const (w head)]

/-- An enum's body: the tag, the fields, zero Words up to the head, then a
`bytes` field's length Word and payload. -/
def bodyCells (shape : Shape) (length choice : Nat) : List Cell :=
  let constructor := chosen shape choice
  [.const (EnumReturn.tag constructor)] ++ headCells (bodyHead shape) constructor.payload ++
    List.replicate ((bodyHead shape - 32 - CoreContractEntryProfile.enumPayloadHeadSize constructor.payload) / 32)
      (.const Word.zero) ++
    (if constructor.payload == .boundedBytes then [.const (w length)] ++ payloadCells length else [])

/-- std's canonical encoding as Words. -/
def canonicalCells (returned : Returned) : List Cell :=
  match returned.kind with
  | .tuple extra => [.value .r 32, .value .c 32, .value .x 32, .value .o 32].take (extra + 2)
  | .bytes => [.const (w 32), .const (w returned.length)] ++ payloadCells returned.length
  | .enum shape => (if shape.dynamic then [.const (w 32)] else []) ++ bodyCells shape returned.length returned.choice

def canonicalSize (returned : Returned) : Nat := 32 * (canonicalCells returned).length

/-- The position of the `bytes` length Word: the value's at 32, or a dynamic
enum's `bytes` constructor's after the offset Word and the body's head. -/
def lengthPosition (returned : Returned) : Nat :=
  match returned.kind with
  | .enum shape => 32 + bodyHead shape
  | _ => 32

/-- The tag's position: inline at 0, or after a dynamic enum's offset Word. -/
def tagPosition (shape : Shape) : Nat := if shape.dynamic then 32 else 0

/-- A dynamic enum's `bytes` tail offset, after the offset Word and the tag. -/
def tailPosition : Nat := 64

/-- A static enum cut to the chosen constructor's head. -/
def narrowedSize (shape : Shape) (choice : Nat) : Nat :=
  32 + CoreContractEntryProfile.enumPayloadHeadSize (chosen shape choice).payload

/-- Trailing bytes: zeros (0), `0xff` (1) or the ramp `1, 2, 3, ...` (2). -/
def patternByte (pattern position : Nat) : Nat :=
  match pattern with
  | 0 => 0
  | 1 => 0xff
  | _ => (position + 1) % 256

/-- `count` pattern bytes as Words, the last one zero-padded. -/
def patternCells (count pattern : Nat) : List Cell :=
  (List.range ((count + 31) / 32)).map fun index =>
    .const (w ((List.range 32).foldl (fun total byte =>
      total * 256 + if 32 * index + byte < count then patternByte pattern (32 * index + byte) else 0) 0))

/-- Whether a malformation applies, within its bounds. -/
def Malformation.valid (returned : Returned) : Malformation → Bool
  | .truncate kept => kept < canonicalSize returned
  | .trailing count pattern => 1 ≤ count && count ≤ 64 && pattern < 3
  | .offset value => returned.hasOffset && value.val != 32
  | .length value => returned.carriesBytes && value.val != returned.length
  | .tag value | .tagCut value => match returned.kind with
      | .enum shape => !shape.constructors.any (EnumReturn.tag · == value)
      | _ => false
  | .tail value => match returned.kind with
      | .enum shape => shape.dynamic && returned.carriesBytes && value.val != bodyHead shape
      | _ => false
  | .narrow => match returned.kind with
      | .enum shape => !shape.dynamic && narrowedSize shape returned.choice < canonicalSize returned
      | _ => false

/-- The returned Words and the size the child returns. -/
def returnedCells (returned : Returned) : List Cell × Nat :=
  let cells := canonicalCells returned
  let size := canonicalSize returned
  match returned.delivery with
  | .typed => (cells, size)
  | .raw malformation =>
      let tag := match returned.kind with
        | .enum shape => tagPosition shape
        | _ => 0
      match malformation with
      | .truncate kept => (cells.take ((kept + 31) / 32), kept)
      | .trailing count pattern => (cells ++ patternCells count pattern, size + count)
      | .offset value => (cells.set 0 (.const value), size)
      | .length value => (cells.set (lengthPosition returned / 32) (.const value), size)
      | .tag value => (cells.set (tag / 32) (.const value), size)
      | .tagCut value => ((cells.set (tag / 32) (.const value)).take (tag / 32 + 1), tag + 32)
      | .tail value => (cells.set (tailPosition / 32) (.const value), size)
      | .narrow => match returned.kind with
          | .enum shape => (cells.take (narrowedSize shape returned.choice / 32), narrowedSize shape returned.choice)
          | _ => (cells, size)

/-- A raw child's data Words, at least one. -/
def rawCells (returned : Returned) : List Cell :=
  match (returnedCells returned).1 with
  | [] => [.const Word.zero]
  | cells => cells

def rawExtraWords (returned : Returned) : Nat := (rawCells returned).length - 1

/-- Two to four Words, a `bytes` length of at most 64, a valid enum shape with
a chosen constructor, unused fields zero, and a malformation that applies. -/
def Returned.valid (returned : Returned) : Bool :=
  returned.length ≤ maxLength &&
  (match returned.kind with
    | .tuple extra => extra ≤ 2 && returned.length == 0 && returned.choice == 0
    | .bytes => returned.choice == 0
    | .enum shape => decide shape.Valid && returned.choice < shape.constructors.length &&
        ((chosen shape returned.choice).payload == .boundedBytes || returned.length == 0)) &&
  (match returned.delivery with
    | .typed => true
    | .raw malformation => malformation.valid returned)

/-! ### A binder-level builder for de Bruijn Core expressions -/

/-- An expression at a binder depth. -/
private abbrev B := Nat → Expr

private def bvar (level : Nat) : B := fun depth => .var (depth - 1 - level)
private def bword (value : Nat) : B := fun _ => .word (w value)
private def bconst (value : Word) : B := fun _ => .word value
private def bunit : B := fun _ => .unit
private def bhost (index : Nat) (argument : B) : B := fun depth => .apply (.var (index + depth)) (argument depth)
private def bapply (function argument : B) : B := fun depth => .apply (function depth) (argument depth)
private def blet (value : B) (body : Nat → B) : B := fun depth => .letE (value depth) (body depth (depth + 1))
private def bcond (condition yes no : B) : B := fun depth => .ifE (condition depth) (yes depth) (no depth)
private def bcase (scrutinee : B) (left right : Nat → B) : B := fun depth =>
  .caseE (scrutinee depth) (left depth (depth + 1)) (right depth (depth + 1))
private def bbinary (operator : BinaryOp) (left right : B) : B := fun depth =>
  .binary operator (left depth) (right depth)
private def bpair (left right : B) : B := fun depth => .pair (left depth) (right depth)
private def binLeft (type : Ty) (value : B) : B := fun depth => .inLeft type (value depth)
private def binRight (type : Ty) (value : B) : B := fun depth => .inRight type (value depth)
private def bfirst (value : B) : B := fun depth => .first (value depth)
private def bsecond (value : B) : B := fun depth => .second (value depth)

private def badd (left right : B) : B := bbinary .wordAdd left right
private def bsub (left right : B) : B := bbinary .wordSub left right
private def bgt (left right : B) : B := bbinary .wordGt left right
private def beq (left right : B) : B := bbinary .wordEq left right
private def bbitSet (value : B) (bit : Nat) : B := beq (bbinary .wordAnd value (bword bit)) (bword bit)

private def sload (slot : Nat) : B := bhost 0 (bword slot)
private def sstore (slot : Nat) (value : B) : B := bhost 1 (bpair (bword slot) value)
private def inputSize : B := bhost 7 bunit
/-- The input Word at a byte offset; an absent Word reads as zero, which the
checks before every read never reach. -/
private def readAt (offset : B) : B := bcase (bhost 8 offset) (fun _ => bword 0) (fun value => bvar value)

/-- Right-nested pairs of the values. -/
private def btuple : List B → B
  | [] => bunit
  | [value] => value
  | value :: rest => bpair value (btuple rest)

/-! ### The child -/

/-- The levels of the child's values. -/
private structure Values where
  r : Nat
  c : Nat
  x : Nat
  o : Nat
  d0 : Nat
  d1 : Nat

private def sourceLevel (values : Values) : Source → Nat
  | .r => values.r
  | .c => values.c
  | .x => values.x
  | .o => values.o
  | .d0 => values.d0
  | .d1 => values.d1

/-- The first `kept` bytes of a Word. -/
def keepMask (kept : Nat) : Nat := (2 ^ (8 * kept) - 1) * 2 ^ (8 * (32 - kept))

private def cellValue (values : Values) : Cell → B
  | .const value => bconst value
  | .value source kept =>
      if kept ≥ 32 then bvar (sourceLevel values source)
      else bbinary .wordAnd (bvar (sourceLevel values source)) (bword (keepMask kept))

/-- The Wire type of the child's returned side. -/
def childReturnedType (returned : Returned) : Ty :=
  match returned.delivery with
  | .raw _ => .product .unit (.product .word (TupleReturn.wordTuple (rawExtraWords returned)))
  | .typed => match returned.kind with
    | .tuple extra => TupleReturn.wordTuple (extra + 1)
    | .bytes => BytesReturn.bytesType
    | .enum shape => EnumReturn.returnedType shape

/-- The child's entry convention. -/
def childProfile (returned : Returned) : CoreContractEntryProfile :=
  match returned.delivery with
  | .raw _ => .rawBytesOutcomeV1 (rawExtraWords returned)
  | .typed => match returned.kind with
    | .tuple extra => .wordTupleOutcomeV1 extra
    | .bytes => .boundedBytesOutcomeV1
    | .enum shape => shape.profile

def childResultType (returned : Returned) : Ty := .sum (childReturnedType returned) (.sum .word .word)

theorem childResultType_toCore (returned : Returned) :
    (childResultType returned).toCore = (childProfile returned).resultType := by
  rcases returned with ⟨kind, length, choice, delivery⟩
  cases delivery with
  | raw malformation =>
      simp [childResultType, childReturnedType, childProfile, Ty.toCore, TupleReturn.wordTuple_toCore,
        CoreContractEntryProfile.resultType, CoreContractEntryProfile.rawBytesType]
  | typed =>
      cases kind with
      | tuple extra =>
          simp [childResultType, childReturnedType, childProfile, Ty.toCore, TupleReturn.wordTuple_toCore,
            CoreContractEntryProfile.resultType]
      | bytes => rfl
      | enum shape =>
          simp [childResultType, childReturnedType, childProfile, Ty.toCore, EnumReturn.returnedType,
            EnumReturn.enumType_toCore, Shape.profile, CoreContractEntryProfile.resultType]

/-- A typed `bytes` value of the plan's length: empty, or the tag `L - 1` with
`d0` and `d1`. -/
private def bytesValue (values : Values) (length : Nat) : B :=
  if length = 0 then binLeft BytesReturn.dataType bunit
  else binRight .unit (bpair (bword (length - 1)) (bpair (bvar values.d0) (bvar values.d1)))

/-- A constructor's value: its tag and fields. -/
private def constructorValue (values : Values) (length : Nat) (constructor : Constructor) : B :=
  bpair (bconst (EnumReturn.tag constructor)) (match constructor.payload with
    | .noWords => bunit
    | .oneWord => bvar values.d0
    | .twoWords => bpair (bvar values.d0) (bvar values.d1)
    | .boundedBytes => bytesValue values length)

/-- Constructor `index` of the constructors from `constructor` on, injected
into their right-nested sum. -/
private def inject (values : Values) (length : Nat) : Nat → Constructor → List Constructor → B
  | _, constructor, [] => constructorValue values length constructor
  | 0, constructor, next :: rest =>
      binLeft (EnumReturn.enumType next.payload (rest.map Constructor.payload)) (constructorValue values length constructor)
  | index + 1, constructor, next :: rest =>
      binRight (EnumReturn.payloadType constructor.payload) (inject values length index next rest)

/-- The returned side's value over `d0` and `d1`. -/
private def valueOf (returned : Returned) (values : Values) : B :=
  match returned.delivery with
  | .raw _ =>
      bpair bunit (bpair (bword (returnedCells returned).2) (btuple ((rawCells returned).map (cellValue values))))
  | .typed => match returned.kind with
    | .tuple extra => btuple ([values.r, values.c, values.x, values.o].take (extra + 2) |>.map bvar)
    | .bytes => bytesValue values returned.length
    | .enum shape =>
        inject values returned.length (returned.choice % shape.constructors.length) shape.first
          (shape.second :: shape.rest)

/-- The returned value: `d0 = r·K` and `d1 = (c·K) xor x`, then the value. -/
private def childValue (returned : Returned) (r c x o : Nat) : B :=
  blet (bbinary .wordMul (bvar r) (bword multiplier)) fun d0 =>
  blet (bbinary .wordXor (bbinary .wordMul (bvar c) (bword multiplier)) (bvar x)) fun d1 =>
  valueOf returned ⟨r, c, x, o, d0, d1⟩

/-- The child with `value` in place of its returned value: the step at level 0,
then `x`, `o`, `c`, `r`, the two writes, and the odd-`x` revert. -/
private def childBody (returned : Returned) (stepBody : Expr) (value : Nat → Nat → Nat → Nat → B) : B :=
  blet (fun _ => stepBody) fun step =>
  blet (readAt (bword 4)) fun x =>
  blet (sload 0) fun o =>
  blet (badd (sload 1) (bword 1)) fun c =>
  blet (bapply (bvar step) (badd (bvar x) (bvar o))) fun r =>
  blet (sstore 0 (bvar r)) fun _ =>
  blet (sstore 1 (bvar c)) fun _ =>
  bcond (bbitSet (bvar x) 1)
    (binRight (childReturnedType returned) (binLeft .word (bvar r)))
    (binLeft (.sum .word .word) (value r c x o))

def childProgramOf (returned : Returned) (stepBody : Expr) : Program := {
  resultType := childResultType returned
  dataDefinitions := []
  body := childBody returned stepBody (childValue returned) 0
}

/-- The child's shell, the step and its returned value apart: measured with a
one-node placeholder step and a Unit value, which are never admitted or run. -/
def childShellNodes (returned : Returned) : Nat :=
  let shell : Program :=
    { resultType := childResultType returned
      dataDefinitions := []
      body := childBody returned (.word Word.zero) (fun _ _ _ _ => bunit) 0 }
  let placeholder : Program := { resultType := .function .word .word, dataDefinitions := [], body := .word Word.zero }
  programNodes shell - programNodes placeholder

/-! ### The parent -/

/-- The call phase's request: the target, the selector, the argument and the
kept input. -/
def callResultType : Ty := .sum (TupleReturn.wordTuple 3) (.sum .word .word)

/-- Read the target at 4 and the input at 36, write `p + input` to slot 0,
then return the request. -/
private def callBody : B :=
  blet (readAt (bword 4)) fun target =>
  blet (readAt (bword 36)) fun input =>
  blet (sload 0) fun prior =>
  blet (sstore 0 (badd (bvar prior) (bvar input))) fun _ =>
  binLeft (.sum .word .word) (btuple [bvar target, bword getSelector, bvar input, bvar input])

def callProgram : Program := {
  resultType := callResultType
  dataDefinitions := []
  body := callBody 0
}

/-- The decoded record: the constructor index and four Words. -/
def recordType : Ty := .product .word (.product .word (.product .word (.product .word .word)))

private def decoded : Ty := .sum recordType .word

private def reject (error : Nat) : B := binRight recordType (bword error)

private def record (index first second third fourth : B) : B :=
  binLeft .word (bpair index (bpair first (bpair second (bpair third fourth))))

/-- The return data start after the kept input and the status Word. -/
def base : Nat := 64

/-- Keep the first `remaining` bytes of a Word: all from 32 on, none for zero. -/
private def bmask (remaining : B) : B :=
  fun depth => .unary .wordNot (.binary .wordShr (.word (w (2 ^ 256 - 1))) (.binary .wordMul (.word (w 8)) (remaining depth)))

/-- Payload chunk `index` of a payload at absolute `data` of `length` bytes,
when the length exceeds the chunk's start: the payload Word masked to the
payload when all its bytes exist, otherwise the Word ending at the payload's
last byte shifted to the chunk's start. -/
private def chunk (size data length : Nat) (index : Nat) : B :=
  bcond (bgt (bvar length) (bword (32 * index)))
    (bcond (bgt (badd (bvar data) (bword (32 * index + 32))) (bvar size))
      (bbinary .wordShl (readAt (bsub (badd (bvar data) (bvar length)) (bword 32)))
        (bbinary .wordMul (bword 8) (bsub (bword (32 * (index + 1))) (bvar length))))
      (bbinary .wordAnd (readAt (badd (bvar data) (bword (32 * index))))
        (bmask (bsub (bvar length) (bword (32 * index))))))
    (bword 0)

/-- A `bytes` value whose tail offset Word lies at `start + head`, its offset
relative to `start`, within `room` bytes from `start`: the offset `t <= room`,
the length Word at `start + t` and a length that fits after it. -/
private def bytesAt (size start room : Nat) (head : Nat) (finish : Nat → Nat → Nat → B) : B :=
  bcond (bgt (bword (head + 32)) (bvar room)) (reject truncatedError)
    (blet (readAt (badd (bvar start) (bword head))) fun tail =>
     bcond (bgt (bvar tail) (bvar room)) (reject truncatedError)
       (bcond (bgt (bword 32) (bsub (bvar room) (bvar tail))) (reject truncatedError)
         (blet (readAt (badd (bvar start) (bvar tail))) fun length =>
          bcond (bgt (bvar length) (bsub (bsub (bvar room) (bvar tail)) (bword 32))) (reject truncatedError)
            (blet (badd (badd (bvar start) (bvar tail)) (bword 32)) fun data =>
              finish size data length))))

/-- The chosen constructor's fields in a body at absolute `start` with `room`
bytes, as the record. -/
private def fields (size start room : Nat) (index : Nat) : EnumPayload → B
  | .noWords => record (bword index) (bword 0) (bword 0) (bword 0) (bword 0)
  | .oneWord =>
      bcond (bgt (bword 64) (bvar room)) (reject truncatedError)
        (record (bword index) (readAt (badd (bvar start) (bword 32))) (bword 0) (bword 0) (bword 0))
  | .twoWords =>
      bcond (bgt (bword 96) (bvar room)) (reject truncatedError)
        (record (bword index) (readAt (badd (bvar start) (bword 32))) (readAt (badd (bvar start) (bword 64)))
          (bword 0) (bword 0))
  | .boundedBytes =>
      bytesAt size start room 32 fun size data length =>
        record (bword index) (bvar length) (chunk size data length 0) (chunk size data length 1) (bword 0)

/-- The tag at `start` against each constructor's tag in declaration order; no
match is the unknown tag's empty data. -/
private def dispatch (size start room tag : Nat) : Nat → List Constructor → B
  | _, [] => reject emptyRevert
  | index, constructor :: rest =>
      bcond (beq (bvar tag) (bconst (EnumReturn.tag constructor))) (fields size start room index constructor.payload)
        (dispatch size start room tag (index + 1) rest)

/-- An enum body at absolute `start` with `room` bytes: the tag must exist. -/
private def enumAt (shape : Shape) (size start room : Nat) : B :=
  bcond (bgt (bword 32) (bvar room)) (reject truncatedError)
    (blet (readAt (bvar start)) fun tag => dispatch size start room tag 1 shape.constructors)

/-- std's decision on the return data of `m` bytes at `base`, as the record or
the revert Word. -/
private def decoder (kind : Kind) (size m : Nat) : B :=
  match kind with
  | .tuple extra =>
      let count := extra + 2
      bcond (bgt (bword (32 * count)) (bvar m)) (reject truncatedError)
        (record (bword 0) (readAt (bword base)) (readAt (bword (base + 32)))
          (if count > 2 then readAt (bword (base + 64)) else bword 0)
          (if count > 3 then readAt (bword (base + 96)) else bword 0))
  | .bytes =>
      blet (bword base) fun start =>
      bytesAt size start m 0 fun size data length =>
        record (bword 0) (bvar length) (chunk size data length 0) (chunk size data length 1) (bword 0)
  | .enum shape =>
      if shape.dynamic then
        bcond (bgt (bword 32) (bvar m)) (reject truncatedError)
          (blet (readAt (bword base)) fun offset =>
           bcond (bgt (bvar offset) (bvar m)) (reject truncatedError)
             (blet (badd (bword base) (bvar offset)) fun start =>
              blet (bsub (bvar m) (bvar offset)) fun room =>
              enumAt shape size start room))
      else
        blet (bword base) fun start => enumAt shape size start m

/-- The resume phase over the kept input, the status Word and the return data:
the record when the child returned and std accepts its data, or the revert
Word, or for another status the revert data's first Word; then the writes, the
sum and bit 1's revert. -/
private def resumeBody (kind : Kind) : B :=
  blet inputSize fun size =>
  blet (readAt (bword 0)) fun input =>
  blet (readAt (bword 32)) fun status =>
  blet (bsub (bvar size) (bword base)) fun m =>
  blet (beq (bvar status) (bword 1)) fun ok =>
  bcase
    (bcond (bvar ok) (decoder kind size m)
      (record (bword 0) (bcond (bgt (bword 32) (bvar m)) (bword 0) (readAt (bword base))) (bword 0) (bword 0) (bword 0)))
    (fun record =>
      blet (sstore 1 (badd (bcond (bvar ok) (bword 1) (bword 0)) (bbinary .wordMul (bword 2) (bvar m)))) fun _ =>
      blet (sstore 2 (bfirst (bvar record))) fun _ =>
      blet (sstore 3 (bfirst (bsecond (bvar record)))) fun _ =>
      blet (sstore 4 (bfirst (bsecond (bsecond (bvar record))))) fun _ =>
      blet (sstore 5 (bfirst (bsecond (bsecond (bsecond (bvar record)))))) fun _ =>
      blet (sstore 6 (bsecond (bsecond (bsecond (bsecond (bvar record)))))) fun _ =>
      blet (badd (badd (badd (badd (badd (sload 0) (bfirst (bvar record))) (bfirst (bsecond (bvar record))))
          (bfirst (bsecond (bsecond (bvar record))))) (bfirst (bsecond (bsecond (bsecond (bvar record))))))
          (bsecond (bsecond (bsecond (bsecond (bvar record)))))) fun sum =>
      bcond (bbitSet (bvar input) 2)
        (binRight .word (binLeft .word (bvar sum)))
        (binLeft (.sum .word .word) (bvar sum)))
    (fun error => binRight .word (binLeft .word (bvar error)))

def resumeResultType : Ty := .sum .word (.sum .word .word)

def resumeProgram (kind : Kind) : Program := {
  resultType := resumeResultType
  dataDefinitions := []
  body := resumeBody kind 0
}

def callNodes : Nat := programNodes callProgram
def resumeNodes (kind : Kind) : Nat := programNodes (resumeProgram kind)

/-- Every contract is bounded by 1,024 nodes. -/
def maxContractNodes : Nat := 1024

/-! ### The checked plan -/

structure CheckedPlan where private mk ::
  step : Aggregates.CheckedDAG
  returned : Returned
  valid : returned.valid = true
  childChecked : (childProgramOf returned step.program.body).check = true
  callChecked : callProgram.check = true
  resumeChecked : (resumeProgram returned.kind).check = true

namespace CheckedPlan

def childProgram (plan : CheckedPlan) : Program := childProgramOf plan.returned plan.step.program.body
def callProgram (_plan : CheckedPlan) : Program := CallReturn.callProgram
def resumeProgram (plan : CheckedPlan) : Program := CallReturn.resumeProgram plan.returned.kind

def ofParts? (step : Aggregates.CheckedDAG) (returned : Returned) : Option CheckedPlan :=
  if valid : returned.valid = true then
    if childChecked : (childProgramOf returned step.program.body).check = true then
      if callChecked : CallReturn.callProgram.check = true then
        if resumeChecked : (CallReturn.resumeProgram returned.kind).check = true then
          some ⟨step, returned, valid, childChecked, callChecked, resumeChecked⟩
        else none
      else none
    else none
  else none

theorem childWellTyped (plan : CheckedPlan) : plan.childProgram.WellTyped :=
  Program.check_full_sound plan.childChecked

theorem callWellTyped (plan : CheckedPlan) : plan.callProgram.WellTyped :=
  Program.check_full_sound plan.callChecked

theorem resumeWellTyped (plan : CheckedPlan) : plan.resumeProgram.WellTyped :=
  Program.check_full_sound plan.resumeChecked

def childCode (plan : CheckedPlan) : CheckedHostCoreProgram :=
  ⟨plan.childProgram.toCore, Program.check_promotes_current plan.childChecked⟩

def callCode (plan : CheckedPlan) : CheckedHostCoreProgram :=
  ⟨plan.callProgram.toCore, Program.check_promotes_current plan.callChecked⟩

def resumeCode (plan : CheckedPlan) : CheckedHostCoreProgram :=
  ⟨plan.resumeProgram.toCore, Program.check_promotes_current plan.resumeChecked⟩

def childContract (plan : CheckedPlan) : CheckedCoreContract :=
  ⟨plan.childCode, childProfile plan.returned, childResultType_toCore plan.returned⟩

def callContract (plan : CheckedPlan) : CheckedCoreContract :=
  CheckedCoreContract.wordTupleOutcomeV1 plan.callCode 2 (by
    change callResultType.toCore = _
    simp [callResultType, Ty.toCore, TupleReturn.wordTuple_toCore, CoreContractEntryProfile.resultType])

def resumeContract (plan : CheckedPlan) : CheckedCoreContract :=
  CheckedCoreContract.wordOutcomeV1 plan.resumeCode rfl

/-- The parent in continuation-passing form, keeping the input. -/
def parent (plan : CheckedPlan) : CallResumeParent := {
  call := plan.callContract
  resume := plan.resumeContract
  keptWords := 1
  call_entryProfile := rfl
  resume_entryProfile := rfl
}

theorem childContract_program (plan : CheckedPlan) :
    plan.childContract.code.program = plan.childProgram.toCore := rfl

theorem childContract_entryProfile (plan : CheckedPlan) :
    plan.childContract.entryProfile = childProfile plan.returned := rfl

end CheckedPlan
end Solcore.Synthesis.Core.CallReturn
