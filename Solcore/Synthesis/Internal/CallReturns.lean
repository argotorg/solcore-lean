import Solcore.Core.Primitive
import Solcore.Core.Wire.Codec
import Solcore.Synthesis.Internal.Aggregates
import Solcore.Synthesis.Internal.AbiReturns
import Solcore.Synthesis.Internal.EnumAbi
import Solcore.Synthesis.Core.StdDispatch
import Solcore.ContractRuntime.Internal.CallPhaseLaws
import Solcore.Synthesis.Internal.Calls
import Solcore.Synthesis.Stateful.Sequence
import Solcore.Synthesis.Internal.Storage

/-!
# Profiles: call returns, sequences, branches

The profiles `stateful-call-returns`, `stateful-call-sequences` and `stateful-call-branches`.
-/

section
-- leanmerge: from Solcore.Synthesis.Core.CallBuilder
/-! A binder-level builder for de Bruijn Core expressions, shared by the call
profiles' contracts: an expression is built at its binder depth, so a binder's
level names it from inside any later binder. The host functions are the
storage read and write, the input size and the input Word at a byte offset. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Core.CallBuilder

open Solcore.Core (Word)
open Solcore.Core.Wire

private def w (value : Nat) : Word := Word.ofNatModulo value

/-- An expression at a binder depth. -/
abbrev B := Nat → Expr

def bvar (level : Nat) : B := fun depth => .var (depth - 1 - level)
def bword (value : Nat) : B := fun _ => .word (w value)
def bconst (value : Word) : B := fun _ => .word value
def bunit : B := fun _ => .unit
def bhost (index : Nat) (argument : B) : B := fun depth => .apply (.var (index + depth)) (argument depth)
def bapply (function argument : B) : B := fun depth => .apply (function depth) (argument depth)
def blam (parameter result : Ty) (body : Nat → B) : B := fun depth =>
  .lambda parameter result (body depth (depth + 1))
def blet (value : B) (body : Nat → B) : B := fun depth => .letE (value depth) (body depth (depth + 1))
def bcond (condition yes no : B) : B := fun depth => .ifE (condition depth) (yes depth) (no depth)
def bcase (scrutinee : B) (left right : Nat → B) : B := fun depth =>
  .caseE (scrutinee depth) (left depth (depth + 1)) (right depth (depth + 1))
def bbinary (operator : BinaryOp) (left right : B) : B := fun depth =>
  .binary operator (left depth) (right depth)
def bpair (left right : B) : B := fun depth => .pair (left depth) (right depth)
def binLeft (type : Ty) (value : B) : B := fun depth => .inLeft type (value depth)
def binRight (type : Ty) (value : B) : B := fun depth => .inRight type (value depth)
def bfirst (value : B) : B := fun depth => .first (value depth)
def bsecond (value : B) : B := fun depth => .second (value depth)

def badd (left right : B) : B := bbinary .wordAdd left right
def bsub (left right : B) : B := bbinary .wordSub left right
def bgt (left right : B) : B := bbinary .wordGt left right
def beq (left right : B) : B := bbinary .wordEq left right
def bbitSet (value : B) (bit : Nat) : B := beq (bbinary .wordAnd value (bword bit)) (bword bit)

def sload (slot : Nat) : B := bhost 0 (bword slot)
def sstore (slot : Nat) (value : B) : B := bhost 1 (bpair (bword slot) value)
def inputSize : B := bhost 7 bunit
/-- The input Word at a byte offset; an absent Word reads as zero, which the
checks before every read never reach. -/
def readAt (offset : B) : B := bcase (bhost 8 offset) (fun _ => bword 0) (fun value => bvar value)

/-- Right-nested pairs of the values. -/
def btuple : List B → B
  | [] => bunit
  | [value] => value
  | value :: rest => bpair value (btuple rest)

end Solcore.Synthesis.Core.CallBuilder
end

section
-- leanmerge: from Solcore.Synthesis.Core.CallReturn
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
open Solcore.Synthesis.Core.CallBuilder

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
end

section
-- leanmerge: from Solcore.Synthesis.Core.CallSequence
/-! Checked contracts for a parent that calls a child two or three times in one
method and measures the latest return data around each call. The child
`get(uint256 x)` reads `o = slot 0` and `c = slot 1 + 1`, applies a closed
aggregate step `r = step(x + o)` and writes `r` to slot 0 and `c` to slot 1.
With the class byte `b = x mod 256` and `L = min(b >> 1, 96)`, its data are the
first `L` bytes of `d0 ‖ d1 ‖ d2`, where `d0 = r·K`, `d1 = (c·K) xor x` and
`d2 = d0 xor d1`: reverted when `b` is odd, otherwise returned, both raw.

The parent is in continuation-passing form for the call chain. Its call phase
writes `p + input` to slot 0 and `z = 0` to slot 1, and requests call 1 with
`mix·256 + b_1`, where `mix = input >> 32` and `b_k` is the input's byte
`k - 1`. It keeps seven Words: the target, the input, `mix`, the running sum,
the size the next call's preceding `returndatasize` reads, call 1's copy's
first Word and whether call 1's data have a whole Word. Each later phase reads
the kept Words, the status Word and the call's data at base 256, writes the
call's flag and size, first Word, preceding size, size and window, and either
requests the next call with the size as the next preceding one, or, as the
last phase, writes call 1's first Word re-read once per later call and reverts
with the sum under the input's bit 24, or returns it. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Core.CallSequence

open Solcore.Core (Word)
open Solcore.Core.Wire
open Solcore.ContractRuntime
open Solcore.Synthesis.Core.CallBuilder

def childVersion : String := "core-call-sequence-child-v1"
def parentVersion : String := "core-call-sequence-parent-v1"

/-- `get(uint256)`, the child's one method. -/
def getSelector : Nat := CallReturn.getSelector

/-- The bytes returns' odd multiplier. -/
def multiplier : Nat := CallReturn.multiplier

/-- The child's longest data: three Words. -/
def capacity : Nat := 96

/-- The widest window: one Word. -/
def maxWidth : Nat := 32

/-- The Words each requesting phase keeps: the target, the input, `mix`, the
running sum, the next preceding size, call 1's first Word and whether call 1's
data have a whole Word. -/
def keptWords : Nat := 7

/-- The return data start after the kept Words and the status Word. -/
def base : Nat := 32 * (keptWords + 1)

/-- The parent's slots for `calls` calls: the accumulator, `z`, five per call
and the re-read. -/
def parentSlotCount (calls : Nat) : Nat := 5 * calls + 3

/-- The child's slots: the step result and the call count. -/
def childSlotCount : Nat := 2

private def w (value : Nat) : Word := Word.ofNatModulo value

/-- A window of `width` bytes at `offset` in a call's data. -/
structure Window where
  offset : Nat
  width : Nat
  deriving Repr, BEq, DecidableEq

def Window.valid (window : Window) : Bool := window.offset ≤ capacity && window.width ≤ maxWidth

/-- Two or three calls, each with a valid window. -/
def validWindows (windows : List Window) : Bool :=
  (windows.length == 2 || windows.length == 3) && windows.all Window.valid

/-! ### The child -/

/-- The raw data side: a unit marker, the length Word and three data Words. -/
def rawType : Ty := .product .unit (.product .word (TupleReturn.wordTuple 2))

def childResultType : Ty := .sum rawType (.sum rawType .word)

theorem childResultType_toCore :
    childResultType.toCore = (CoreContractEntryProfile.rawOutcomeV1 2).resultType := by
  simp [childResultType, rawType, Ty.toCore, TupleReturn.wordTuple_toCore,
    CoreContractEntryProfile.resultType, CoreContractEntryProfile.rawBytesType]

private def band (left right : B) : B := bbinary .wordAnd left right
private def bmul (left right : B) : B := bbinary .wordMul left right
private def bxor (left right : B) : B := bbinary .wordXor left right
private def bshr (value : B) (shift : Nat) : B := bbinary .wordShr value (bword shift)

/-- The child with `step` at level 0, then `x`, `o`, `c`, `r`, the two writes,
the length and the three data Words. -/
private def childBody (stepBody : Expr) : B :=
  blet (fun _ => stepBody) fun step =>
  blet (readAt (bword 4)) fun x =>
  blet (sload 0) fun o =>
  blet (badd (sload 1) (bword 1)) fun c =>
  blet (bapply (bvar step) (badd (bvar x) (bvar o))) fun r =>
  blet (sstore 0 (bvar r)) fun _ =>
  blet (sstore 1 (bvar c)) fun _ =>
  blet (bshr (band (bvar x) (bword 255)) 1) fun half =>
  blet (bcond (bgt (bvar half) (bword capacity)) (bword capacity) (bvar half)) fun length =>
  blet (bmul (bvar r) (bword multiplier)) fun d0 =>
  blet (bxor (bmul (bvar c) (bword multiplier)) (bvar x)) fun d1 =>
  blet (bxor (bvar d0) (bvar d1)) fun d2 =>
  let data := bpair bunit (bpair (bvar length) (btuple [bvar d0, bvar d1, bvar d2]))
  bcond (bbitSet (bvar x) 1)
    (binRight rawType (binLeft .word data))
    (binLeft (.sum rawType .word) data)

def childProgramOf (stepBody : Expr) : Program := {
  resultType := childResultType
  dataDefinitions := []
  body := childBody stepBody 0
}

/-- The child's shell, the step apart: measured with a one-node placeholder
step, which is never admitted or run. -/
def childShellNodes : Nat :=
  let placeholder : Program := { resultType := .function .word .word, dataDefinitions := [], body := .word Word.zero }
  programNodes (childProgramOf (.word Word.zero)) - programNodes placeholder

/-! ### The parent -/

/-- A requesting phase's result: the target, the selector, the argument and the
kept Words. -/
def requestType : Ty := .sum (TupleReturn.wordTuple (keptWords + 2)) (.sum .word .word)

/-- The argument of call `k`, from zero: `mix·256` plus the input's byte `k`. -/
private def argument (mix input : Nat) (call : Nat) : B :=
  badd (bmul (bvar mix) (bword 256)) (band (bshr (bvar input) (8 * call)) (bword 255))

/-- The request for call `call` and the kept Words. -/
private def request (target input mix sum previous copy whole : B) (call : Nat) (mixLevel inputLevel : Nat) : B :=
  binLeft (.sum .word .word) (btuple [target, bword getSelector, argument mixLevel inputLevel call,
    target, input, mix, sum, previous, copy, whole])

/-- Read the target at 4 and the input at 36, write `p + input` to slot 0 and
`z = 0` to slot 1, then request call 1. -/
private def callBody : B :=
  blet (readAt (bword 4)) fun target =>
  blet (readAt (bword 36)) fun input =>
  blet (badd (sload 0) (bvar input)) fun accumulator =>
  blet (sstore 0 (bvar accumulator)) fun _ =>
  blet (sstore 1 (bword 0)) fun _ =>
  blet (bshr (bvar input) 32) fun mix =>
  request (bvar target) (bvar input) (bvar mix) (bvar accumulator) (bword 0) (bword 0) (bword 0) 0 mix input

def callProgram : Program := {
  resultType := requestType
  dataDefinitions := []
  body := callBody 0
}

/-- The data's bytes `offset` to `offset + width - 1`, left-aligned in a zero
Word, when they lie inside the `m` bytes at `base`, and otherwise zero: the
Word at `base + offset` when it exists, otherwise the Word ending at the data's
last byte shifted to the offset, then masked to the width. -/
private def window (window : Window) (m : Nat) : B :=
  bcond (bgt (bword (window.offset + window.width)) (bvar m)) (bword 0)
    (band
      (bcond (bgt (bword (window.offset + 32)) (bvar m))
        (bbinary .wordShl (readAt (bsub (badd (bword base) (bvar m)) (bword 32)))
          (bmul (bword 8) (bsub (bword (window.offset + 32)) (bvar m))))
        (readAt (bword (base + window.offset))))
      (bword (CallReturn.keepMask window.width)))

/-- The phase after call `call`, which requests the next call. Call 1's phase
keeps its first Word and whether its data have a whole Word. -/
private def middleBody (call : Nat) (spot : Window) : B :=
  blet inputSize fun size =>
  blet (readAt (bword 0)) fun target =>
  blet (readAt (bword 32)) fun input =>
  blet (readAt (bword 64)) fun mix =>
  blet (readAt (bword 96)) fun sum =>
  blet (readAt (bword 128)) fun previous =>
  blet (readAt (bword 160)) fun copy =>
  blet (readAt (bword 192)) fun whole =>
  blet (readAt (bword 224)) fun status =>
  blet (bsub (bvar size) (bword base)) fun m =>
  blet (bcond (beq (bvar status) (bword 1)) (bword 1) (bword 0)) fun ok =>
  blet (bcond (bgt (bword 32) (bvar m)) (bword 0) (readAt (bword base))) fun first =>
  blet (window spot m) fun copied =>
  blet (sstore (5 * call - 3) (badd (bvar ok) (bmul (bword 2) (bvar m)))) fun _ =>
  blet (sstore (5 * call - 2) (bvar first)) fun _ =>
  blet (sstore (5 * call - 1) (bvar previous)) fun _ =>
  blet (sstore (5 * call) (bvar m)) fun _ =>
  blet (sstore (5 * call + 1) (bvar copied)) fun _ =>
  blet (badd (badd (badd (badd (badd (badd (bvar sum) (bvar ok)) (bmul (bword 2) (bvar m))) (bvar first))
    (bvar previous)) (bvar m)) (bvar copied)) fun total =>
  blet (badd (badd (badd (bvar mix) (bvar first)) (bvar m)) (bvar copied)) fun mixed =>
  let copy' := if call = 1 then bvar first else bvar copy
  let whole' := if call = 1 then bcond (bgt (bword 32) (bvar m)) (bword 0) (bword 1) else bvar whole
  request (bvar target) (bvar input) (bvar mixed) (bvar total) (bvar m) copy' whole' call mixed input

def middleProgram (call : Nat) (spot : Window) : Program := {
  resultType := requestType
  dataDefinitions := []
  body := middleBody call spot 0
}

/-- The phase after the last call, call `calls`: the re-read, the sum and bit
24's revert. -/
private def lastBody (calls : Nat) (spot : Window) : B :=
  blet inputSize fun size =>
  blet (readAt (bword 32)) fun input =>
  blet (readAt (bword 96)) fun sum =>
  blet (readAt (bword 128)) fun previous =>
  blet (readAt (bword 160)) fun copy =>
  blet (readAt (bword 192)) fun whole =>
  blet (readAt (bword 224)) fun status =>
  blet (bsub (bvar size) (bword base)) fun m =>
  blet (bcond (beq (bvar status) (bword 1)) (bword 1) (bword 0)) fun ok =>
  blet (bcond (bgt (bword 32) (bvar m)) (bword 0) (readAt (bword base))) fun first =>
  blet (window spot m) fun copied =>
  blet (bcond (beq (bvar whole) (bword 1)) (bmul (bword (calls - 1)) (bvar copy)) (bword 0)) fun again =>
  blet (sstore (5 * calls - 3) (badd (bvar ok) (bmul (bword 2) (bvar m)))) fun _ =>
  blet (sstore (5 * calls - 2) (bvar first)) fun _ =>
  blet (sstore (5 * calls - 1) (bvar previous)) fun _ =>
  blet (sstore (5 * calls) (bvar m)) fun _ =>
  blet (sstore (5 * calls + 1) (bvar copied)) fun _ =>
  blet (sstore (5 * calls + 2) (bvar again)) fun _ =>
  blet (badd (badd (badd (badd (badd (badd (badd (bvar sum) (bvar ok)) (bmul (bword 2) (bvar m))) (bvar first))
    (bvar previous)) (bvar m)) (bvar copied)) (bvar again)) fun total =>
  bcond (bbitSet (bvar input) (2 ^ 24))
    (binRight .word (binLeft .word (bvar total)))
    (binLeft (.sum .word .word) (bvar total))

def lastResultType : Ty := .sum .word (.sum .word .word)

def lastProgram (calls : Nat) (spot : Window) : Program := {
  resultType := lastResultType
  dataDefinitions := []
  body := lastBody calls spot 0
}

/-- The phases after calls 1 to `n - 1`, which request the next call. -/
def middlePrograms (windows : List Window) : List Program :=
  windows.dropLast.zipIdx.map fun (spot, index) => middleProgram (index + 1) spot

def lastProgramOf (windows : List Window) : Program :=
  lastProgram windows.length (windows.getLastD ⟨0, 0⟩)

def callNodes : Nat := programNodes callProgram

/-- Every contract is bounded by 1,024 nodes. -/
def maxContractNodes : Nat := 1024

/-! ### The checked plan -/

structure CheckedPlan where private mk ::
  step : Aggregates.CheckedDAG
  windows : List Window
  valid : validWindows windows = true
  childChecked : (childProgramOf step.program.body).check = true
  callChecked : callProgram.check = true
  middlesChecked : (middlePrograms windows).all Program.check = true
  lastChecked : (lastProgramOf windows).check = true

namespace CheckedPlan

def childProgram (plan : CheckedPlan) : Program := childProgramOf plan.step.program.body
def callProgram (_plan : CheckedPlan) : Program := CallSequence.callProgram
def middlePrograms (plan : CheckedPlan) : List Program := CallSequence.middlePrograms plan.windows
def lastProgram (plan : CheckedPlan) : Program := lastProgramOf plan.windows
def calls (plan : CheckedPlan) : Nat := plan.windows.length

def ofParts? (step : Aggregates.CheckedDAG) (windows : List Window) : Option CheckedPlan :=
  if valid : validWindows windows = true then
    if childChecked : (childProgramOf step.program.body).check = true then
      if callChecked : CallSequence.callProgram.check = true then
        if middlesChecked : (CallSequence.middlePrograms windows).all Program.check = true then
          if lastChecked : (lastProgramOf windows).check = true then
            some ⟨step, windows, valid, childChecked, callChecked, middlesChecked, lastChecked⟩
          else none
        else none
      else none
    else none
  else none

theorem childWellTyped (plan : CheckedPlan) : plan.childProgram.WellTyped :=
  Program.check_full_sound plan.childChecked

theorem callWellTyped (plan : CheckedPlan) : plan.callProgram.WellTyped :=
  Program.check_full_sound plan.callChecked

theorem lastWellTyped (plan : CheckedPlan) : plan.lastProgram.WellTyped :=
  Program.check_full_sound plan.lastChecked

def childCode (plan : CheckedPlan) : CheckedHostCoreProgram :=
  ⟨plan.childProgram.toCore, Program.check_promotes_current plan.childChecked⟩

def callCode (plan : CheckedPlan) : CheckedHostCoreProgram :=
  ⟨plan.callProgram.toCore, Program.check_promotes_current plan.callChecked⟩

def lastCode (plan : CheckedPlan) : CheckedHostCoreProgram :=
  ⟨plan.lastProgram.toCore, Program.check_promotes_current plan.lastChecked⟩

def childContract (plan : CheckedPlan) : CheckedCoreContract :=
  CheckedCoreContract.rawOutcomeV1 plan.childCode 2 childResultType_toCore

theorem requestType_toCore :
    requestType.toCore = (CoreContractEntryProfile.wordTupleOutcomeV1 (keptWords + 1)).resultType := by
  simp [requestType, Ty.toCore, TupleReturn.wordTuple_toCore, CoreContractEntryProfile.resultType]

/-- A requesting phase, of the call phase's result type. -/
def requestContract (program : Program) (checked : program.check = true)
    (typed : program.resultType = requestType) : CheckedCoreContract :=
  CheckedCoreContract.wordTupleOutcomeV1 ⟨program.toCore, Program.check_promotes_current checked⟩ (keptWords + 1)
    (by
      change program.resultType.toCore = _
      rw [typed, requestType_toCore])

def callContract (plan : CheckedPlan) : CheckedCoreContract :=
  requestContract plan.callProgram plan.callChecked rfl

/-- Each middle program of `windows` is a requesting phase. -/
theorem middlePrograms_resultType (windows : List Window) :
    ∀ program ∈ CallSequence.middlePrograms windows, program.resultType = requestType := by
  intro program member
  simp only [CallSequence.middlePrograms, List.mem_map] at member
  obtain ⟨_, _, rfl⟩ := member
  rfl

def middleContracts (plan : CheckedPlan) : List CheckedCoreContract :=
  plan.middlePrograms.attach.map fun ⟨program, member⟩ =>
    requestContract program (List.all_eq_true.mp plan.middlesChecked program member)
      (middlePrograms_resultType plan.windows program member)

def lastContract (plan : CheckedPlan) : CheckedCoreContract :=
  CheckedCoreContract.wordOutcomeV1 plan.lastCode rfl

theorem middleContracts_entryProfile (plan : CheckedPlan) :
    ∀ phase ∈ plan.middleContracts, phase.entryProfile = .wordTupleOutcomeV1 (keptWords + 1) := by
  intro phase member
  simp only [middleContracts, List.mem_map] at member
  obtain ⟨_, _, rfl⟩ := member
  rfl

/-- The parent in continuation-passing form for the call chain. -/
def parent (plan : CheckedPlan) : CallChainParent := {
  call := plan.callContract
  middles := plan.middleContracts
  last := plan.lastContract
  keptWords := keptWords
  call_entryProfile := rfl
  middles_entryProfile := plan.middleContracts_entryProfile
  last_entryProfile := rfl
}

theorem childContract_entryProfile (plan : CheckedPlan) :
    plan.childContract.entryProfile = .rawOutcomeV1 2 := rfl

theorem middleContracts_length (plan : CheckedPlan) :
    plan.middleContracts.length = plan.calls - 1 := by
  simp [middleContracts, CheckedPlan.middlePrograms, CallSequence.middlePrograms, calls]

end CheckedPlan
end Solcore.Synthesis.Core.CallSequence
end

section
-- leanmerge: from Solcore.Synthesis.Core.CallBranch
/-! Checked contracts for a parent whose calls sit in branches and loops, so
that the input decides how many calls a transaction makes. The child is
`CallSequence`'s child. The parent has one to three sites in program order,
each a branch or a loop, whose bounds number the potential calls, the
positions, from zero. Position `q`'s argument is `mix·256` plus the input's
byte `q`; site `i`'s control bits are the input's bits `24 + 2i` and `25 + 2i`;
bit 30 reverts the parent and `mix = input >> 32`.

The parent is in continuation-passing form for the choice chain: a call phase
and one resume program, all choice phases. Each phase defines every site's
steps as lambdas over a state of `mix`, the calls made, the latest data's size
and a loop's counter: a site's entry reads the size before it and calls or
skips, a loop's iteration calls while its counter is below its limit and the
latest size differs from its stop length, and a site's exit reads the size and
the exit window after it. The last lambda writes the call count, sums the slots
and finishes or reverts. The call phase writes slot 0 and `z = 0`, then enters
site 0 with no data; the resume phase writes the reads after its call, kept as
its position, then continues that call's site. A request keeps five Words: the
target, the input, `mix`, the position and the calls made with it. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Core.CallBranch

open Solcore.Core (Word)
open Solcore.Core.Wire
open Solcore.ContractRuntime
open Solcore.Synthesis.Core.CallBuilder
open Solcore.Synthesis.Core.CallSequence (Window childProgramOf childResultType childResultType_toCore)

def parentVersion : String := "core-call-branch-parent-v1"

/-- `get(uint256)`, the child's one method. -/
def getSelector : Nat := CallSequence.getSelector

/-- The child's longest data: three Words. -/
def capacity : Nat := CallSequence.capacity

/-- The most calls a transaction makes. -/
def maxCalls : Nat := 3

/-- The Words each request keeps: the target, the input, `mix`, the position
and the calls made with it. -/
def keptWords : Nat := 5

/-- The return data start after the kept Words and the status Word. -/
def base : Nat := 32 * (keptWords + 1)

/-- The input bit that reverts the parent. -/
def revertBit : Nat := 30

/-- Site `index`'s first control bit. -/
def controlBit (index : Nat) : Nat := 24 + 2 * index

inductive Kind where
  | branch
  | loop
  deriving Repr, BEq, DecidableEq

/-- One call site: a branch of bound one, or a loop of bound one to three that
stops on its stop length, with the window read right after each call and the
one read after the site. -/
structure Site where
  kind : Kind
  bound : Nat
  stop : Nat
  callWindow : Window
  exitWindow : Window
  deriving Repr, BEq, DecidableEq

def Site.valid (site : Site) : Bool :=
  site.callWindow.valid && site.exitWindow.valid &&
    match site.kind with
    | .branch => site.bound == 1 && site.stop == 0
    | .loop => 1 ≤ site.bound && site.bound ≤ maxCalls && site.stop ≤ capacity

/-- The number of positions. -/
def positions (sites : List Site) : Nat := (sites.map (·.bound)).sum

/-- One to three valid sites with at most three positions. -/
def validSites (sites : List Site) : Bool :=
  1 ≤ sites.length && sites.length ≤ 3 && sites.all Site.valid && positions sites ≤ maxCalls

/-- Site `index`'s first position. -/
def firstPosition (sites : List Site) (index : Nat) : Nat := positions (sites.take index)

/-- The site of position `position`. -/
def siteOf (sites : List Site) (position : Nat) : Nat :=
  ((List.range sites.length).filter fun index => firstPosition sites index ≤ position).length - 1

/-- Site `index`'s three slots: the size before it, then the size and the exit
window after it. -/
def siteSlot (index : Nat) : Nat := 2 + 3 * index

/-- Position `position`'s four slots: the flag plus twice the size, the first
Word, the size and the call window after its call. -/
def positionSlot (sites : List Site) (position : Nat) : Nat := 2 + 3 * sites.length + 4 * position

/-- The slot of the number of calls made. -/
def countSlot (sites : List Site) : Nat := positionSlot sites (positions sites)

/-- The parent's slots: the accumulator, `z`, three per site, four per position
and the call count. -/
def parentSlotCount (sites : List Site) : Nat := countSlot sites + 1

def childSlotCount : Nat := CallSequence.childSlotCount

private def w (value : Nat) : Word := Word.ofNatModulo value

private def band (left right : B) : B := bbinary .wordAnd left right
private def bmul (left right : B) : B := bbinary .wordMul left right
private def bshr (value shift : B) : B := bbinary .wordShr value shift

/-! ### The parent -/

/-- A choice phase's result: the choosing Word, the target, the selector, the
argument and the kept Words, or a reverted Word, or a trap. -/
def choiceType : Ty := .sum (TupleReturn.wordTuple (keptWords + 3)) (.sum .word .word)

/-- The state of each site's lambdas: `mix`, the calls made, the latest data's
size and a loop's counter. -/
def stateType : Ty := .product .word (.product .word (.product .word .word))

private def state (mix calls size counter : B) : B := bpair mix (bpair calls (bpair size counter))
private def mixOf (value : B) : B := bfirst value
private def callsOf (value : B) : B := bfirst (bsecond value)
private def sizeOf (value : B) : B := bfirst (bsecond (bsecond value))
private def counterOf (value : B) : B := bsecond (bsecond (bsecond value))

/-- The request for the call at `position`, keeping the target, the input,
`mix`, the position and the calls made with it. -/
private def request (target input mix calls position : B) : B :=
  binLeft (.sum .word .word) (btuple [bword 1, target, bword getSelector,
    badd (bmul mix (bword 256)) (band (bshr input (bmul (bword 8) position)) (bword 255)),
    target, input, mix, position, badd calls (bword 1)])

/-- Finish with `value` as the returned Word. -/
private def finishWith (value : B) : B :=
  binLeft (.sum .word .word) (btuple ([bword 0, value] ++ List.replicate (keptWords + 2) (bword 0)))

/-- The data's bytes `offset` to `offset + width - 1`, left-aligned in a zero
Word, when they lie inside the `size` bytes at `base`, and otherwise zero: the
Word at `base + offset` when it exists, otherwise the Word ending at the data's
last byte shifted to the offset, then masked to the width. -/
private def window (spot : Window) (size : B) : B :=
  bcond (bgt (bword (spot.offset + spot.width)) size) (bword 0)
    (band
      (bcond (bgt (bword (spot.offset + 32)) size)
        (bbinary .wordShl (readAt (bsub (badd (bword base) size) (bword 32)))
          (bmul (bword 8) (bsub (bword (spot.offset + 32)) size)))
        (readAt (bword (base + spot.offset))))
      (bword (CallReturn.keepMask spot.width)))

/-- Zero the four slots of `position`, which no call reached. -/
private def zeroPosition (sites : List Site) (position : Nat) : B :=
  blet (sstore (positionSlot sites position) (bword 0)) fun _ =>
  blet (sstore (positionSlot sites position + 1) (bword 0)) fun _ =>
  blet (sstore (positionSlot sites position + 2) (bword 0)) fun _ =>
  sstore (positionSlot sites position + 3) (bword 0)

/-- The finishing lambda: the call count, the sum of every slot, and bit 30's
revert. -/
private def finishBody (sites : List Site) (input : Nat) : Nat → B := fun value =>
  blet (sstore (countSlot sites) (callsOf (bvar value))) fun _ =>
  blet (((List.range (countSlot sites + 1)).map sload).foldl badd (bword 0)) fun total =>
  bcond (bbitSet (bvar input) (2 ^ revertBit))
    (binRight (TupleReturn.wordTuple (keptWords + 3)) (binLeft .word (bvar total)))
    (finishWith (bvar total))

/-- Site `index`'s exit: the size and the exit window after it, then the next
site's entry, or the finish. -/
private def exitBody (site : Site) (index next : Nat) : Nat → B := fun value =>
  blet (sizeOf (bvar value)) fun size =>
  blet (sstore (siteSlot index + 1) (bvar size)) fun _ =>
  blet (window site.exitWindow (bvar size)) fun copied =>
  blet (sstore (siteSlot index + 2) (bvar copied)) fun _ =>
  bapply (bvar next) (state (badd (badd (mixOf (bvar value)) (bvar size)) (bvar copied))
    (callsOf (bvar value)) (bvar size) (bword 0))

/-- A loop's iteration at its counter: a call while the counter is below the
limit and the latest size differs from the stop length, otherwise zeros for
the positions left, then the exit. -/
private def iterateBody (sites : List Site) (site : Site) (index target input exit : Nat) : Nat → B := fun value =>
  let first := firstPosition sites index
  blet (counterOf (bvar value)) fun counter =>
  blet (band (bshr (bvar input) (bword (controlBit index))) (bword 3)) fun requested =>
  blet (bcond (bgt (bvar requested) (bword site.bound)) (bword site.bound) (bvar requested)) fun limit =>
  blet (bcond (bgt (bvar limit) (bvar counter))
    (bcond (beq (sizeOf (bvar value)) (bword site.stop)) (bword 0) (bword 1)) (bword 0)) fun go =>
  bcond (beq (bvar go) (bword 1))
    (request (bvar target) (bvar input) (mixOf (bvar value)) (callsOf (bvar value)) (badd (bword first) (bvar counter)))
    (((List.range site.bound).foldr (fun offset rest =>
        blet (bcond (bgt (bword (offset + 1)) (bvar counter)) (zeroPosition sites (first + offset)) bunit) fun _ => rest)
      (bapply (bvar exit) (bvar value))))

/-- Site `index`'s entry: the size before it, then a branch's call or zeros,
or a loop's first iteration. -/
private def enterBody (sites : List Site) (site : Site) (index target input exit : Nat) (iterate : Option Nat) :
    Nat → B := fun value =>
  let first := firstPosition sites index
  blet (sstore (siteSlot index) (sizeOf (bvar value))) fun _ =>
  match site.kind, iterate with
  | .loop, some loop =>
      bapply (bvar loop) (state (mixOf (bvar value)) (callsOf (bvar value)) (sizeOf (bvar value)) (bword 0))
  | _, _ =>
      bcond (bbitSet (bvar input) (2 ^ controlBit index))
        (request (bvar target) (bvar input) (mixOf (bvar value)) (callsOf (bvar value)) (bword first))
        (blet (zeroPosition sites first) fun _ => bapply (bvar exit) (bvar value))

/-- The lambdas of one site. -/
structure Levels where
  enter : Nat
  exit : Nat
  iterate : Option Nat

/-- Define the lambdas of sites `index` down to 0, the lambda after site
`index` being `next`, then continue with every site's levels, from site 0. -/
private def defineFrom (sites : List Site) (target input : Nat) :
    Nat → Nat → List Levels → (List Levels → B) → B
  | index, next, defined, rest =>
      let site := sites.getD index ⟨.branch, 1, 0, ⟨0, 0⟩, ⟨0, 0⟩⟩
      blet (blam stateType choiceType (exitBody site index next)) fun exit =>
      let enter := fun (iterate : Option Nat) =>
        blet (blam stateType choiceType (enterBody sites site index target input exit iterate)) fun entry =>
          let defined' := ⟨entry, exit, iterate⟩ :: defined
          match index with
          | 0 => rest defined'
          | previous + 1 => defineFrom sites target input previous entry defined' rest
      match site.kind with
      | .loop =>
          blet (blam stateType choiceType (iterateBody sites site index target input exit)) fun loop =>
            enter (some loop)
      | .branch => enter none
termination_by index _ _ _ => index

/-- Every site's lambdas after the finish, then `rest` with their levels. -/
private def withSites (sites : List Site) (target input : Nat) (rest : List Levels → B) : B :=
  blet (blam stateType choiceType (finishBody sites input)) fun finish =>
  defineFrom sites target input (sites.length - 1) finish [] rest

/-- Read the target at 4 and the input at 36, write `p + input` to slot 0 and
`z = 0` to slot 1, then enter site 0 with no data. -/
private def callBody (sites : List Site) : B :=
  blet (readAt (bword 4)) fun target =>
  blet (readAt (bword 36)) fun input =>
  blet (sstore 0 (badd (sload 0) (bvar input))) fun _ =>
  blet (sstore 1 (bword 0)) fun _ =>
  blet (bshr (bvar input) (bword 32)) fun mix =>
  withSites sites target input fun levels =>
    bapply (bvar (levels.headD ⟨0, 0, none⟩).enter) (state (bvar mix) (bword 0) (bword 0) (bword 0))

/-- After the call at `position`: its four slots from the status Word and the
data, then the rest of its site. -/
private def afterCall (sites : List Site) (levels : List Levels) (position mix calls status size : Nat) : B :=
  let index := siteOf sites position
  let site := sites.getD index ⟨.branch, 1, 0, ⟨0, 0⟩, ⟨0, 0⟩⟩
  let siteLevels := levels.getD index ⟨0, 0, none⟩
  blet (bcond (beq (bvar status) (bword 1)) (bword 1) (bword 0)) fun ok =>
  blet (bcond (bgt (bword 32) (bvar size)) (bword 0) (readAt (bword base))) fun firstWord =>
  blet (window site.callWindow (bvar size)) fun copied =>
  blet (sstore (positionSlot sites position) (badd (bvar ok) (bmul (bword 2) (bvar size)))) fun _ =>
  blet (sstore (positionSlot sites position + 1) (bvar firstWord)) fun _ =>
  blet (sstore (positionSlot sites position + 2) (bvar size)) fun _ =>
  blet (sstore (positionSlot sites position + 3) (bvar copied)) fun _ =>
  let after := state (badd (badd (badd (bvar mix) (bvar firstWord)) (bvar size)) (bvar copied)) (bvar calls) (bvar size)
    (bword (position - firstPosition sites index + 1))
  match siteLevels.iterate with
  | some loop => bapply (bvar loop) after
  | none => bapply (bvar siteLevels.exit) after

/-- Dispatch on the kept position, from `position` on. -/
private def dispatch (sites : List Site) (levels : List Levels) (kept mix calls status size : Nat) : Nat → B
  | position =>
      if position + 1 ≥ positions sites then afterCall sites levels position mix calls status size
      else bcond (beq (bvar kept) (bword position)) (afterCall sites levels position mix calls status size)
        (dispatch sites levels kept mix calls status size (position + 1))
termination_by position => positions sites - position
decreasing_by omega

/-- Read the kept Words, the status Word and the data's size, then continue
after the kept position's call. -/
private def resumeBody (sites : List Site) : B :=
  blet inputSize fun total =>
  blet (readAt (bword 0)) fun target =>
  blet (readAt (bword 32)) fun input =>
  blet (readAt (bword 64)) fun mix =>
  blet (readAt (bword 96)) fun position =>
  blet (readAt (bword 128)) fun calls =>
  blet (readAt (bword 160)) fun status =>
  blet (bsub (bvar total) (bword base)) fun size =>
  withSites sites target input fun levels =>
    dispatch sites levels position mix calls status size 0

def callProgram (sites : List Site) : Program := {
  resultType := choiceType
  dataDefinitions := []
  body := callBody sites 0
}

def resumeProgram (sites : List Site) : Program := {
  resultType := choiceType
  dataDefinitions := []
  body := resumeBody sites 0
}

/-- The child is bounded by 1,024 nodes. -/
def maxChildNodes : Nat := CallSequence.maxContractNodes

/-- Each parent phase is bounded by 2,048 nodes. -/
def maxPhaseNodes : Nat := 2048

/-! ### The checked plan -/

structure CheckedPlan where private mk ::
  step : Aggregates.CheckedDAG
  sites : List Site
  valid : validSites sites = true
  childChecked : (childProgramOf step.program.body).check = true
  callChecked : (callProgram sites).check = true
  resumeChecked : (resumeProgram sites).check = true

namespace CheckedPlan

def childProgram (plan : CheckedPlan) : Program := childProgramOf plan.step.program.body
def callProgram (plan : CheckedPlan) : Program := CallBranch.callProgram plan.sites
def resumeProgram (plan : CheckedPlan) : Program := CallBranch.resumeProgram plan.sites
def positions (plan : CheckedPlan) : Nat := CallBranch.positions plan.sites

def ofParts? (step : Aggregates.CheckedDAG) (sites : List Site) : Option CheckedPlan :=
  if valid : validSites sites = true then
    if childChecked : (childProgramOf step.program.body).check = true then
      if callChecked : (CallBranch.callProgram sites).check = true then
        if resumeChecked : (CallBranch.resumeProgram sites).check = true then
          some ⟨step, sites, valid, childChecked, callChecked, resumeChecked⟩
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

def childContract (plan : CheckedPlan) : CheckedCoreContract :=
  CheckedCoreContract.rawOutcomeV1 plan.childCode 2 childResultType_toCore

theorem choiceType_toCore :
    choiceType.toCore = (CoreContractEntryProfile.wordTupleOutcomeV1 (keptWords + 2)).resultType := by
  simp [choiceType, Ty.toCore, TupleReturn.wordTuple_toCore, CoreContractEntryProfile.resultType]

/-- A choice phase of `program`, of the choice result type. -/
def choiceContract (program : Program) (checked : program.check = true)
    (typed : program.resultType = choiceType) : CheckedCoreContract :=
  CheckedCoreContract.wordTupleOutcomeV1 ⟨program.toCore, Program.check_promotes_current checked⟩ (keptWords + 2)
    (by
      change program.resultType.toCore = _
      rw [typed, choiceType_toCore])

def callContract (plan : CheckedPlan) : CheckedCoreContract :=
  choiceContract plan.callProgram plan.callChecked rfl

def resumeContract (plan : CheckedPlan) : CheckedCoreContract :=
  choiceContract plan.resumeProgram plan.resumeChecked rfl

/-- The parent in continuation-passing form for the choice chain: the call
phase and one resume phase per possible call, all the same program. -/
def parent (plan : CheckedPlan) : CallChoiceParent := {
  call := ⟨plan.callContract, .choose⟩
  resumes := List.replicate maxCalls ⟨plan.resumeContract, .choose⟩
  keptWords := keptWords
  call_entryProfile := rfl
  resumes_entryProfile := by
    intro phase member
    rw [List.eq_of_mem_replicate member]
    rfl
}

theorem childContract_entryProfile (plan : CheckedPlan) :
    plan.childContract.entryProfile = .rawOutcomeV1 2 := rfl

end CheckedPlan
end Solcore.Synthesis.Core.CallBranch
end

section
-- leanmerge: from Solcore.Synthesis.Source.CallReturnEmitter
/-! Emit the call-return protocol as two sources with one contract each. The
child `SynthesizedReturnCallee` has one method `get(uint256 x)`: it follows the
original Core child in order, the step over `x` and slot 0, the writes of slots
0 and 1 and the odd-`x` revert of 32 bytes, then returns the plan's value. Typed,
the method declares the value's type and std's dispatcher encodes it; raw, it
declares `uint256`, writes the Words of the malformed encoding to memory and
ends with `return_`. A `bytes` value's data past its length are never read,
since std's encoder zero-pads them.

The parent `SynthesizedReturnCaller` has one method `run(uint256 target,
uint256 input)`. It writes `slot 0 + input` to slot 0, calls the target with
std's `raw_call` and the payload `0x9507d39a ‖ input`, and, when the call
succeeds, decodes the return data with std's `abi_decode` and
`MemoryWordReader` as the plan's type; otherwise it keeps the revert data's
first Word. It writes the flag and twice the size, the constructor index and
four Words to slots 1 to 6, sums them with slot 0, and reverts with the sum
under bit 1 of the input. Both sources declare the enum when the plan has one.
No emitter proof covers these wrappers. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.CallReturn

open Solcore.Synthesis.Core.CallReturn (CheckedPlan Kind Returned Delivery Cell Source)
open Solcore.Synthesis.Core.EnumReturn (Constructor Shape)

def emitterVersion : String := "solcore-source-call-returns-v1"
def wrapperVersion : String := "solcore-call-returns-contracts-v1"
def parentContractName : String := "SynthesizedReturnCaller"
def childContractName : String := "SynthesizedReturnCallee"
def parentMethodSignature : String := "run(uint256,uint256)"
def childMethodSignature : String := "get(uint256)"
def parentSelector : String := "0x7357f5d2"
def childSelector : String := "0x9507d39a"
def enumName : String := Solcore.Synthesis.Source.EnumReturn.enumName
def parentDeployPath : List String := [parentContractName ++ "Deploy"]
def parentRuntimePath : List String := [parentContractName ++ "Deploy", parentContractName]
def childDeployPath : List String := [childContractName ++ "Deploy"]
def childRuntimePath : List String := [childContractName ++ "Deploy", childContractName]

structure EmittedContracts where
  parentSource : String
  childSource : String
  deriving Repr, BEq

/-- A Word as a hexadecimal literal. -/
private def literal (value : Nat) : String := "0x" ++ String.ofList (Nat.toDigits 16 value)

private def multiplierLiteral : String := literal Solcore.Synthesis.Core.CallReturn.multiplier

/-- The enum's declaration, when the plan has one. -/
private def enumLines (kind : Kind) : List String :=
  match kind with
  | .enum shape =>
      ["enum " ++ enumName ++ " {"] ++
        shape.constructors.zipIdx.map (fun (constructor, index) =>
          "    " ++ Solcore.Synthesis.Source.EnumReturn.declaration constructor ++
            if index + 1 = shape.constructors.length then "" else ",") ++
        ["}", ""]
  | _ => []

private def stdImports (kind : Kind) : List String :=
  ["import * from std;", "import * from std.dispatch;"] ++
    match kind with
    | .enum _ => ["import * from std.Generic;", "import * from std.ABIGeneric;"]
    | _ => []

private def sourceName : Source → String
  | .r => "sc_r"
  | .c => "sc_c"
  | .x => "sc_x"
  | .o => "sc_o"
  | .d0 => "sc_d0"
  | .d1 => "sc_d1"

private def cellExpression : Cell → String
  | .const value => literal value.val
  | .value source kept =>
      if kept ≥ 32 then sourceName source
      else "(" ++ sourceName source ++ " & " ++ literal (Solcore.Synthesis.Core.CallReturn.keepMask kept) ++ ")"

/-- The declared return type of the child's method. -/
private def childReturnType (returned : Returned) : String :=
  match returned.delivery with
  | .raw _ => "uint256"
  | .typed => match returned.kind with
    | .tuple extra => "(" ++ ", ".intercalate (List.replicate (extra + 2) "uint256") ++ ")"
    | .bytes => "memory<bytes>"
    | .enum _ => enumName

/-- A `bytes` value of `length` bytes of `d0 ‖ d1`, bound to `sc_bytes`. -/
private def bytesLines (length : Nat) : List String :=
  ["        let sc_pointer: word = allocate_memory(96);",
    "        mstore(sc_pointer, " ++ toString length ++ ");",
    "        mstore((sc_pointer + 32), sc_d0);",
    "        mstore((sc_pointer + 64), sc_d1);",
    "        let sc_bytes: memory<bytes> = Typedef.abs(sc_pointer);"]

private def valueLines (returned : Returned) : List String :=
  match returned.delivery with
  | .raw _ =>
      let cells := Solcore.Synthesis.Core.CallReturn.rawCells returned
      ["        let sc_p: word = allocate_memory(" ++ toString (32 * cells.length) ++ ");"] ++
        cells.zipIdx.map (fun (cell, index) =>
          "        mstore(" ++ (if index = 0 then "sc_p" else "(sc_p + " ++ toString (32 * index) ++ ")") ++ ", " ++
            cellExpression cell ++ ");") ++
        ["        return_(sc_p, " ++ toString (Solcore.Synthesis.Core.CallReturn.returnedCells returned).2 ++ ");",
          "        return uint256(0);"]
  | .typed => match returned.kind with
    | .tuple extra =>
        ["        return (" ++ ", ".intercalate
          ((["sc_r", "sc_c", "sc_x", "sc_o"].take (extra + 2)).map fun name => "uint256(" ++ name ++ ")") ++ ");"]
    | .bytes => bytesLines returned.length ++ ["        return sc_bytes;"]
    | .enum shape =>
        let constructor := Solcore.Synthesis.Core.CallReturn.chosen shape returned.choice
        let value := enumName ++ "." ++ constructor.name
        match constructor.payload with
        | .noWords => ["        return " ++ value ++ ";"]
        | .oneWord => ["        return " ++ value ++ "(uint256(sc_d0));"]
        | .twoWords => ["        return " ++ value ++ "(uint256(sc_d0), uint256(sc_d1));"]
        | .boundedBytes => bytesLines returned.length ++ ["        return " ++ value ++ "(sc_bytes);"]

/-- The parent's decoding of a returned call, as the plan's type. -/
private def bytesRecordLines (indent value : String) : List String :=
  [indent ++ "let sc_b: word = Typedef.rep(" ++ value ++ ");",
    indent ++ "sc_w0 = mload(sc_b);",
    indent ++ "if (sc_w0 > 0) {",
    indent ++ "    sc_w1 = mload((sc_b + 32));",
    indent ++ "}",
    indent ++ "if (sc_w0 > 32) {",
    indent ++ "    sc_w2 = mload((sc_b + 64));",
    indent ++ "}"]

private def armLines (index : Nat) (constructor : Constructor) : List String :=
  let indent := "                            "
  let case := "                        case " ++ enumName ++ "." ++ constructor.name
  let marker := indent ++ "sc_index = " ++ toString (index + 1) ++ ";"
  (match constructor.payload with
    | .noWords => [case ++ " {", marker]
    | .oneWord => [case ++ "(sc_a0) {", marker, indent ++ "sc_w0 = Typedef.rep(sc_a0);"]
    | .twoWords => [case ++ "(sc_a0, sc_a1) {", marker, indent ++ "sc_w0 = Typedef.rep(sc_a0);",
        indent ++ "sc_w1 = Typedef.rep(sc_a1);"]
    | .boundedBytes => [case ++ "(sc_blob) {", marker] ++ bytesRecordLines indent "sc_blob") ++
    ["                        }"]

private def decodeLines (kind : Kind) : List String :=
  let indent := "                    "
  match kind with
  | .tuple extra =>
      let count := extra + 2
      let names := (List.range count).map fun index => "sc_a" ++ toString index
      let types := ", ".intercalate (List.replicate count "uint256")
      [indent ++ "let sc_tuple: (" ++ types ++ ") = abi_decode(ret, @(" ++ types ++ "), @MemoryWordReader);",
        indent ++ "match (sc_tuple) {",
        indent ++ "    case (" ++ ", ".intercalate names ++ ") {"] ++
        names.zipIdx.map (fun (name, index) =>
          indent ++ "        sc_w" ++ toString index ++ " = Typedef.rep(" ++ name ++ ");") ++
        [indent ++ "    }", indent ++ "}"]
  | .bytes =>
      [indent ++ "let sc_bytes: memory<bytes> = abi_decode(ret, @memory<bytes>, @MemoryWordReader);"] ++
        bytesRecordLines indent "sc_bytes"
  | .enum shape =>
      [indent ++ "let sc_value: " ++ enumName ++ " = abi_decode(ret, @" ++ enumName ++ ", @MemoryWordReader);",
        indent ++ "match (sc_value) {"] ++
        (shape.constructors.zipIdx.map fun (constructor, index) => armLines index constructor).flatten ++
        [indent ++ "}"]

def emit (plan : CheckedPlan) : Except EmitError EmittedContracts := do
  let returned := plan.returned
  let mut names : List String := []
  let mut child := stdImports returned.kind ++
    [AggregateRenderer.opcodeImportWith ["sload", "sstore", "mstore", "return_", "revert_"]
      (plan.step.helpers ++ [plan.step.entry]), ""] ++ enumLines returned.kind
  for (body, index) in plan.step.helpers.zipIdx do
    let rendered ← AggregateRenderer.render names .word [.word "sc_arg"] 4 0 body
    let result ← AggregateRenderer.requireValue rendered
    let name := "sc_fn" ++ toString index
    child := child ++ ["function " ++ name ++ "(sc_arg: word) returns (word) {"] ++
      rendered.lines ++ ["    return " ++ result ++ ";", "}", ""]
    names := name :: names
  let entry ← AggregateRenderer.render names .word [.word "sc_arg"] 4 0 plan.step.entry
  let result ← AggregateRenderer.requireValue entry
  child := child ++ ["function sc_step(sc_arg: word) returns (word) {"] ++
    entry.lines ++ ["    return " ++ result ++ ";", "}", "",
    "contract " ++ childContractName ++ " {",
    "    function get(x: uint256) public returns (" ++ childReturnType returned ++ ") {",
    "        let sc_x: word = Typedef.rep(x);",
    "        let sc_o: word = sload(0);",
    "        let sc_c: word = (sload(1) + 1);",
    "        let sc_r: word = sc_step((sc_x + sc_o));",
    "        sstore(0, sc_r);",
    "        sstore(1, sc_c);",
    "        if ((sc_x & 1) == 1) {",
    "            mstore(0, sc_r);",
    "            revert_(0, 32);",
    "        }",
    "        let sc_d0: word = (sc_r * " ++ multiplierLiteral ++ ");",
    "        let sc_d1: word = ((sc_c * " ++ multiplierLiteral ++ ") ^ sc_x);"] ++
    valueLines returned ++ ["    }", "}"]
  let parent := stdImports returned.kind ++
    [AggregateRenderer.opcodeImportWith ["sload", "sstore", "mstore", "mload", "revert_"] [], ""] ++
    enumLines returned.kind ++
    ["contract " ++ parentContractName ++ " {",
    "    function run(target: uint256, input: uint256) public returns (uint256) {",
    "        let sc_target: word = Typedef.rep(target);",
    "        let sc_input: word = Typedef.rep(input);",
    "        sstore(0, (sload(0) + sc_input));",
    "        let sc_payload: word = allocate_memory(68);",
    "        mstore(sc_payload, 36);",
    "        mstore((sc_payload + 32), " ++ literal (Solcore.Synthesis.Core.CallReturn.getSelector * 2 ^ 224) ++ ");",
    "        mstore((sc_payload + 36), sc_input);",
    "        let sc_data: memory<bytes> = Typedef.abs(sc_payload);",
    "        let sc_ok: word = 0;",
    "        let sc_size: word = 0;",
    "        let sc_index: word = 0;",
    "        let sc_w0: word = 0;",
    "        let sc_w1: word = 0;",
    "        let sc_w2: word = 0;",
    "        let sc_w3: word = 0;",
    "        match (raw_call(address(sc_target), uint256(0), sc_data)) {",
    "            case (ok, ret) {",
    "                sc_ok = frombool(ok);",
    "                let sc_ret: word = Typedef.rep(ret);",
    "                sc_size = mload(sc_ret);",
    "                if (sc_ok == 1) {"] ++ decodeLines returned.kind ++
    ["                }",
    "                if ((sc_ok == 0) && (sc_size > 31)) {",
    "                    sc_w0 = mload((sc_ret + 32));",
    "                }",
    "            }",
    "        }",
    "        sstore(1, (sc_ok + (2 * sc_size)));",
    "        sstore(2, sc_index);",
    "        sstore(3, sc_w0);",
    "        sstore(4, sc_w1);",
    "        sstore(5, sc_w2);",
    "        sstore(6, sc_w3);",
    "        let sc_sum: word = (((((sload(0) + sc_index) + sc_w0) + sc_w1) + sc_w2) + sc_w3);",
    "        if ((sc_input & 2) == 2) {",
    "            mstore(0, sc_sum);",
    "            revert_(0, 32);",
    "        }",
    "        return uint256(sc_sum);",
    "    }",
    "}"]
  return {
    parentSource := String.intercalate "\n" parent ++ "\n"
    childSource := String.intercalate "\n" child ++ "\n"
  }

end Solcore.Synthesis.Source.CallReturn
end

section
-- leanmerge: from Solcore.Synthesis.Source.CallSequenceEmitter
/-! Emit the call-sequence protocol as two sources with one contract each,
under the call-return profile's wrapper names and methods. The child
`SynthesizedReturnCallee` has one method `get(uint256 x)`: it follows the
original Core child in order, the step over `x` and slot 0 and the writes of
slots 0 and 1, then computes the length from the class byte in inline Yul,
writes `d0`, `d1` and `d2` to memory and ends with `revert_` for an odd class
byte, otherwise with `return_`.

The parent `SynthesizedReturnCaller` has one method `run(uint256 target,
uint256 input)`. It writes `slot 0 + input` to slot 0; in inline Yul it copies
zero bytes at offset 0 into a zeroed scratch Word and reads it back, and takes
`mix = input >> 32`. For each call it reads `returndatasize()` in inline Yul,
calls the target with std's `raw_call` and the payload `0x9507d39a ‖ x`, keeps
the flag, the copy's length and its first Word when it has one, then reads
`returndatasize()` and copies the plan's window with `returndatacopy` in
inline Yul when it lies inside the data; from the second call on it re-reads
call 1's copy's first Word. It writes every slot at the end, sums them with
slot 0 and reverts with the sum under bit 24 of the input. No emitter proof
covers these wrappers. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.CallSequence

open Solcore.Synthesis.Core.CallSequence (CheckedPlan Window)
open Solcore.Synthesis.Source.CallReturn (EmittedContracts)

def emitterVersion : String := "solcore-source-call-sequences-v1"
def wrapperVersion : String := "solcore-call-sequences-contracts-v1"

/-- A Word as a hexadecimal literal. -/
private def literal (value : Nat) : String := "0x" ++ String.ofList (Nat.toDigits 16 value)

private def multiplierLiteral : String := literal Solcore.Synthesis.Core.CallSequence.multiplier

private def stdImports : List String := ["import * from std;", "import * from std.dispatch;"]

private def name (prefix_ : String) (call : Nat) : String := prefix_ ++ toString call

/-- Call `call`, from one: the argument, the read before the call, the call,
the reads after it and, from the second call on, the re-read of call 1's copy. -/
private def callLines (call : Nat) (spot : Window) : List String :=
  let n := fun base => name base call
  ["        let " ++ n "sc_class" ++ ": word = 0;",
    "        assembly {",
    "            " ++ n "sc_class" ++ " := and(shr(" ++ toString (8 * (call - 1)) ++ ", sc_input), 255)",
    "        }",
    "        let " ++ n "sc_x" ++ ": word = ((sc_mix * 256) + " ++ n "sc_class" ++ ");",
    "        let " ++ n "sc_payload" ++ ": word = allocate_memory(68);",
    "        mstore(" ++ n "sc_payload" ++ ", 36);",
    "        mstore((" ++ n "sc_payload" ++ " + 32), " ++
      literal (Solcore.Synthesis.Core.CallSequence.getSelector * 2 ^ 224) ++ ");",
    "        mstore((" ++ n "sc_payload" ++ " + 36), " ++ n "sc_x" ++ ");",
    "        let " ++ n "sc_data" ++ ": memory<bytes> = Typedef.abs(" ++ n "sc_payload" ++ ");",
    "        let " ++ n "sc_p" ++ ": word = 1;",
    "        assembly {",
    "            " ++ n "sc_p" ++ " := returndatasize()",
    "        }",
    "        let " ++ n "sc_ok" ++ ": word = 0;"] ++
  (if call > 1 then ["        let " ++ n "sc_size" ++ ": word = 0;", "        let " ++ n "sc_ret" ++ ": word = 0;"] else []) ++
  ["        let " ++ n "sc_first" ++ ": word = 0;",
    "        match (raw_call(address(sc_target), uint256(0), " ++ n "sc_data" ++ ")) {",
    "            case (ok, ret) {",
    "                " ++ n "sc_ok" ++ " = frombool(ok);",
    "                " ++ n "sc_ret" ++ " = Typedef.rep(ret);",
    "                " ++ n "sc_size" ++ " = mload(" ++ n "sc_ret" ++ ");",
    "                if (" ++ n "sc_size" ++ " > 31) {",
    "                    " ++ n "sc_first" ++ " = mload((" ++ n "sc_ret" ++ " + 32));",
    "                }",
    "            }",
    "        }",
    "        let " ++ n "sc_n" ++ ": word = 0;",
    "        let " ++ n "sc_c" ++ ": word = 0;",
    "        assembly {",
    "            " ++ n "sc_n" ++ " := returndatasize()",
    "            mstore(sc_scratch, 0)",
    "            if iszero(gt(add(" ++ toString spot.offset ++ ", " ++ toString spot.width ++ "), returndatasize())) {",
    "                returndatacopy(sc_scratch, " ++ toString spot.offset ++ ", " ++ toString spot.width ++ ")",
    "            }",
    "            " ++ n "sc_c" ++ " := mload(sc_scratch)",
    "        }"] ++
  (if call > 1 then
    ["        if (sc_size1 > 31) {",
      "            sc_again = (sc_again + mload((sc_ret1 + 32)));",
      "        }"]
  else []) ++
  ["        sc_mix = (((sc_mix + " ++ n "sc_first" ++ ") + " ++ n "sc_n" ++ ") + " ++ n "sc_c" ++ ");"]

/-- Call `call`'s five slot writes. -/
private def storeLines (call : Nat) : List String :=
  let n := fun base => name base call
  let slot := fun offset => toString (5 * call - 3 + offset)
  ["        sstore(" ++ slot 0 ++ ", (" ++ n "sc_ok" ++ " + (2 * " ++ n "sc_size" ++ ")));",
    "        sstore(" ++ slot 1 ++ ", " ++ n "sc_first" ++ ");",
    "        sstore(" ++ slot 2 ++ ", " ++ n "sc_p" ++ ");",
    "        sstore(" ++ slot 3 ++ ", " ++ n "sc_n" ++ ");",
    "        sstore(" ++ slot 4 ++ ", " ++ n "sc_c" ++ ");"]

/-- The terms of the sum, in the order the slots hold them. -/
private def sumTerms (calls : Nat) : List String :=
  ["sload(0)", "sc_z0"] ++ (List.range calls).flatMap (fun index =>
    let n := fun base => name base (index + 1)
    [n "sc_ok", "(2 * " ++ n "sc_size" ++ ")", n "sc_first", n "sc_p", n "sc_n", n "sc_c"]) ++ ["sc_again"]

private def sumExpression (calls : Nat) : String :=
  match sumTerms calls with
  | [] => "0"
  | first :: rest => rest.foldl (fun total term => "(" ++ total ++ " + " ++ term ++ ")") first

/-- The child's source: the step's helpers and entry, then the contract. -/
def childSource (step : Solcore.Synthesis.Core.Aggregates.CheckedDAG) : Except EmitError String := do
  let mut names : List String := []
  let mut child := stdImports ++
    [AggregateRenderer.opcodeImportWith ["sload", "sstore", "mstore", "return_", "revert_"]
      (step.helpers ++ [step.entry]), ""]
  for (body, index) in step.helpers.zipIdx do
    let rendered ← AggregateRenderer.render names .word [.word "sc_arg"] 4 0 body
    let result ← AggregateRenderer.requireValue rendered
    let helper := "sc_fn" ++ toString index
    child := child ++ ["function " ++ helper ++ "(sc_arg: word) returns (word) {"] ++
      rendered.lines ++ ["    return " ++ result ++ ";", "}", ""]
    names := helper :: names
  let entry ← AggregateRenderer.render names .word [.word "sc_arg"] 4 0 step.entry
  let result ← AggregateRenderer.requireValue entry
  child := child ++ ["function sc_step(sc_arg: word) returns (word) {"] ++
    entry.lines ++ ["    return " ++ result ++ ";", "}", "",
    "contract " ++ Solcore.Synthesis.Source.CallReturn.childContractName ++ " {",
    "    function get(x: uint256) public returns (uint256) {",
    "        let sc_x: word = Typedef.rep(x);",
    "        let sc_o: word = sload(0);",
    "        let sc_c: word = (sload(1) + 1);",
    "        let sc_r: word = sc_step((sc_x + sc_o));",
    "        sstore(0, sc_r);",
    "        sstore(1, sc_c);",
    "        let sc_len: word = 0;",
    "        assembly {",
    "            sc_len := and(shr(1, sc_x), 127)",
    "            if gt(sc_len, " ++ toString Solcore.Synthesis.Core.CallSequence.capacity ++ ") { sc_len := " ++
      toString Solcore.Synthesis.Core.CallSequence.capacity ++ " }",
    "        }",
    "        let sc_d0: word = (sc_r * " ++ multiplierLiteral ++ ");",
    "        let sc_d1: word = ((sc_c * " ++ multiplierLiteral ++ ") ^ sc_x);",
    "        let sc_d2: word = (sc_d0 ^ sc_d1);",
    "        let sc_p: word = allocate_memory(96);",
    "        mstore(sc_p, sc_d0);",
    "        mstore((sc_p + 32), sc_d1);",
    "        mstore((sc_p + 64), sc_d2);",
    "        if ((sc_x & 1) == 1) {",
    "            revert_(sc_p, sc_len);",
    "        }",
    "        return_(sc_p, sc_len);",
    "        return uint256(0);",
    "    }",
    "}"]
  return String.intercalate "\n" child ++ "\n"

def emit (plan : CheckedPlan) : Except EmitError EmittedContracts := do
  let childText ← childSource plan.step
  let calls := plan.calls
  let parent := stdImports ++
    [AggregateRenderer.opcodeImportWith ["sload", "sstore", "mstore", "mload", "revert_"] [], "",
    "contract " ++ Solcore.Synthesis.Source.CallReturn.parentContractName ++ " {",
    "    function run(target: uint256, input: uint256) public returns (uint256) {",
    "        let sc_target: word = Typedef.rep(target);",
    "        let sc_input: word = Typedef.rep(input);",
    "        sstore(0, (sload(0) + sc_input));",
    "        let sc_scratch: word = allocate_memory(32);",
    "        let sc_z0: word = 1;",
    "        let sc_mix: word = 0;",
    "        assembly {",
    "            mstore(sc_scratch, 0)",
    "            returndatacopy(sc_scratch, 0, 0)",
    "            sc_z0 := mload(sc_scratch)",
    "            sc_mix := shr(32, sc_input)",
    "        }",
    "        let sc_again: word = 0;",
    "        let sc_ret1: word = 0;",
    "        let sc_size1: word = 0;"] ++
    (plan.windows.zipIdx.flatMap fun (spot, index) => callLines (index + 1) spot) ++
    ["        sstore(1, sc_z0);"] ++
    ((List.range calls).flatMap fun index => storeLines (index + 1)) ++
    ["        sstore(" ++ toString (5 * calls + 2) ++ ", sc_again);",
    "        let sc_sum: word = " ++ sumExpression calls ++ ";",
    "        let sc_rev: word = 0;",
    "        assembly {",
    "            sc_rev := and(shr(24, sc_input), 1)",
    "        }",
    "        if (sc_rev == 1) {",
    "            mstore(0, sc_sum);",
    "            revert_(0, 32);",
    "        }",
    "        return uint256(sc_sum);",
    "    }",
    "}"]
  return {
    parentSource := String.intercalate "\n" parent ++ "\n"
    childSource := childText
  }

end Solcore.Synthesis.Source.CallSequence
end

section
-- leanmerge: from Solcore.Synthesis.Source.CallBranchEmitter
/-! Emit the call-branch protocol as two sources with one contract each, under
the call-return profile's wrapper names and methods. The child is the
call-sequence profile's child.

The parent `SynthesizedReturnCaller` has one method `run(uint256 target,
uint256 input)`. It writes `slot 0 + input` to slot 0; in inline Yul it copies
zero bytes at offset 0 into a zeroed scratch Word and reads it back, and takes
`mix = input >> 32`. For each site it reads `returndatasize()` in inline Yul,
then a branch calls when its control bit is set, and a loop calls while its
counter is below its limit and, read in inline Yul, `returndatasize()` differs
from its stop length. Each call goes through std's `raw_call` with the payload
`0x9507d39a ‖ x`, keeps the flag plus twice the copy's length and the copy's
first Word, then reads `returndatasize()` and the call window with a guarded
`returndatacopy`; after the site it reads `returndatasize()` and the exit
window. It writes every slot at the end, sums them and reverts with the sum
under bit 30 of the input. No emitter proof covers these wrappers. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.CallBranch

open Solcore.Synthesis.Core.CallBranch (CheckedPlan Site Kind)
open Solcore.Synthesis.Core.CallSequence (Window)
open Solcore.Synthesis.Source.CallReturn (EmittedContracts)

def emitterVersion : String := "solcore-source-call-branches-v1"
def wrapperVersion : String := "solcore-call-branches-contracts-v1"

private def literal (value : Nat) : String := "0x" ++ String.ofList (Nat.toDigits 16 value)

private def stdImports : List String := ["import * from std;", "import * from std.dispatch;"]

private def indent (depth : Nat) (lines : List String) : List String :=
  lines.map fun line => String.ofList (List.replicate (4 * depth) ' ') ++ line

/-- One call: the argument from `mix` and the class byte the expression names,
the call through std's `raw_call`, and the flag plus twice the size and the
first Word into `k` and `f`. -/
private def callLines (classExpr k f : String) : List String :=
  ["let sc_class: word = 0;",
    "assembly {",
    "    sc_class := " ++ classExpr,
    "}",
    "let sc_x: word = ((sc_mix * 256) + sc_class);",
    "let sc_payload: word = allocate_memory(68);",
    "mstore(sc_payload, 36);",
    "mstore((sc_payload + 32), " ++
      literal (Solcore.Synthesis.Core.CallBranch.getSelector * 2 ^ 224) ++ ");",
    "mstore((sc_payload + 36), sc_x);",
    "let sc_data: memory<bytes> = Typedef.abs(sc_payload);",
    "match (raw_call(address(sc_target), uint256(0), sc_data)) {",
    "    case (ok, ret) {",
    "        let sc_ret: word = Typedef.rep(ret);",
    "        let sc_size: word = mload(sc_ret);",
    "        " ++ k ++ " = (frombool(ok) + (2 * sc_size));",
    "        if (sc_size > 31) {",
    "            " ++ f ++ " = mload((sc_ret + 32));",
    "        }",
    "    }",
    "}",
    "sc_calls = (sc_calls + 1);"]

/-- `returndatasize()` into `n` and the window into `v`, in inline Yul. -/
private def readLines (n v : String) (spot : Window) : List String :=
  ["assembly {",
    "    " ++ n ++ " := returndatasize()",
    "    mstore(sc_scratch, 0)",
    "    if iszero(gt(add(" ++ toString spot.offset ++ ", " ++ toString spot.width ++ "), returndatasize())) {",
    "        returndatacopy(sc_scratch, " ++ toString spot.offset ++ ", " ++ toString spot.width ++ ")",
    "    }",
    "    " ++ v ++ " := mload(sc_scratch)",
    "}"]

private def positionName (base : String) (position : Nat) : String := base ++ toString position
private def siteName (base : String) (index : Nat) : String := base ++ toString index

/-- Site `index` at its first position `first`. -/
private def siteLines (site : Site) (index first : Nat) : List String :=
  let p := siteName "sc_p" index
  let entry := ["assembly {", "    " ++ p ++ " := returndatasize()", "}"]
  let body := match site.kind with
    | .branch =>
        let k := positionName "sc_k" first
        let f := positionName "sc_f" first
        let n := positionName "sc_n" first
        let v := positionName "sc_v" first
        let bit := siteName "sc_bit" index
        ["let " ++ bit ++ ": word = 0;",
          "assembly {",
          "    " ++ bit ++ " := and(shr(" ++ toString (Solcore.Synthesis.Core.CallBranch.controlBit index) ++
            ", sc_input), 1)",
          "}",
          "if (" ++ bit ++ " == 1) {"] ++
        indent 1 (callLines ("and(shr(" ++ toString (8 * first) ++ ", sc_input), 255)") k f ++
          readLines n v site.callWindow ++
          ["sc_mix = (((sc_mix + " ++ f ++ ") + " ++ n ++ ") + " ++ v ++ ");"]) ++
        ["}"]
    | .loop =>
        let limit := siteName "sc_limit" index
        let counter := siteName "sc_counter" index
        let go := siteName "sc_go" index
        let condition := "    " ++ go ++ " := and(gt(" ++ limit ++ ", " ++ counter ++ "), iszero(eq(returndatasize(), " ++
          toString site.stop ++ ")))"
        let assign := (List.range site.bound).flatMap fun offset =>
          let position := first + offset
          ["if (" ++ counter ++ " == " ++ toString offset ++ ") {",
            "    " ++ positionName "sc_k" position ++ " = sc_k;",
            "    " ++ positionName "sc_f" position ++ " = sc_f;",
            "    " ++ positionName "sc_n" position ++ " = sc_n;",
            "    " ++ positionName "sc_v" position ++ " = sc_v;",
            "}"]
        ["let " ++ limit ++ ": word = 0;",
          "assembly {",
          "    " ++ limit ++ " := and(shr(" ++ toString (Solcore.Synthesis.Core.CallBranch.controlBit index) ++
            ", sc_input), 3)",
          "    if gt(" ++ limit ++ ", " ++ toString site.bound ++ ") { " ++ limit ++ " := " ++ toString site.bound ++ " }",
          "}",
          "let " ++ counter ++ ": word = 0;",
          "let " ++ go ++ ": word = 0;",
          "assembly {", condition, "}",
          "while (" ++ go ++ " == 1) {"] ++
        indent 1 (["let sc_k: word = 0;", "let sc_f: word = 0;"] ++
          callLines ("and(shr(mul(8, add(" ++ toString first ++ ", " ++ counter ++ ")), sc_input), 255)") "sc_k" "sc_f" ++
          ["let sc_n: word = 0;", "let sc_v: word = 0;"] ++
          readLines "sc_n" "sc_v" site.callWindow ++ assign ++
          ["sc_mix = (((sc_mix + sc_f) + sc_n) + sc_v);",
            counter ++ " = (" ++ counter ++ " + 1);",
            "assembly {", condition, "}"]) ++
        ["}"]
  let a := siteName "sc_a" index
  let u := siteName "sc_u" index
  entry ++ body ++ readLines a u site.exitWindow ++ ["sc_mix = ((sc_mix + " ++ a ++ ") + " ++ u ++ ");"]

/-- The slot values in slot order: slot 0, `z`, each site's three and each
position's four, and the call count. -/
private def slotTerms (sites : List Site) (positions : Nat) : List String :=
  ["sload(0)", "sc_z"] ++
    ((List.range sites.length).flatMap fun index => ["sc_p", "sc_a", "sc_u"].map (siteName · index)) ++
    ((List.range positions).flatMap fun position => ["sc_k", "sc_f", "sc_n", "sc_v"].map (positionName · position)) ++
    ["sc_calls"]

def emit (plan : CheckedPlan) : Except EmitError EmittedContracts := do
  let childText ← Solcore.Synthesis.Source.CallSequence.childSource plan.step
  let sites := plan.sites
  let positions := plan.positions
  let terms := slotTerms sites positions
  let declared := (terms.drop 1).filter (· != "sc_z") |>.filter (· != "sc_calls")
  let sum := match terms with
    | [] => "0"
    | first :: rest => rest.foldl (fun total term => "(" ++ total ++ " + " ++ term ++ ")") first
  let parent := stdImports ++
    [AggregateRenderer.opcodeImportWith ["sload", "sstore", "mstore", "mload", "revert_"] [], "",
    "contract " ++ Solcore.Synthesis.Source.CallReturn.parentContractName ++ " {",
    "    function run(target: uint256, input: uint256) public returns (uint256) {",
    "        let sc_target: word = Typedef.rep(target);",
    "        let sc_input: word = Typedef.rep(input);",
    "        sstore(0, (sload(0) + sc_input));",
    "        let sc_scratch: word = allocate_memory(32);",
    "        let sc_z: word = 1;",
    "        let sc_mix: word = 0;",
    "        assembly {",
    "            mstore(sc_scratch, 0)",
    "            returndatacopy(sc_scratch, 0, 0)",
    "            sc_z := mload(sc_scratch)",
    "            sc_mix := shr(32, sc_input)",
    "        }",
    "        let sc_calls: word = 0;"] ++
    declared.map (fun name => "        let " ++ name ++ ": word = 0;") ++
    indent 2 ((sites.zipIdx.flatMap fun (site, index) =>
      siteLines site index (Solcore.Synthesis.Core.CallBranch.firstPosition sites index))) ++
    ((terms.drop 1).zipIdx.map fun (term, slot) => "        sstore(" ++ toString (slot + 1) ++ ", " ++ term ++ ");") ++
    ["        let sc_sum: word = " ++ sum ++ ";",
    "        let sc_rev: word = 0;",
    "        assembly {",
    "            sc_rev := and(shr(" ++ toString Solcore.Synthesis.Core.CallBranch.revertBit ++ ", sc_input), 1)",
    "        }",
    "        if (sc_rev == 1) {",
    "            mstore(0, sc_sum);",
    "            revert_(0, 32);",
    "        }",
    "        return uint256(sc_sum);",
    "    }",
    "}"]
  return {
    parentSource := String.intercalate "\n" parent ++ "\n"
    childSource := childText
  }

end Solcore.Synthesis.Source.CallBranch
end

section
-- leanmerge: from Solcore.Synthesis.Stateful.CallReturnExecution
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
end

section
-- leanmerge: from Solcore.Synthesis.Source.CallReturnCases
/-! A call-return case retains the three original checked Core contracts, the
child's returned value with its delivery, and a role-based transaction
sequence. Every replay reconstructs the contracts from the plan. Each
transaction records std's prescribed rejection, computed by the byte-level
model over the child's bytes; saved outcomes are never an oracle, and the
call-and-resume convention selects the committed worlds. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.CallReturn
open Lean Solcore.Core Solcore.Synthesis.Core
open Solcore.Synthesis.Core.CallReturn (CheckedPlan Kind Returned Delivery Malformation)
open Solcore.Synthesis.Core.EnumReturn (Constructor Shape)
open Solcore.Synthesis.Stateful.CallReturnExecution (Transaction Bindings)
open Solcore.ContractRuntime (EnumPayload encodeBytesText)

def caseSchema : String := "solcore-lean.semantic-call-return-case.v1"
def planSchema : String := "solcore-lean.call-return-plan.v1"
def profileVersion : String := "stateful-call-returns-v1/call-return-sequence-seed-v1"
def templateVersion : String := "std-raw-call-decode-record-step-revert-odd-input-v1"
def corpusSchema : String := "solcore-lean.semantic-call-return-corpus.v1"

abbrev boundaryInputs := NestedCall.boundaryInputs
abbrev validId := Storage.validId
abbrev validTransactions := Storage.validTransactions

/-- The `bytes` lengths drawn half of the time, std's boundaries. -/
def lengthBank : List Nat := [0, 1, 31, 32, 33, 63, 64]

/-- Random steps and the child's shell stay within the largest step budget. -/
def maxStepNodes : Nat := 512

private def w (value : Nat) : Word := Word.ofNatModulo value

/-- The child's shell and its step, which a node budget bounds. -/
def budgetNodes (plan : CheckedPlan) : Nat :=
  CallReturn.childShellNodes plan.returned + Wire.programNodes plan.step.program

structure CheckedScenario where private mk ::
  plan : CheckedPlan
  transactions : List Transaction
  valid : validTransactions transactions
  bounded : Wire.programNodes plan.childProgram ≤ CallReturn.maxContractNodes ∧
    Wire.programNodes plan.resumeProgram ≤ CallReturn.maxContractNodes ∧
    Wire.programNodes plan.callProgram ≤ CallReturn.maxContractNodes

def checkedScenario (plan : CheckedPlan) (transactions : List Transaction) : Except String CheckedScenario := do
  if valid : validTransactions transactions then
    if bounded : Wire.programNodes plan.childProgram ≤ CallReturn.maxContractNodes ∧
        Wire.programNodes plan.resumeProgram ≤ CallReturn.maxContractNodes ∧
        Wire.programNodes plan.callProgram ≤ CallReturn.maxContractNodes then
      return ⟨plan, transactions, valid, bounded⟩
    else throw "call-return contracts exceed the 1024-node contract limit"
  else throw s!"call-return scenario requires 1..{Stateful.Sequence.maxTransactions} transactions with distinct valid IDs"

/-! ### Plans -/

def malformationKinds : List String := ["truncate", "trailing", "offset", "length", "tag", "tagCut", "tail", "narrow"]

def kindOf : Malformation → String
  | .truncate _ => "truncate"
  | .trailing _ _ => "trailing"
  | .offset _ => "offset"
  | .length _ => "length"
  | .tag _ => "tag"
  | .tagCut _ => "tagCut"
  | .tail _ => "tail"
  | .narrow => "narrow"

def malformationJson : Malformation → Json
  | .truncate kept => Json.mkObj [("kind", toJson "truncate"), ("kept", toJson kept)]
  | .trailing count pattern => Json.mkObj [("kind", toJson "trailing"), ("count", toJson count),
      ("pattern", toJson (Stateful.StdCalldata.patternNames.getD pattern "zeros"))]
  | .offset value => Json.mkObj [("kind", toJson "offset"), ("value", toJson (toString value.val))]
  | .length value => Json.mkObj [("kind", toJson "length"), ("value", toJson (toString value.val))]
  | .tag value => Json.mkObj [("kind", toJson "tag"), ("value", toJson (toString value.val))]
  | .tagCut value => Json.mkObj [("kind", toJson "tagCut"), ("value", toJson (toString value.val))]
  | .tail value => Json.mkObj [("kind", toJson "tail"), ("value", toJson (toString value.val))]
  | .narrow => Json.mkObj [("kind", toJson "narrow")]

private def wordText (text : String) : Except String Word := do
  unless text.length ≤ 78 do throw "a Word exceeds 78 decimal digits"
  Input.inputWord text

def decodeMalformation (json : Json) : Except String Malformation := do
  match ← json.getObjValAs? String "kind" with
  | "truncate" => return .truncate (← json.getObjValAs? Nat "kept")
  | "trailing" =>
      let some pattern := Stateful.StdCalldata.patternNames.idxOf? (← json.getObjValAs? String "pattern")
        | throw "unsupported trailing pattern"
      return .trailing (← json.getObjValAs? Nat "count") pattern
  | "offset" => return .offset (← wordText (← json.getObjValAs? String "value"))
  | "length" => return .length (← wordText (← json.getObjValAs? String "value"))
  | "tag" => return .tag (← wordText (← json.getObjValAs? String "value"))
  | "tagCut" => return .tagCut (← wordText (← json.getObjValAs? String "value"))
  | "tail" => return .tail (← wordText (← json.getObjValAs? String "value"))
  | "narrow" => return .narrow
  | _ => throw "unsupported malformation kind"

def deliveryJson : Delivery → Json
  | .typed => Json.mkObj [("kind", toJson "typed")]
  | .raw malformation => Json.mkObj [("kind", toJson "raw"), ("malformation", malformationJson malformation)]

def decodeDelivery (json : Json) : Except String Delivery := do
  match ← json.getObjValAs? String "kind" with
  | "typed" => return .typed
  | "raw" => return .raw (← decodeMalformation (← json.getObjVal? "malformation"))
  | _ => throw "unsupported delivery"

/-- The kind's name, as the plan records it. -/
def kindName : Kind → String
  | .tuple _ => "tuple"
  | .bytes => "bytes"
  | .enum shape => if shape.dynamic then "dynamic-enum" else "static-enum"

def planJson (plan : CheckedPlan) : Json :=
  let returned := plan.returned
  Json.mkObj ([("schema", toJson planSchema), ("kind", toJson (kindName returned.kind))] ++
    (match returned.kind with
      | .tuple extra => [("arity", toJson (extra + 2))]
      | .enum shape => [("constructors", toJson (shape.constructors.map EnumReturn.constructorJson))]
      | .bytes => []) ++
    [("length", toJson returned.length), ("choice", toJson returned.choice),
      ("delivery", deliveryJson returned.delivery), ("stepProgram", Wire.encodeProgram plan.step.program)])

private def payloadOf? (fields : String) : Option EnumPayload :=
  [EnumPayload.noWords, .oneWord, .twoWords, .boundedBytes].find?
    (Solcore.Synthesis.Core.EnumReturn.fieldSignature · == fields)

def checkedPlan (json : Json) : Except String CheckedPlan := do
  unless (← json.getObjValAs? String "schema") = planSchema do throw "unsupported call-return plan schema"
  let kind ← match ← json.getObjValAs? String "kind" with
    | "tuple" =>
        let arity ← json.getObjValAs? Nat "arity"
        unless 2 ≤ arity && arity ≤ 4 do throw "a returned tuple has two to four Words"
        pure (Kind.tuple (arity - 2))
    | "bytes" => pure .bytes
    | "static-enum" | "dynamic-enum" =>
        let rows ← (← json.getObjVal? "constructors").getArr?
        let constructors ← rows.toList.mapM fun row => do
          let some payload := payloadOf? (← row.getObjValAs? String "fields") | throw "unsupported constructor fields"
          return ({name := ← row.getObjValAs? String "name", payload} : Constructor)
        let some shape := EnumReturn.Shape.ofList? constructors | throw "an enum needs at least two constructors"
        pure (.enum shape)
    | _ => throw "unsupported returned kind"
  let returned : Returned := ⟨kind, ← json.getObjValAs? Nat "length", ← json.getObjValAs? Nat "choice",
    ← decodeDelivery (← json.getObjVal? "delivery")⟩
  let step ← Aggregate.checkedFunction (← json.getObjVal? "stepProgram")
  let some plan := CheckedPlan.ofParts? step returned
    | throw "call-return plan needs a valid returned value, a malformation that applies, and full host-Core admission"
  unless json == planJson plan do throw "call-return plan differs from its canonical checked representation"
  return plan

/-! ### Transactions and their prescribed rejections -/

/-- std's prescribed rejection of each transaction's return data, from the
byte-level model; none when the child reverts or std accepts. -/
def prescribed (plan : CheckedPlan) (fuel : Nat) (transactions : List Transaction) :
    Except String (List (Option ByteArray)) := do
  let some rows := Stateful.CallReturnExecution.model plan fuel transactions
    | throw "call-return model exhausted Core fuel"
  return rows.map (·.rejection)

def rejectionJson : Option ByteArray → Json
  | none => Json.null
  | some data => toJson (encodeBytesText data)

def transactionJson (tx : Transaction) (rejection : Option ByteArray) : Json := Json.mkObj [
  ("id", toJson tx.id), ("input", toJson (toString tx.input.val)),
  ("value", toJson "0"), ("target", toJson "parent"), ("callee", toJson "child"),
  ("stdRejection", rejectionJson rejection)]

def transactionsJson (plan : CheckedPlan) (fuel : Nat) (transactions : List Transaction) : Except String Json := do
  let rejections ← prescribed plan fuel transactions
  return toJson ((transactions.zip rejections).map fun (tx, rejection) => transactionJson tx rejection)

/-- The transactions' identities and inputs; their prescribed rejections are
checked against the model once the plan is known. -/
def decodeSequence (json : Json) : Except String (List Transaction) := do
  let rows ← json.getArr?
  unless 1 ≤ rows.size && rows.size ≤ Stateful.Sequence.maxTransactions do
    throw s!"transaction count must be between 1 and {Stateful.Sequence.maxTransactions}"
  let transactions ← rows.toList.mapM fun row => do
    let input ← wordText (← row.getObjValAs? String "input")
    return ({id := ← row.getObjValAs? String "id", input} : Transaction)
  unless validTransactions transactions do throw "call-return scenario requires distinct valid transaction IDs"
  return transactions

/-- An imported sequence: exactly each transaction's ID and input. -/
def decodeImportedSequence (json : Json) : Except String (List Transaction) := do
  let transactions ← decodeSequence json
  unless json == toJson (transactions.map fun tx =>
      Json.mkObj [("id", toJson tx.id), ("input", toJson (toString tx.input.val))]) do
    throw "imported transactions carry exactly their ID and input"
  return transactions

def decodeTransactions (plan : CheckedPlan) (fuel : Nat) (json : Json) : Except String (List Transaction) := do
  let transactions ← decodeSequence json
  unless json == (← transactionsJson plan fuel transactions) do
    throw "transactions differ from their canonical ID, input, role metadata or prescribed rejection"
  return transactions

/-! ### Cases -/

def programsJson (plan : CheckedPlan) : Json := Json.mkObj [
  ("parentCall", Wire.encodeProgram plan.callProgram), ("parentResume", Wire.encodeProgram plan.resumeProgram),
  ("child", Wire.encodeProgram plan.childProgram)]

def contractsJson : Json := Json.mkObj [
  ("parent", Json.mkObj [("name", toJson parentContractName), ("method", toJson "run"),
    ("signature", toJson parentMethodSignature), ("selector", toJson parentSelector),
    ("deployPath", toJson parentDeployPath), ("runtimePath", toJson parentRuntimePath),
    ("constructorCalldata", toJson "0x"), ("constructorValue", toJson "0")]),
  ("child", Json.mkObj [("name", toJson childContractName), ("method", toJson "get"),
    ("signature", toJson childMethodSignature), ("selector", toJson childSelector),
    ("deployPath", toJson childDeployPath), ("runtimePath", toJson childRuntimePath),
    ("constructorCalldata", toJson "0x"), ("constructorValue", toJson "0")])]

def initialStateJson : Json := Json.mkObj [
  ("accounts", toJson [
    Json.mkObj [("role", toJson "parent"), ("balance", toJson "0"), ("storage", toJson ([] : List Json))],
    Json.mkObj [("role", toJson "child"), ("balance", toJson "0"), ("storage", toJson ([] : List Json))]]),
  ("callerBalance", toJson "0")]

def observedSlotsJson : Json := Json.mkObj [
  ("parent", toJson (Stateful.CallReturnExecution.parentSlots.map fun slot => toString slot.val)),
  ("child", toJson (Stateful.CallReturnExecution.childSlots.map fun slot => toString slot.val))]

def makeCase (scenario : CheckedScenario) (emitted : EmittedContracts) (origin : Json) (fuel : Nat)
    (revision : GeneratorRevision := .v1) (mask : FeatureMask := FeatureMask.all) : Except String Json := do
  return Json.mkObj [
    ("schema", toJson caseSchema), ("callReturnPlan", planJson scenario.plan),
    ("programs", programsJson scenario.plan),
    ("sources", Json.mkObj [("parent", toJson emitted.parentSource), ("child", toJson emitted.childSource)]),
    ("transactions", ← transactionsJson scenario.plan fuel scenario.transactions),
    ("initialState", initialStateJson), ("observedSlots", observedSlotsJson),
    ("provenance", Json.mkObj <| swarmField revision mask ++ [
      ("origin", origin), ("profileVersion", toJson profileVersion),
      ("functionVersion", toJson CallReturn.childVersion), ("parentVersion", toJson CallReturn.parentVersion),
      ("templateVersion", toJson templateVersion),
      ("stepProfileVersion", toJson Aggregate.profileVersion),
      ("stepFunctionVersion", toJson Aggregates.version),
      ("stepTemplateVersion", toJson Aggregate.templateVersion),
      ("generatorVersion", toJson revision.version),
      ("emitterVersion", toJson emitterVersion), ("wrapperVersion", toJson wrapperVersion),
      ("features", toJson scenario.plan.step.features)]),
    ("contracts", contractsJson), ("executionFuel", toJson fuel)]

def emitCase (scenario : CheckedScenario) (origin : Json) (fuel : Nat)
    (revision : GeneratorRevision := .v1) (mask : FeatureMask := FeatureMask.all) : Except String Json := do
  unless fuel ≤ 10000000 do throw "execution fuel exceeds limit"
  let emitted ← (emit scenario.plan).mapError reprStr
  makeCase scenario emitted origin fuel revision mask

private def decodeProgram (json : Json) : Except String Wire.Program :=
  (Wire.decodeProgramWithBudget {maxDepth := 512, maxNodes := CallReturn.maxContractNodes, maxIntegerBytes := 4096}
    json).mapError (fun
    | .protocol error => error.toJson.compress
    | .exhausted exhaustion => "Core decode budget exceeded: " ++ reprStr exhaustion)

/-- Every origin must reconstruct the three fixed host contracts, including
imports and reductions. Arbitrary well-typed programs are not admissible
replacements. -/
def caseProgram (json : Json) : Except String CheckedScenario := do
  unless (← json.getObjValAs? String "schema") = caseSchema do throw "unsupported semantic call-return case schema"
  let plan ← checkedPlan (← json.getObjVal? "callReturnPlan")
  let fuel ← json.getObjValAs? Nat "executionFuel"
  unless fuel ≤ 10000000 do throw "saved execution fuel exceeds limit"
  let transactions ← decodeTransactions plan fuel (← json.getObjVal? "transactions")
  let originals ← json.getObjVal? "programs"
  for (name, expected) in [("parentCall", plan.callProgram), ("parentResume", plan.resumeProgram),
      ("child", plan.childProgram)] do
    let program ← decodeProgram (← originals.getObjVal? name)
    unless Wire.encodeProgram program == Wire.encodeProgram expected do
      throw "saved original Core program differs from its canonical call-return plan"
  unless originals == programsJson plan do throw "saved program roles are not canonical"
  unless (← json.getObjVal? "initialState") == initialStateJson do throw "initial accounts must be empty and unfunded"
  unless (← json.getObjVal? "observedSlots") == observedSlotsJson do
    throw "observed slots must be the parent's 0 to 6 and the child's 0 and 1"
  checkedScenario plan transactions

def observe (scenario : CheckedScenario) (bindings : Bindings) (fuel : Nat) : Json :=
  Stateful.CallReturnExecution.observe scenario.plan scenario.transactions bindings fuel

/-! ### Generation -/

/-- SplitMix64's finalizer. The generator's draws are affine in its start, so
consecutive seeds would otherwise start streams whose draws step by a fixed
residue. -/
private def mixed (value : Nat) : Nat :=
  let z := value % 2 ^ 64
  let z := (z ^^^ (z >>> 30)) * 0xbf58476d1ce4e5b9 % 2 ^ 64
  let z := (z ^^^ (z >>> 27)) * 0x94d049bb133111eb % 2 ^ 64
  z ^^^ (z >>> 31)

/-- High halves of successive draws from the stream that starts at the mixed
`seed` xor `domain`, each below its bound. -/
private def boundedDraws (seed : Seed) (domain : Nat) (bounds : List Nat) : List Nat := Id.run do
  let mut state := Seed.ofNat (mixed (seed.toNat ^^^ domain))
  let mut values : Array Nat := #[]
  for bound in bounds do
    let (value, next) := state.draw
    values := values.push (value.toNat / 2 ^ 32 % bound)
    state := next
  return values.toList

/-- The kind, the tuple's arity, a length selector and a uniform length, the
choice, the delivery's selector, the malformation's kind and its bank entry. -/
def shapeBounds : List Nat := [8, 3, 14, 65, 12, 3, 12, 16]

def shapeChoices (seed : Seed) : List Nat := boundedDraws seed 0x7265742d73686170 shapeBounds

/-- A tuple three times in eight, `bytes` twice and an enum three times, its
shape drawn as for the enum-return profile. -/
def generatedKind (seed : Seed) : Kind :=
  let choices := shapeChoices seed
  match choices.getD 0 0 with
  | 0 | 1 | 2 => .tuple (choices.getD 1 0)
  | 3 | 4 => .bytes
  | _ => .enum (EnumReturn.generatedShape seed)

/-- The returned value with every field its kind does not use set to zero. -/
def canonicalReturned (returned : Returned) : Returned :=
  let choice := match returned.kind with
    | .enum shape => returned.choice % shape.constructors.length
    | _ => 0
  let base := {returned with choice}
  {base with length := if base.carriesBytes then base.length else 0}

private def uniqueNats (values : List Nat) : List Nat := values.eraseDups

/-- The malformations of a kind that apply, in bank order. -/
def malformationBank (returned : Returned) (kind : String) : List Malformation :=
  let typed := {returned with delivery := .typed}
  let n := CallReturn.canonicalSize typed
  let valid := fun (malformation : Malformation) => malformation.valid typed
  let words := fun (values : List Nat) => (uniqueNats values).map w
  (match kind with
    | "truncate" =>
        let boundaries := (List.range ((n + 31) / 32)).filterMap fun index =>
          if 0 < index && 32 * index < n then some index else none
        (uniqueNats (0 :: (boundaries.flatMap fun index => [32 * index - 1, 32 * index]) ++ [n - 1])).map Malformation.truncate
    | "trailing" => [1, 31, 32, 33].flatMap fun count => [0, 1, 2].map (Malformation.trailing count)
    | "offset" => (words [0, 1, n - 31, n, 2 ^ 255, 2 ^ 256 - 32]).map Malformation.offset
    | "length" =>
        let length := returned.length
        let fits := n - (CallReturn.lengthPosition typed + 32)
        (words ([0] ++ (if length > 0 then [length - 1] else []) ++ [length + 1, fits, fits + 1, 2 ^ 256 - 1])).map
          Malformation.length
    | "tag" | "tagCut" =>
        let tag := match returned.kind with
          | .enum shape => (EnumReturn.tag (CallReturn.chosen shape returned.choice)).val
          | _ => 0
        let values := words [0, tag + 1, tag ^^^ 2 ^ 255, 2 ^ 256 - 1]
        if kind == "tag" then values.map Malformation.tag else values.map Malformation.tagCut
    | "tail" => (words [0, 32, n - 32 + 1, 2 ^ 256 - 1]).map Malformation.tail
    | "narrow" => [.narrow]
    | _ => []).filter valid

def applicableKinds (returned : Returned) : List String :=
  malformationKinds.filter fun kind => !(malformationBank returned kind).isEmpty

/-- Typed when the delivery draw is 0, otherwise raw with a kind uniformly
among those that apply and then an entry of its bank uniformly. -/
def generatedReturned (seed : Seed) : Returned :=
  let choices := shapeChoices seed
  let selector := choices.getD 2 0
  let length := if selector < lengthBank.length then lengthBank.getD selector 0 else choices.getD 3 0
  let typed := canonicalReturned ⟨generatedKind seed, length, choices.getD 4 0, .typed⟩
  if choices.getD 5 0 == 0 then typed
  else match applicableKinds typed with
    | [] => typed
    | kinds =>
        let kind := kinds.getD (choices.getD 6 0 % kinds.length) "truncate"
        let entries := malformationBank typed kind
        match entries.getD (choices.getD 7 0 % entries.length) (.truncate 0) with
        | malformation => {typed with delivery := .raw malformation}

/-- Three inputs from the boundary bank. -/
def sequenceBounds : List Nat := [10, 10, 10]

def sequenceChoices (seed : Seed) : List Nat := boundedDraws seed 0x7265742d73657173 sequenceBounds

def blockTransactions (seed : Seed) (first : Nat) : List Transaction :=
  (sequenceChoices seed).zipIdx.map fun (choice, index) =>
    ⟨"tx-" ++ toString (first + index), boundaryInputs.getD choice Word.zero⟩

/-- The first `count` transactions of the seed's consecutive blocks. -/
def generatedTransactions (seed : Seed) (count : Nat := 3) : List Transaction :=
  Stateful.Sequence.blocks blockTransactions seed count

/-- The child's shell lies inside the budget with the step, which the complete
measure bounds again. -/
def generatedScenario (seed : Seed) (nodes : Nat) (revision : GeneratorRevision := .v1)
    (transactions : Nat := 3) : Except String (CheckedScenario × Json) := do
  Stateful.Sequence.checkCount transactions
  let returned := generatedReturned seed
  let shell := CallReturn.childShellNodes returned
  unless nodes ≤ maxStepNodes && shell < nodes do
    throw "node budget is too small for the call-return child or exceeds 512"
  let (step, stepOrigin) ← Aggregate.generatedFunction seed (nodes - shell) revision
  let some plan := CheckedPlan.ofParts? step returned | throw "generated call-return plan failed full Core admission"
  let scenario ← checkedScenario plan (generatedTransactions seed transactions)
  unless budgetNodes scenario.plan ≤ nodes do throw "call-return child exceeds its requested node budget"
  return (scenario, Stateful.Sequence.recordCount (Json.mkObj [
    ("kind", toJson "call-return-generated"), ("seed", toJson (toString seed.toNat)),
    ("finalSeed", ← stepOrigin.getObjVal? "finalSeed"), ("maxProgramNodes", toJson nodes),
    ("stepOrigin", stepOrigin), ("shapeChoices", toJson (shapeChoices seed)),
    ("sequenceChoices", toJson (Stateful.Sequence.blockChoices sequenceChoices seed transactions))]) transactions)

private def rowStatus (row : Json) : Option String := (row.getObjValAs? String "status").toOption

/-- The history must complete with the model's outcomes. -/
def validateGenerated (scenario : CheckedScenario) (fuel : Nat) : Except String Unit := do
  Aggregate.inputSensitive scenario.plan.step fuel
  let observed := observe scenario Solcore.Synthesis.Stateful.NestedCallExecution.fixtureBindings fuel
  let rows ← observed.getObjValAs? (List Json) "transactions"
  unless (← observed.getObjValAs? String "status") = "complete" do
    if rows.any (fun row => rowStatus row == some "out-of-fuel") then throw "call-return history exhausted Core fuel"
    else throw "call-return history stopped without a permitted root completion"
  let some expected := Stateful.CallReturnExecution.model scenario.plan fuel scenario.transactions
    | throw "call-return history exhausted Core fuel"
  unless rows.map rowStatus == expected.map (fun row => some (if row.reverted then "reverted" else "returned")) do
    throw "call-return history did not follow its prescribed outcomes"

def generateCases (firstSeed : Seed) (nodes count attempts fuel : Nat)
    (revision : GeneratorRevision := .v1) (transactions : Nat := 3) : Json := Id.run do
  let mut cases : Array Json := #[]
  let mut excluded : Array Json := #[]
  let mut attempted := 0
  for index in List.range attempts do
    if cases.size < count then
      attempted := attempted + 1
      let seed := Seed.ofNat (firstSeed.toNat + index)
      let result := do
        unless fuel ≤ 10000000 do throw "execution fuel exceeds limit"
        let (scenario, origin) ← generatedScenario seed nodes revision transactions
        let emitted ← (emit scenario.plan).mapError reprStr
        validateGenerated scenario fuel
        makeCase scenario emitted (origin.setObjVal! "validationFuel" (toJson fuel)) fuel revision (revision.caseMask seed)
      match result with
      | .error error =>
          let resource := error == "boundary observation exhausted Core fuel" ||
            error == "call-return history exhausted Core fuel" || error == "call-return model exhausted Core fuel"
          excluded := excluded.push (Json.mkObj [
            ("seed", toJson (toString seed.toNat)), ("stage", toJson "call-return-profile"),
            ("reason", toJson error),
            ("code", toJson (if resource then "validation-out-of-fuel" else "profile-excluded")),
            ("category", toJson (if resource then "inconclusive-resource" else "excluded"))])
      | .ok case => cases := cases.push case
  return Json.mkObj [("schema", toJson corpusSchema),
    ("requested", toJson count), ("attempted", toJson attempted),
    ("status", toJson (if cases.size = count then "complete" else "generation-exhausted")),
    ("excluded", .arr excluded), ("cases", .arr cases)]

/-! ### Reductions -/

/-- A tuple's extra Words, then `bytes` and enums by their shape. -/
def kindWeight : Kind → Nat
  | .tuple extra => extra
  | .bytes => 3
  | .enum shape => 4 + EnumReturn.shapeWeight shape

/-- Nothing for a typed delivery, otherwise one plus the malformation's
position in its kind's bank, or one plus the bank's size outside it. -/
def deliveryWeight (returned : Returned) : Nat :=
  match returned.delivery with
  | .typed => 0
  | .raw malformation =>
      let bank := malformationBank returned (kindOf malformation)
      1 + (bank.idxOf? malformation).getD bank.length

def inputWeight (scenario : CheckedScenario) : Nat :=
  scenario.transactions.foldl (fun total transaction => total + transaction.input.val) 0

def scenarioComplexity (scenario : CheckedScenario) : Complexity := complexity scenario.plan.childProgram.body

/-- Transaction count, the kind, the delivery, the `bytes` length, the child's
size and literals, then the inputs. Every axis is a natural number and the
comparison is strictly lexicographic. -/
def StrictlySmaller (candidate source : CheckedScenario) : Prop :=
  candidate.transactions.length < source.transactions.length ∨
  (candidate.transactions.length = source.transactions.length ∧
    (kindWeight candidate.plan.returned.kind < kindWeight source.plan.returned.kind ∨
    (kindWeight candidate.plan.returned.kind = kindWeight source.plan.returned.kind ∧
      (deliveryWeight candidate.plan.returned < deliveryWeight source.plan.returned ∨
      (deliveryWeight candidate.plan.returned = deliveryWeight source.plan.returned ∧
        (candidate.plan.returned.length < source.plan.returned.length ∨
        (candidate.plan.returned.length = source.plan.returned.length ∧
          ((scenarioComplexity candidate).StrictlySmaller (scenarioComplexity source) ∨
          (scenarioComplexity candidate = scenarioComplexity source ∧
            inputWeight candidate < inputWeight source)))))))))

instance (candidate source : CheckedScenario) : Decidable (StrictlySmaller candidate source) := by
  unfold StrictlySmaller
  infer_instance

structure Reduction (source : CheckedScenario) where private mk ::
  candidate : CheckedScenario
  sameHelperCount : candidate.plan.step.helpers.length = source.plan.step.helpers.length
  sameBindings : Aggregate.bindingInventory candidate.plan.step = Aggregate.bindingInventory source.plan.step
  stableIds : (candidate.transactions.map (·.id)).Sublist (source.transactions.map (·.id))
  strict : StrictlySmaller candidate source

private def sealReduction (source : CheckedScenario) (step : Aggregates.CheckedDAG) (returned : Returned)
    (transactions : List Transaction) : Option (Reduction source) := do
  let plan ← CheckedPlan.ofParts? step returned
  let candidate ← (checkedScenario plan transactions).toOption
  if count : candidate.plan.step.helpers.length = source.plan.step.helpers.length then
    if bindings : Aggregate.bindingInventory candidate.plan.step = Aggregate.bindingInventory source.plan.step then
      if ids : (candidate.transactions.map (·.id)).Sublist (source.transactions.map (·.id)) then
        if strict : StrictlySmaller candidate source then some ⟨candidate, count, bindings, ids, strict⟩
        else none
      else none
    else none
  else none

/-- The returned value made canonical, with its malformation kept only when it
still applies. -/
def reanchor (returned : Returned) : Returned :=
  let typed := canonicalReturned {returned with delivery := .typed}
  match returned.delivery with
  | .typed => typed
  | .raw malformation => if malformation.valid typed then {typed with delivery := .raw malformation} else typed

private def moveDown (index value : Nat) : Nat := if value > index then value - 1 else value

/-- The next narrower fields: two Words to one, one Word to none and `bytes`
to none. -/
private def narrower : EnumPayload → Option EnumPayload
  | .twoWords => some .oneWord
  | .oneWord => some .noWords
  | .boundedBytes => some .noWords
  | .noWords => none

/-- Simpler kinds: an enum and `bytes` become a pair of Words, and a tuple
loses its last Word. -/
private def simpler : Kind → Option Kind
  | .enum _ | .bytes => some (.tuple 0)
  | .tuple (extra + 1) => some (.tuple extra)
  | .tuple 0 => none

/-- One-transaction removals, a dropped or earlier malformation, a shorter
length, a simpler kind, dropped and narrowed enum constructors, step
reductions, then per transaction each boundary input. Candidates still need
execution to establish that they preserve a finding. -/
def reductions (source : CheckedScenario) : List (Reduction source) := Id.run do
  let returned := source.plan.returned
  let mut raw : List (Aggregates.CheckedDAG × Returned × List Transaction) := []
  -- Removing one transaction comes first, from the last back: a long
  -- sequence loses the tail beyond a difference before the candidate limit.
  for index in (List.range source.transactions.length).reverse do
    raw := raw ++ [(source.plan.step, returned,
      (source.transactions.zipIdx.filter (fun (_, current) => current != index)).map Prod.fst)]
  if let .raw malformation := returned.delivery then
    raw := raw ++ [(source.plan.step, {returned with delivery := .typed}, source.transactions)]
    let bank := malformationBank returned (kindOf malformation)
    for earlier in bank.take ((bank.idxOf? malformation).getD bank.length) do
      raw := raw ++ [(source.plan.step, {returned with delivery := .raw earlier}, source.transactions)]
  for shorter in [0, returned.length / 2] do
    if shorter < returned.length then
      raw := raw ++ [(source.plan.step, reanchor {returned with length := shorter}, source.transactions)]
  if let some kind := simpler returned.kind then
    raw := raw ++ [(source.plan.step, reanchor {returned with kind, length := 0, choice := 0}, source.transactions)]
  if let .enum shape := returned.kind then
    for index in List.range shape.constructors.length do
      if index != returned.choice then
        if let some smaller := EnumReturn.Shape.ofList? (shape.constructors.eraseIdx index) then
          raw := raw ++ [(source.plan.step,
            reanchor {returned with kind := .enum smaller, choice := moveDown index returned.choice}, source.transactions)]
    for index in List.range shape.constructors.length do
      if let some constructor := shape.constructors[index]? then
        if let some payload := narrower constructor.payload then
          if let some smaller := EnumReturn.Shape.ofList? (shape.constructors.set index {constructor with payload}) then
            raw := raw ++ [(source.plan.step, reanchor {returned with kind := .enum smaller}, source.transactions)]
  for reduced in Aggregate.reductions ⟨source.plan.step, Word.zero⟩ do
    raw := raw ++ [(reduced.candidate.function, returned, source.transactions)]
  for index in List.range source.transactions.length do
    for input in boundaryInputs do
      let transactions := source.transactions.zipIdx.map fun (transaction, current) =>
        if current == index then {transaction with input := input} else transaction
      raw := raw ++ [(source.plan.step, returned, transactions)]
  let mut seen : List String := []
  let mut result := []
  for (step, returned, transactions) in raw do
    if let some reduced := sealReduction source step returned transactions then
      let identity := (Json.mkObj [("plan", planJson reduced.candidate.plan),
        ("transactions", toJson (reduced.candidate.transactions.map fun tx => toString tx.input.val ++ tx.id))]).compress
      if !seen.contains identity then
        seen := identity :: seen
        result := result ++ [reduced]
  return result

private def sequenceJson (transactions : List Transaction) : Json :=
  toJson (transactions.map fun tx => Json.mkObj [("id", toJson tx.id), ("input", toJson (toString tx.input.val))])

private def reducedOrigin (parent : CheckedScenario) : Json := Json.mkObj [
  ("kind", toJson "reduced"), ("parentPlan", planJson parent.plan),
  ("parentPrograms", programsJson parent.plan), ("parentTransactions", sequenceJson parent.transactions)]

def replayCase (json : Json) (fuel : Nat) : Except String Json := do
  unless fuel ≤ 10000000 do throw "execution fuel exceeds limit"
  let admitted ← caseProgram json
  let provenance ← json.getObjVal? "provenance"
  let revision := savedRevision provenance
  let mask ← savedMask provenance revision
  for (name, expected) in [
      ("generatorVersion", revision.version), ("profileVersion", profileVersion),
      ("functionVersion", CallReturn.childVersion), ("parentVersion", CallReturn.parentVersion),
      ("templateVersion", templateVersion),
      ("stepProfileVersion", Aggregate.profileVersion), ("stepFunctionVersion", Aggregates.version),
      ("stepTemplateVersion", Aggregate.templateVersion),
      ("emitterVersion", emitterVersion), ("wrapperVersion", wrapperVersion)] do
    unless (← provenance.getObjValAs? String name) = expected do throw (name ++ " changed")
  let origin ← provenance.getObjVal? "origin"
  let emitted ← (emit admitted.plan).mapError reprStr
  let sources ← json.getObjVal? "sources"
  unless (← sources.getObjValAs? String "parent") = emitted.parentSource &&
      (← sources.getObjValAs? String "child") = emitted.childSource &&
      sources == Json.mkObj [("parent", toJson emitted.parentSource), ("child", toJson emitted.childSource)] do
    throw "saved sources differ from call-return plan emission"
  unless (← json.getObjVal? "contracts") == contractsJson do throw "saved contract metadata differs from call-return wrappers"
  unless (← provenance.getObjVal? "features") == toJson admitted.plan.step.features do throw "saved features differ from checked step"
  let kind ← origin.getObjValAs? String "kind"
  if kind = "call-return-generated" then
    let seedText ← origin.getObjValAs? String "seed"
    unless seedText.length ≤ 20 do throw "invalid saved seed"
    let some seed := seedText.toNat? | throw "invalid saved seed"
    unless seed < 2 ^ 64 && toString seed = seedText do throw "noncanonical saved seed"
    unless mask == revision.caseMask (Seed.ofNat seed) do throw "saved swarm mask differs from its generation seed"
    let (expected, expectedOrigin) ← generatedScenario (Seed.ofNat seed) (← origin.getObjValAs? Nat "maxProgramNodes") revision
      (← Stateful.Sequence.savedCount origin)
    let validationFuel ← origin.getObjValAs? Nat "validationFuel"
    unless validationFuel ≤ 10000000 do throw "saved validation fuel exceeds limit"
    unless origin == expectedOrigin.setObjVal! "validationFuel" (toJson validationFuel) do
      throw "saved origin differs from generated call-return provenance"
    unless planJson expected.plan == planJson admitted.plan &&
        sequenceJson expected.transactions == sequenceJson admitted.transactions do
      throw "saved plan or transaction sequence differs from its generation seed"
    validateGenerated expected validationFuel
  else if kind = "imported" then
    unless origin == Json.mkObj [("kind", toJson "imported")] do throw "noncanonical imported origin"
  else if kind = "reduced" then
    let parentPlan ← checkedPlan (← origin.getObjVal? "parentPlan")
    let parentTransactions ← decodeSequence (← origin.getObjVal? "parentTransactions")
    let parent ← checkedScenario parentPlan parentTransactions
    unless (← origin.getObjVal? "parentPrograms") == programsJson parent.plan do
      throw "reduction parent programs differ from their plan"
    unless (sealReduction parent admitted.plan.step admitted.plan.returned admitted.transactions).isSome do
      throw "reduction does not preserve bindings/IDs or decrease the complete scenario"
    unless origin == reducedOrigin parent do throw "noncanonical reduced origin"
  else throw "unsupported call-return case origin"
  makeCase admitted emitted origin fuel revision mask

def shrinkCases (json : Json) (limit fuel : Nat) : Except String Json := do
  let _ ← replayCase json fuel
  let source ← caseProgram json
  -- Reductions inherit the parent case's recorded G0 revision and swarm mask.
  let provenance ← json.getObjVal? "provenance"
  let revision := savedRevision provenance
  let mask ← savedMask provenance revision
  let cases ← ((reductions source).take limit).mapM fun reduced =>
    emitCase reduced.candidate (reducedOrigin source) fuel revision mask
  return Json.mkObj [("schema", toJson corpusSchema), ("cases", toJson cases)]

end Solcore.Synthesis.Source.CallReturn
end

section
-- leanmerge: from Solcore.Synthesis.Stateful.CallSequenceExecution
/-! Execute the original checked call-sequence contracts over an account world.
The parent is installed as its call phase and the child as its contract; each
transaction runs through the public call chain, which runs the call phase, each
child and each resume phase through the public top-level runner and commits as
one transaction. Only the chain's committed world becomes the next
transaction's world. Observations report each transaction's whole return data,
the parent's slots 0 to `5n + 2` for `n` calls, the child's slots 0 and 1, both
balances and both contracts' whole committed storage; no transaction commits a
log.

`model` is a second account of the same sources, written over the bytes instead
of in Core: the child's data cut to its class byte's length, and the EVM's
return-data buffer as the parent's reads see it, with the step evaluated alone
in Core. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Stateful.CallSequenceExecution
open Lean Solcore.Core Solcore.ContractRuntime
open Solcore.Synthesis.Core
open Solcore.Synthesis.Core.CallSequence (CheckedPlan Window)

def historySchema : String := "solcore-lean.call-sequence-history.v1"

abbrev Bindings := NestedCallExecution.Bindings
abbrev Transaction := StorageExecution.Transaction

def inputData (bindings : Bindings) (input : Word) : HostStorageDriver.InputData :=
  NestedCallExecution.inputData bindings input

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

def parentSlots (plan : CheckedPlan) : List Word :=
  (List.range (CallSequence.parentSlotCount plan.calls)).map Word.ofNatModulo

def childSlots : List Word := (List.range CallSequence.childSlotCount).map Word.ofNatModulo

private def slotsJson (account : Account) (slots : List Word) : Json := toJson (slots.map fun slot => Json.mkObj [
  ("slot", toJson (toString slot.val)), ("value", toJson (toString (account.storageRead slot).val))])

private def accountJson (world : WorldState) (role : String) (address : Address) (slots : List Word) : Json :=
  match world.account? address with
  | none => Json.null
  | some account => Json.mkObj [
      ("role", toJson role), ("address", toJson (toString address.val)),
      ("balance", toJson (toString account.balance.val)), ("storage", slotsJson account slots)]

def accountsJson (plan : CheckedPlan) (world : WorldState) (bindings : Bindings) : Json := toJson [
  accountJson world "parent" bindings.parent (parentSlots plan), accountJson world "child" bindings.child childSlots]

private def outcomeFields : FrameOutcome Word → List (String × Json)
  | .returned bytes => [("status", toJson "returned"), ("output", toJson (encodeBytesText bytes))]
  | .reverted bytes => [("status", toJson "reverted"), ("output", toJson (encodeBytesText bytes))]
  | .trapped reason => [("status", toJson "trapped"), ("reason", toJson (toString reason.val))]

private def stoppedRow (plan : CheckedPlan) (common : List (String × Json)) (status : String) (world : WorldState)
    (bindings : Bindings) : Json :=
  Json.mkObj (common ++ [("status", toJson status), ("committedAccounts", accountsJson plan world bindings),
    ("accountStorage", CallReturnExecution.wholeStorageJson world bindings), ("logs", Json.null)])

/-- Each transaction runs through the chain against the current committed
world; local heaps start fresh and only the committed world persists. -/
def observe (plan : CheckedPlan) (transactions : List Transaction) (bindings : Bindings) (fuel : Nat) : Json := Id.run do
  let mut world := initialWorld plan bindings
  let initial := accountsJson plan world bindings
  let initialWhole := CallReturnExecution.wholeStorageJson world bindings
  let mut rows : Array Json := #[]
  let mut stopped : Option String := none
  for (transaction, index) in transactions.zipIdx do
    if stopped.isNone then
      let common := [("id", toJson transaction.id), ("index", toJson index)]
      match CallChainExecution.run (registry plan bindings) plan.parent world bindings.parent bindings.caller
          (inputData bindings transaction.input) fuel with
      | .completed outcome finalWorld _ =>
          world := finalWorld
          rows := rows.push (Json.mkObj (common ++ outcomeFields outcome ++ [
            ("committedAccounts", accountsJson plan world bindings),
            ("accountStorage", CallReturnExecution.wholeStorageJson world bindings),
            ("logs", toJson ([] : List Json))]))
          match outcome with
          | .trapped _ => stopped := some transaction.id
          | _ => pure ()
      | .outOfFuel _ =>
          rows := rows.push (stoppedRow plan common "out-of-fuel" world bindings)
          stopped := some transaction.id
      | .unresolved _ =>
          rows := rows.push (stoppedRow plan common "resolution-failure" world bindings)
          stopped := some transaction.id
      | .inputLimit _ =>
          rows := rows.push (stoppedRow plan common "input-limit" world bindings)
          stopped := some transaction.id
  return Json.mkObj [("schema", toJson historySchema), ("bindings", NestedCallExecution.bindingsJson bindings),
    ("fuelPerTransaction", toJson fuel), ("initialAccounts", initial), ("initialAccountStorage", initialWhole),
    ("transactions", .arr rows), ("finalAccounts", accountsJson plan world bindings),
    ("finalAccountStorage", CallReturnExecution.wholeStorageJson world bindings),
    ("status", toJson (if stopped.isNone then "complete" else "incomplete")),
    ("stoppedAt", stopped.map toJson |>.getD Json.null),
    ("unexecuted", toJson ((transactions.drop rows.size).map (·.id)))]

/-! ### The byte-level model -/

/-- A call's class byte: bit 0 reverts and the rest halves to the length. -/
def classOf (x : Word) : Nat := x.val % 256

def revertsOf (x : Word) : Bool := classOf x % 2 == 1

def lengthOf (x : Word) : Nat := min (classOf x / 2) CallSequence.capacity

/-- The argument of call `k`, from zero: `mix·256` plus the input's byte `k`. -/
def argumentOf (mix input : Word) (call : Nat) : Word :=
  mix * Word.ofNatModulo 256 + Word.ofNatModulo (input.val / 2 ^ (8 * call) % 256)

/-- The first `length` bytes of `d0 ‖ d1 ‖ d2`. -/
def childData (r c x : Word) (length : Nat) : ByteArray :=
  let multiplier := Word.ofNatModulo CallSequence.multiplier
  let d0 := r * multiplier
  let d1 := Word.ofNatModulo ((c * multiplier).val ^^^ x.val)
  let d2 := Word.ofNatModulo (d0.val ^^^ d1.val)
  (encodeWordBytesBE d0 ++ encodeWordBytesBE d1 ++ encodeWordBytesBE d2).extract 0 length

private def bigEndian (bytes : List UInt8) : Nat := bytes.foldl (fun total byte => total * 256 + byte.toNat) 0

/-- The data's first Word when they have one, otherwise zero. -/
def firstWord (data : ByteArray) : Word :=
  if data.size ≥ 32 then Word.ofNatModulo (bigEndian (data.extract 0 32).data.toList) else Word.zero

/-- The window's bytes left-aligned in a zero Word when they lie inside the
data, otherwise zero: what `returndatacopy` into a zeroed Word leaves. -/
def windowWord (data : ByteArray) (window : Window) : Word :=
  if window.offset + window.width ≤ data.size then
    Word.ofNatModulo (bigEndian (data.extract window.offset (window.offset + window.width)).data.toList *
      2 ^ (8 * (32 - window.width)))
  else Word.zero

/-- One call's prescribed outcome: whether it returned, and its data's length. -/
structure CallRow where
  returned : Bool
  length : Nat
  deriving BEq, Repr

/-- One modelled transaction: whether it reverts, its 32 output bytes, its calls'
prescribed outcomes, and the parent's and child's committed slots. -/
structure ModelRow where
  reverted : Bool
  output : ByteArray
  calls : List CallRow
  parent : List Word
  child : List Word

/-- The rows the sources prescribe: the pre-call writes; per call the child's
step, writes and data, the reads before and after the call, the window and the
next argument; the re-read and the sum; and bit 24's revert, which keeps every
prior slot. -/
def model (plan : CheckedPlan) (fuel : Nat) (transactions : List Transaction) : Option (List ModelRow) := Id.run do
  let count := plan.calls
  let mut parent : List Word := List.replicate (CallSequence.parentSlotCount count) Word.zero
  let mut child : List Word := List.replicate CallSequence.childSlotCount Word.zero
  let mut rows : Array ModelRow := #[]
  for transaction in transactions do
    let input := transaction.input
    let accumulator := parent.getD 0 Word.zero + input
    let mut written := (parent.set 0 accumulator).set 1 Word.zero
    let mut state := child
    let mut total := accumulator
    let mut mix := Word.ofNatModulo (input.val / 2 ^ 32)
    let mut previous := Word.zero
    let mut copy : Option Word := none
    let mut calls : Array CallRow := #[]
    for (spot, index) in plan.windows.zipIdx do
      let x := argumentOf mix input index
      let o := state.getD 0 Word.zero
      let c := state.getD 1 Word.zero + Word.ofNatModulo 1
      let some r := CallReturnExecution.stepResult plan.step fuel (x + o) | return none
      let returned := !revertsOf x
      let data := childData r c x (lengthOf x)
      if returned then state := [r, c]
      let ok := if returned then Word.ofNatModulo 1 else Word.zero
      let m := Word.ofNatModulo data.size
      let first := firstWord data
      let copied := windowWord data spot
      if index == 0 && data.size ≥ 32 then copy := some first
      let slot := 5 * index + 2
      written := ((((written.set slot (ok + Word.ofNatModulo 2 * m)).set (slot + 1) first).set (slot + 2) previous).set
        (slot + 3) m).set (slot + 4) copied
      total := total + ok + Word.ofNatModulo 2 * m + first + previous + m + copied
      previous := m
      mix := mix + first + m + copied
      calls := calls.push ⟨returned, data.size⟩
    let again := (copy.map fun first => Word.ofNatModulo (count - 1) * first).getD Word.zero
    written := written.set (5 * count + 2) again
    total := total + again
    if input.val / 2 ^ 24 % 2 == 1 then
      rows := rows.push ⟨true, encodeWordBytesBE total, calls.toList, parent, child⟩
    else
      parent := written
      child := state
      rows := rows.push ⟨false, encodeWordBytesBE total, calls.toList, parent, child⟩
  return some rows.toList

end Solcore.Synthesis.Stateful.CallSequenceExecution
end

section
-- leanmerge: from Solcore.Synthesis.Source.CallSequenceCases
/-! A call-sequence case retains the original checked Core contracts, the
plan's calls and windows, and a role-based transaction sequence. Every replay
reconstructs the contracts from the plan. Each transaction records its calls'
prescribed outcomes and the parent's revert, computed by the byte-level model;
saved outcomes are never an oracle, and the call chain selects the committed
worlds. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.CallSequence
open Lean Solcore.Core Solcore.Synthesis.Core
open Solcore.Synthesis.Core.CallSequence (CheckedPlan Window)
open Solcore.Synthesis.Stateful.CallSequenceExecution (Transaction Bindings CallRow)
open Solcore.ContractRuntime (encodeBytesText)

def caseSchema : String := "solcore-lean.semantic-call-sequence-case.v1"
def planSchema : String := "solcore-lean.call-sequence-plan.v1"
def profileVersion : String := "stateful-call-sequences-v1/call-sequence-seed-v1"
def templateVersion : String := "std-raw-call-measure-latest-data-step-revert-odd-class-v1"
def corpusSchema : String := "solcore-lean.semantic-call-sequence-corpus.v1"

abbrev boundaryInputs := NestedCall.boundaryInputs
abbrev validTransactions := Storage.validTransactions

/-- The window offsets and widths, and the data lengths, drawn half of the time. -/
def offsetBank : List Nat := [0, 1, 31, 32, 33, 63, 64, 95, 96]
def widthBank : List Nat := [0, 1, 31, 32]
def lengthBank : List Nat := [0, 1, 31, 32, 33, 63, 64, 65, 95, 96]

/-- Random steps and the child's shell stay within the largest step budget. -/
def maxStepNodes : Nat := 512

private def w (value : Nat) : Word := Word.ofNatModulo value

/-- The child's shell and its step, which a node budget bounds. -/
def budgetNodes (plan : CheckedPlan) : Nat :=
  CallSequence.childShellNodes + Wire.programNodes plan.step.program

/-- Every contract: the child, the call phase, the middle phases and the last. -/
def programs (plan : CheckedPlan) : List Wire.Program :=
  plan.childProgram :: plan.callProgram :: plan.middlePrograms ++ [plan.lastProgram]

structure CheckedScenario where private mk ::
  plan : CheckedPlan
  transactions : List Transaction
  valid : validTransactions transactions
  bounded : (programs plan).all (Wire.programNodes · ≤ CallSequence.maxContractNodes) = true

def checkedScenario (plan : CheckedPlan) (transactions : List Transaction) : Except String CheckedScenario := do
  if valid : validTransactions transactions then
    if bounded : (programs plan).all (Wire.programNodes · ≤ CallSequence.maxContractNodes) = true then
      return ⟨plan, transactions, valid, bounded⟩
    else throw "call-sequence contracts exceed the 1024-node contract limit"
  else throw s!"call-sequence scenario requires 1..{Stateful.Sequence.maxTransactions} transactions with distinct valid IDs"

/-! ### Plans -/

def windowJson (window : Window) : Json :=
  Json.mkObj [("offset", toJson window.offset), ("width", toJson window.width)]

def planJson (plan : CheckedPlan) : Json := Json.mkObj [
  ("schema", toJson planSchema), ("calls", toJson plan.calls),
  ("windows", toJson (plan.windows.map windowJson)), ("stepProgram", Wire.encodeProgram plan.step.program)]

def checkedPlan (json : Json) : Except String CheckedPlan := do
  unless (← json.getObjValAs? String "schema") = planSchema do throw "unsupported call-sequence plan schema"
  let rows ← (← json.getObjVal? "windows").getArr?
  let windows ← rows.toList.mapM fun row => do
    return ({offset := ← row.getObjValAs? Nat "offset", width := ← row.getObjValAs? Nat "width"} : Window)
  unless (← json.getObjValAs? Nat "calls") = windows.length do throw "a plan has one window per call"
  let step ← Aggregate.checkedFunction (← json.getObjVal? "stepProgram")
  let some plan := CheckedPlan.ofParts? step windows
    | throw "call-sequence plan needs two or three calls, windows inside the bounds, and full host-Core admission"
  unless json == planJson plan do throw "call-sequence plan differs from its canonical checked representation"
  return plan

/-! ### Transactions and their prescribed outcomes -/

/-- Each transaction's calls and whether the parent reverts, from the model. -/
def prescribed (plan : CheckedPlan) (fuel : Nat) (transactions : List Transaction) :
    Except String (List (List CallRow × Bool)) := do
  let some rows := Stateful.CallSequenceExecution.model plan fuel transactions
    | throw "call-sequence model exhausted Core fuel"
  return rows.map fun row => (row.calls, row.reverted)

def callRowJson (row : CallRow) : Json := Json.mkObj [
  ("status", toJson (if row.returned then "returned" else "reverted")), ("length", toJson row.length)]

def transactionJson (tx : Transaction) (calls : List CallRow) (reverts : Bool) : Json := Json.mkObj [
  ("id", toJson tx.id), ("input", toJson (toString tx.input.val)),
  ("value", toJson "0"), ("target", toJson "parent"), ("callee", toJson "child"),
  ("calls", toJson (calls.map callRowJson)), ("parentReverts", toJson reverts)]

def transactionsJson (plan : CheckedPlan) (fuel : Nat) (transactions : List Transaction) : Except String Json := do
  let outcomes ← prescribed plan fuel transactions
  return toJson ((transactions.zip outcomes).map fun (tx, (calls, reverts)) => transactionJson tx calls reverts)

def decodeTransactions (plan : CheckedPlan) (fuel : Nat) (json : Json) : Except String (List Transaction) := do
  let transactions ← CallReturn.decodeSequence json
  unless json == (← transactionsJson plan fuel transactions) do
    throw "transactions differ from their canonical ID, input, role metadata or prescribed outcomes"
  return transactions

/-! ### Cases -/

def programsJson (plan : CheckedPlan) : Json := Json.mkObj [
  ("parentCall", Wire.encodeProgram plan.callProgram),
  ("parentMiddles", toJson (plan.middlePrograms.map Wire.encodeProgram)),
  ("parentLast", Wire.encodeProgram plan.lastProgram),
  ("child", Wire.encodeProgram plan.childProgram)]

def observedSlotsJson (plan : CheckedPlan) : Json := Json.mkObj [
  ("parent", toJson ((Stateful.CallSequenceExecution.parentSlots plan).map fun slot => toString slot.val)),
  ("child", toJson (Stateful.CallSequenceExecution.childSlots.map fun slot => toString slot.val))]

def makeCase (scenario : CheckedScenario) (emitted : CallReturn.EmittedContracts) (origin : Json) (fuel : Nat)
    (revision : GeneratorRevision := .v1) (mask : FeatureMask := FeatureMask.all) : Except String Json := do
  return Json.mkObj [
    ("schema", toJson caseSchema), ("callSequencePlan", planJson scenario.plan),
    ("programs", programsJson scenario.plan),
    ("sources", Json.mkObj [("parent", toJson emitted.parentSource), ("child", toJson emitted.childSource)]),
    ("transactions", ← transactionsJson scenario.plan fuel scenario.transactions),
    ("initialState", CallReturn.initialStateJson), ("observedSlots", observedSlotsJson scenario.plan),
    ("provenance", Json.mkObj <| swarmField revision mask ++ [
      ("origin", origin), ("profileVersion", toJson profileVersion),
      ("functionVersion", toJson CallSequence.childVersion), ("parentVersion", toJson CallSequence.parentVersion),
      ("templateVersion", toJson templateVersion),
      ("stepProfileVersion", toJson Aggregate.profileVersion),
      ("stepFunctionVersion", toJson Aggregates.version),
      ("stepTemplateVersion", toJson Aggregate.templateVersion),
      ("generatorVersion", toJson revision.version),
      ("emitterVersion", toJson emitterVersion), ("wrapperVersion", toJson wrapperVersion),
      ("features", toJson scenario.plan.step.features)]),
    ("contracts", CallReturn.contractsJson), ("executionFuel", toJson fuel)]

def emitCase (scenario : CheckedScenario) (origin : Json) (fuel : Nat)
    (revision : GeneratorRevision := .v1) (mask : FeatureMask := FeatureMask.all) : Except String Json := do
  unless fuel ≤ 10000000 do throw "execution fuel exceeds limit"
  let emitted ← (emit scenario.plan).mapError reprStr
  makeCase scenario emitted origin fuel revision mask

private def decodeProgram (json : Json) : Except String Wire.Program :=
  (Wire.decodeProgramWithBudget {maxDepth := 512, maxNodes := CallSequence.maxContractNodes, maxIntegerBytes := 4096}
    json).mapError (fun
    | .protocol error => error.toJson.compress
    | .exhausted exhaustion => "Core decode budget exceeded: " ++ reprStr exhaustion)

private def sameProgram (json : Json) (expected : Wire.Program) : Except String Unit := do
  let program ← decodeProgram json
  unless Wire.encodeProgram program == Wire.encodeProgram expected do
    throw "saved original Core program differs from its canonical call-sequence plan"

/-- Every origin must reconstruct the fixed host contracts, including imports
and reductions. Arbitrary well-typed programs are not admissible
replacements. -/
def caseProgram (json : Json) : Except String CheckedScenario := do
  unless (← json.getObjValAs? String "schema") = caseSchema do throw "unsupported semantic call-sequence case schema"
  let plan ← checkedPlan (← json.getObjVal? "callSequencePlan")
  let fuel ← json.getObjValAs? Nat "executionFuel"
  unless fuel ≤ 10000000 do throw "saved execution fuel exceeds limit"
  let transactions ← decodeTransactions plan fuel (← json.getObjVal? "transactions")
  let originals ← json.getObjVal? "programs"
  sameProgram (← originals.getObjVal? "parentCall") plan.callProgram
  let middles ← (← originals.getObjVal? "parentMiddles").getArr?
  unless middles.size = plan.middlePrograms.length do throw "saved middle phases differ from the plan's calls"
  for (saved, expected) in middles.toList.zip plan.middlePrograms do
    sameProgram saved expected
  sameProgram (← originals.getObjVal? "parentLast") plan.lastProgram
  sameProgram (← originals.getObjVal? "child") plan.childProgram
  unless originals == programsJson plan do throw "saved program roles are not canonical"
  unless (← json.getObjVal? "initialState") == CallReturn.initialStateJson do
    throw "initial accounts must be empty and unfunded"
  unless (← json.getObjVal? "observedSlots") == observedSlotsJson plan do
    throw "observed slots must be the parent's 0 to 5n + 2 and the child's 0 and 1"
  checkedScenario plan transactions

def observe (scenario : CheckedScenario) (bindings : Bindings) (fuel : Nat) : Json :=
  Stateful.CallSequenceExecution.observe scenario.plan scenario.transactions bindings fuel

/-! ### Generation -/

/-- SplitMix64's finalizer. The generator's draws are affine in its start, so
consecutive seeds would otherwise start streams whose draws step by a fixed
residue. -/
private def mixed (value : Nat) : Nat :=
  let z := value % 2 ^ 64
  let z := (z ^^^ (z >>> 30)) * 0xbf58476d1ce4e5b9 % 2 ^ 64
  let z := (z ^^^ (z >>> 27)) * 0x94d049bb133111eb % 2 ^ 64
  z ^^^ (z >>> 31)

/-- High halves of successive draws from the stream that starts at the mixed
`seed` xor `domain`, each below its bound. -/
private def boundedDraws (seed : Seed) (domain : Nat) (bounds : List Nat) : List Nat := Id.run do
  let mut state := Seed.ofNat (mixed (seed.toNat ^^^ domain))
  let mut values : Array Nat := #[]
  for bound in bounds do
    let (value, next) := state.draw
    values := values.push (value.toNat / 2 ^ 32 % bound)
    state := next
  return values.toList

/-- The call count, then per window an offset selector and a uniform offset, a
width selector and a uniform width. -/
def planBounds : List Nat := [2] ++ (List.replicate 3 [18, 97, 8, 33]).flatten

def planChoices (seed : Seed) : List Nat := boundedDraws seed 0x7365712d706c616e planBounds

/-- The bank entry when the selector names one, otherwise the uniform draw. -/
private def banked (bank : List Nat) (selector uniform : Nat) : Nat :=
  if selector < bank.length then bank.getD selector 0 else uniform

def generatedWindows (seed : Seed) : List Window :=
  let choices := planChoices seed
  (List.range (2 + choices.getD 0 0)).map fun index =>
    let at_ := fun position => choices.getD (1 + 4 * index + position) 0
    ⟨banked offsetBank (at_ 0) (at_ 1), banked widthBank (at_ 2) (at_ 3)⟩

/-- Per transaction: per call the revert draw, a length selector and a uniform
length; the parent's revert draw; and seven 32-bit parts of `input >> 32`. -/
def transactionBounds : List Nat := (List.replicate 3 [3, 20, 97]).flatten ++ [4] ++ List.replicate 7 (2 ^ 32)

def sequenceBounds : List Nat := (List.replicate 3 transactionBounds).flatten

def sequenceChoices (seed : Seed) : List Nat := boundedDraws seed 0x7365712d74786e73 sequenceBounds

/-- An input from its draws: each used call's class byte `2L + revert`, the
parent's revert at bit 24 and the high part from bit 32. -/
def inputOf (calls : Nat) (draws : List Nat) : Word :=
  let classes := (List.range calls).map fun call =>
    let at_ := fun position => draws.getD (3 * call + position) 0
    2 * banked lengthBank (at_ 1) (at_ 2) + (if at_ 0 == 0 then 1 else 0)
  let low := classes.zipIdx.foldl (fun total (value, call) => total + value * 2 ^ (8 * call)) 0
  let reverts := if draws.getD 9 0 == 0 then 2 ^ 24 else 0
  let high := (List.range 7).foldl (fun total part => total * 2 ^ 32 + draws.getD (10 + part) 0) 0
  w (high * 2 ^ 32 + reverts + low)

def blockTransactions (calls : Nat) (seed : Seed) (first : Nat) : List Transaction :=
  let choices := sequenceChoices seed
  (List.range 3).map fun index =>
    ⟨"tx-" ++ toString (first + index), inputOf calls (choices.drop (transactionBounds.length * index))⟩

/-- The first `count` transactions of the seed's consecutive blocks. -/
def generatedTransactions (calls : Nat) (seed : Seed) (count : Nat := 3) : List Transaction :=
  Stateful.Sequence.blocks (blockTransactions calls) seed count

/-- The child's shell lies inside the budget with the step, which the complete
measure bounds again. -/
def generatedScenario (seed : Seed) (nodes : Nat) (revision : GeneratorRevision := .v1)
    (transactions : Nat := 3) : Except String (CheckedScenario × Json) := do
  Stateful.Sequence.checkCount transactions
  let windows := generatedWindows seed
  let shell := CallSequence.childShellNodes
  unless nodes ≤ maxStepNodes && shell < nodes do
    throw "node budget is too small for the call-sequence child or exceeds 512"
  let (step, stepOrigin) ← Aggregate.generatedFunction seed (nodes - shell) revision
  let some plan := CheckedPlan.ofParts? step windows | throw "generated call-sequence plan failed full Core admission"
  let scenario ← checkedScenario plan (generatedTransactions windows.length seed transactions)
  unless budgetNodes scenario.plan ≤ nodes do throw "call-sequence child exceeds its requested node budget"
  return (scenario, Stateful.Sequence.recordCount (Json.mkObj [
    ("kind", toJson "call-sequence-generated"), ("seed", toJson (toString seed.toNat)),
    ("finalSeed", ← stepOrigin.getObjVal? "finalSeed"), ("maxProgramNodes", toJson nodes),
    ("stepOrigin", stepOrigin), ("planChoices", toJson (planChoices seed)),
    ("sequenceChoices", toJson (Stateful.Sequence.blockChoices sequenceChoices seed transactions))]) transactions)

private def rowStatus (row : Json) : Option String := (row.getObjValAs? String "status").toOption

/-- The history must complete with the model's outcomes. -/
def validateGenerated (scenario : CheckedScenario) (fuel : Nat) : Except String Unit := do
  Aggregate.inputSensitive scenario.plan.step fuel
  let observed := observe scenario Solcore.Synthesis.Stateful.NestedCallExecution.fixtureBindings fuel
  let rows ← observed.getObjValAs? (List Json) "transactions"
  unless (← observed.getObjValAs? String "status") = "complete" do
    if rows.any (fun row => rowStatus row == some "out-of-fuel") then throw "call-sequence history exhausted Core fuel"
    else throw "call-sequence history stopped without a permitted root completion"
  let some expected := Stateful.CallSequenceExecution.model scenario.plan fuel scenario.transactions
    | throw "call-sequence history exhausted Core fuel"
  unless rows.map rowStatus == expected.map (fun row => some (if row.reverted then "reverted" else "returned")) do
    throw "call-sequence history did not follow its prescribed outcomes"

def generateCases (firstSeed : Seed) (nodes count attempts fuel : Nat)
    (revision : GeneratorRevision := .v1) (transactions : Nat := 3) : Json := Id.run do
  let mut cases : Array Json := #[]
  let mut excluded : Array Json := #[]
  let mut attempted := 0
  for index in List.range attempts do
    if cases.size < count then
      attempted := attempted + 1
      let seed := Seed.ofNat (firstSeed.toNat + index)
      let result := do
        unless fuel ≤ 10000000 do throw "execution fuel exceeds limit"
        let (scenario, origin) ← generatedScenario seed nodes revision transactions
        let emitted ← (emit scenario.plan).mapError reprStr
        validateGenerated scenario fuel
        makeCase scenario emitted (origin.setObjVal! "validationFuel" (toJson fuel)) fuel revision (revision.caseMask seed)
      match result with
      | .error error =>
          let resource := error == "boundary observation exhausted Core fuel" ||
            error == "call-sequence history exhausted Core fuel" || error == "call-sequence model exhausted Core fuel"
          excluded := excluded.push (Json.mkObj [
            ("seed", toJson (toString seed.toNat)), ("stage", toJson "call-sequence-profile"),
            ("reason", toJson error),
            ("code", toJson (if resource then "validation-out-of-fuel" else "profile-excluded")),
            ("category", toJson (if resource then "inconclusive-resource" else "excluded"))])
      | .ok case => cases := cases.push case
  return Json.mkObj [("schema", toJson corpusSchema),
    ("requested", toJson count), ("attempted", toJson attempted),
    ("status", toJson (if cases.size = count then "complete" else "generation-exhausted")),
    ("excluded", .arr excluded), ("cases", .arr cases)]

/-! ### Reductions -/

/-- The windows' offsets and widths. -/
def windowWeight (plan : CheckedPlan) : Nat :=
  plan.windows.foldl (fun total window => total + window.offset + window.width) 0

def inputWeight (scenario : CheckedScenario) : Nat :=
  scenario.transactions.foldl (fun total transaction => total + transaction.input.val) 0

def scenarioComplexity (scenario : CheckedScenario) : Complexity := complexity scenario.plan.childProgram.body

/-- Transaction count, call count, the windows, the child's size and literals,
then the inputs. Every axis is a natural number and the comparison is strictly
lexicographic. -/
def StrictlySmaller (candidate source : CheckedScenario) : Prop :=
  candidate.transactions.length < source.transactions.length ∨
  (candidate.transactions.length = source.transactions.length ∧
    (candidate.plan.calls < source.plan.calls ∨
    (candidate.plan.calls = source.plan.calls ∧
      (windowWeight candidate.plan < windowWeight source.plan ∨
      (windowWeight candidate.plan = windowWeight source.plan ∧
        ((scenarioComplexity candidate).StrictlySmaller (scenarioComplexity source) ∨
        (scenarioComplexity candidate = scenarioComplexity source ∧
          inputWeight candidate < inputWeight source)))))))

instance (candidate source : CheckedScenario) : Decidable (StrictlySmaller candidate source) := by
  unfold StrictlySmaller
  infer_instance

structure Reduction (source : CheckedScenario) where private mk ::
  candidate : CheckedScenario
  sameHelperCount : candidate.plan.step.helpers.length = source.plan.step.helpers.length
  sameBindings : Aggregate.bindingInventory candidate.plan.step = Aggregate.bindingInventory source.plan.step
  stableIds : (candidate.transactions.map (·.id)).Sublist (source.transactions.map (·.id))
  strict : StrictlySmaller candidate source

private def sealReduction (source : CheckedScenario) (step : Aggregates.CheckedDAG) (windows : List Window)
    (transactions : List Transaction) : Option (Reduction source) := do
  let plan ← CheckedPlan.ofParts? step windows
  let candidate ← (checkedScenario plan transactions).toOption
  if count : candidate.plan.step.helpers.length = source.plan.step.helpers.length then
    if bindings : Aggregate.bindingInventory candidate.plan.step = Aggregate.bindingInventory source.plan.step then
      if ids : (candidate.transactions.map (·.id)).Sublist (source.transactions.map (·.id)) then
        if strict : StrictlySmaller candidate source then some ⟨candidate, count, bindings, ids, strict⟩
        else none
      else none
    else none
  else none

/-- The earlier entries of a bank before `value`, or the whole bank when it is
not in it, below `value`. -/
private def earlier (bank : List Nat) (value : Nat) : List Nat :=
  (bank.take ((bank.idxOf? value).getD bank.length)).filter (· < value)

/-- An input's smaller variants: the parent's revert cleared, the high part
cleared, and per class byte, the unused third one of a two-call plan too, its
revert cleared and its length an earlier bank entry, then zero. -/
def smallerInputs (input : Word) : List Word :=
  let value := input.val
  let byte := fun call => value / 2 ^ (8 * call) % 256
  let replace := fun call (next : Nat) => w (value - byte call * 2 ^ (8 * call) + next * 2 ^ (8 * call))
  let revert := if value / 2 ^ 24 % 2 == 1 then [w (value - 2 ^ 24)] else []
  let high := if value ≥ 2 ^ 32 then [w (value % 2 ^ 32)] else []
  let classes := (List.range 3).flatMap fun call =>
    let class_ := byte call
    let length := min (class_ / 2) CallSequence.capacity
    (if class_ % 2 == 1 then [replace call (class_ - 1)] else []) ++
      ((earlier lengthBank length ++ (if length > 0 then [0] else [])).eraseDups.map fun shorter =>
        replace call (2 * shorter + class_ % 2))
  revert ++ high ++ classes

/-- One-transaction removals, the last call dropped, earlier or narrower
windows, step reductions, then per transaction each smaller input. Candidates
still need execution to establish that they preserve a finding. -/
def reductions (source : CheckedScenario) : List (Reduction source) := Id.run do
  let windows := source.plan.windows
  let mut raw : List (Aggregates.CheckedDAG × List Window × List Transaction) := []
  -- Removing one transaction comes first, from the last back: a long
  -- sequence loses the tail beyond a difference before the candidate limit.
  for index in (List.range source.transactions.length).reverse do
    raw := raw ++ [(source.plan.step, windows,
      (source.transactions.zipIdx.filter (fun (_, current) => current != index)).map Prod.fst)]
  if windows.length > 2 then
    raw := raw ++ [(source.plan.step, windows.dropLast, source.transactions)]
  for (spot, index) in windows.zipIdx do
    for offset in earlier offsetBank spot.offset do
      raw := raw ++ [(source.plan.step, windows.set index {spot with offset}, source.transactions)]
    for width in (earlier widthBank spot.width ++ (if spot.width > 0 then [0] else [])).eraseDups do
      raw := raw ++ [(source.plan.step, windows.set index {spot with width}, source.transactions)]
  for reduced in Aggregate.reductions ⟨source.plan.step, Word.zero⟩ do
    raw := raw ++ [(reduced.candidate.function, windows, source.transactions)]
  for (transaction, index) in source.transactions.zipIdx do
    for input in smallerInputs transaction.input do
      let transactions := source.transactions.set index {transaction with input}
      raw := raw ++ [(source.plan.step, windows, transactions)]
  let mut seen : List String := []
  let mut result := []
  for (step, windows, transactions) in raw do
    if let some reduced := sealReduction source step windows transactions then
      let identity := (Json.mkObj [("plan", planJson reduced.candidate.plan),
        ("transactions", toJson (reduced.candidate.transactions.map fun tx => toString tx.input.val ++ tx.id))]).compress
      if !seen.contains identity then
        seen := identity :: seen
        result := result ++ [reduced]
  return result

private def sequenceJson (transactions : List Transaction) : Json :=
  toJson (transactions.map fun tx => Json.mkObj [("id", toJson tx.id), ("input", toJson (toString tx.input.val))])

private def reducedOrigin (parent : CheckedScenario) : Json := Json.mkObj [
  ("kind", toJson "reduced"), ("parentPlan", planJson parent.plan),
  ("parentPrograms", programsJson parent.plan), ("parentTransactions", sequenceJson parent.transactions)]

def replayCase (json : Json) (fuel : Nat) : Except String Json := do
  unless fuel ≤ 10000000 do throw "execution fuel exceeds limit"
  let admitted ← caseProgram json
  let provenance ← json.getObjVal? "provenance"
  let revision := savedRevision provenance
  let mask ← savedMask provenance revision
  for (name, expected) in [
      ("generatorVersion", revision.version), ("profileVersion", profileVersion),
      ("functionVersion", CallSequence.childVersion), ("parentVersion", CallSequence.parentVersion),
      ("templateVersion", templateVersion),
      ("stepProfileVersion", Aggregate.profileVersion), ("stepFunctionVersion", Aggregates.version),
      ("stepTemplateVersion", Aggregate.templateVersion),
      ("emitterVersion", emitterVersion), ("wrapperVersion", wrapperVersion)] do
    unless (← provenance.getObjValAs? String name) = expected do throw (name ++ " changed")
  let origin ← provenance.getObjVal? "origin"
  let emitted ← (emit admitted.plan).mapError reprStr
  let sources ← json.getObjVal? "sources"
  unless (← sources.getObjValAs? String "parent") = emitted.parentSource &&
      (← sources.getObjValAs? String "child") = emitted.childSource &&
      sources == Json.mkObj [("parent", toJson emitted.parentSource), ("child", toJson emitted.childSource)] do
    throw "saved sources differ from call-sequence plan emission"
  unless (← json.getObjVal? "contracts") == CallReturn.contractsJson do
    throw "saved contract metadata differs from call-sequence wrappers"
  unless (← provenance.getObjVal? "features") == toJson admitted.plan.step.features do throw "saved features differ from checked step"
  let kind ← origin.getObjValAs? String "kind"
  if kind = "call-sequence-generated" then
    let seedText ← origin.getObjValAs? String "seed"
    unless seedText.length ≤ 20 do throw "invalid saved seed"
    let some seed := seedText.toNat? | throw "invalid saved seed"
    unless seed < 2 ^ 64 && toString seed = seedText do throw "noncanonical saved seed"
    unless mask == revision.caseMask (Seed.ofNat seed) do throw "saved swarm mask differs from its generation seed"
    let (expected, expectedOrigin) ← generatedScenario (Seed.ofNat seed) (← origin.getObjValAs? Nat "maxProgramNodes") revision
      (← Stateful.Sequence.savedCount origin)
    let validationFuel ← origin.getObjValAs? Nat "validationFuel"
    unless validationFuel ≤ 10000000 do throw "saved validation fuel exceeds limit"
    unless origin == expectedOrigin.setObjVal! "validationFuel" (toJson validationFuel) do
      throw "saved origin differs from generated call-sequence provenance"
    unless planJson expected.plan == planJson admitted.plan &&
        sequenceJson expected.transactions == sequenceJson admitted.transactions do
      throw "saved plan or transaction sequence differs from its generation seed"
    validateGenerated expected validationFuel
  else if kind = "imported" then
    unless origin == Json.mkObj [("kind", toJson "imported")] do throw "noncanonical imported origin"
  else if kind = "reduced" then
    let parentPlan ← checkedPlan (← origin.getObjVal? "parentPlan")
    let parentTransactions ← CallReturn.decodeSequence (← origin.getObjVal? "parentTransactions")
    let parent ← checkedScenario parentPlan parentTransactions
    unless (← origin.getObjVal? "parentPrograms") == programsJson parent.plan do
      throw "reduction parent programs differ from their plan"
    unless (sealReduction parent admitted.plan.step admitted.plan.windows admitted.transactions).isSome do
      throw "reduction does not preserve bindings/IDs or decrease the complete scenario"
    unless origin == reducedOrigin parent do throw "noncanonical reduced origin"
  else throw "unsupported call-sequence case origin"
  makeCase admitted emitted origin fuel revision mask

def shrinkCases (json : Json) (limit fuel : Nat) : Except String Json := do
  let _ ← replayCase json fuel
  let source ← caseProgram json
  -- Reductions inherit the parent case's recorded G0 revision and swarm mask.
  let provenance ← json.getObjVal? "provenance"
  let revision := savedRevision provenance
  let mask ← savedMask provenance revision
  let cases ← ((reductions source).take limit).mapM fun reduced =>
    emitCase reduced.candidate (reducedOrigin source) fuel revision mask
  return Json.mkObj [("schema", toJson corpusSchema), ("cases", toJson cases)]

end Solcore.Synthesis.Source.CallSequence
end

section
-- leanmerge: from Solcore.Synthesis.Stateful.CallBranchExecution
/-! Execute the original checked call-branch contracts over an account world.
The parent is installed as its call phase and the child as its contract; each
transaction runs through the public choice chain, which runs the call phase,
each child and each resume phase through the public top-level runner and
commits as one transaction. Only the chain's committed world becomes the next
transaction's world. Observations report each transaction's whole return data,
the parent's slots 0 to `B + 4P`, the child's slots 0 and 1, both balances and
both contracts' whole committed storage; no transaction commits a log.

`model` is a second account of the same sources, written over the bytes instead
of in Core: the child's data cut to its class byte's length, and the EVM's
return-data buffer as the parent's reads see it through its sites, with the
step evaluated alone in Core. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Stateful.CallBranchExecution
open Lean Solcore.Core Solcore.ContractRuntime
open Solcore.Synthesis.Core
open Solcore.Synthesis.Core.CallBranch (CheckedPlan Site)
open Solcore.Synthesis.Stateful.CallSequenceExecution (revertsOf lengthOf childData firstWord windowWord)

def historySchema : String := "solcore-lean.call-branch-history.v1"

abbrev Bindings := NestedCallExecution.Bindings
abbrev Transaction := StorageExecution.Transaction

def inputData (bindings : Bindings) (input : Word) : HostStorageDriver.InputData :=
  NestedCallExecution.inputData bindings input

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

def parentSlots (plan : CheckedPlan) : List Word :=
  (List.range (CallBranch.parentSlotCount plan.sites)).map Word.ofNatModulo

def childSlots : List Word := (List.range CallBranch.childSlotCount).map Word.ofNatModulo

private def slotsJson (account : Account) (slots : List Word) : Json := toJson (slots.map fun slot => Json.mkObj [
  ("slot", toJson (toString slot.val)), ("value", toJson (toString (account.storageRead slot).val))])

private def accountJson (world : WorldState) (role : String) (address : Address) (slots : List Word) : Json :=
  match world.account? address with
  | none => Json.null
  | some account => Json.mkObj [
      ("role", toJson role), ("address", toJson (toString address.val)),
      ("balance", toJson (toString account.balance.val)), ("storage", slotsJson account slots)]

def accountsJson (plan : CheckedPlan) (world : WorldState) (bindings : Bindings) : Json := toJson [
  accountJson world "parent" bindings.parent (parentSlots plan), accountJson world "child" bindings.child childSlots]

private def outcomeFields : FrameOutcome Word → List (String × Json)
  | .returned bytes => [("status", toJson "returned"), ("output", toJson (encodeBytesText bytes))]
  | .reverted bytes => [("status", toJson "reverted"), ("output", toJson (encodeBytesText bytes))]
  | .trapped reason => [("status", toJson "trapped"), ("reason", toJson (toString reason.val))]

private def stoppedRow (plan : CheckedPlan) (common : List (String × Json)) (status : String) (world : WorldState)
    (bindings : Bindings) : Json :=
  Json.mkObj (common ++ [("status", toJson status), ("committedAccounts", accountsJson plan world bindings),
    ("accountStorage", CallReturnExecution.wholeStorageJson world bindings), ("logs", Json.null)])

/-- Each transaction runs through the choice chain against the current
committed world; local heaps start fresh and only the committed world
persists. -/
def observe (plan : CheckedPlan) (transactions : List Transaction) (bindings : Bindings) (fuel : Nat) : Json := Id.run do
  let mut world := initialWorld plan bindings
  let initial := accountsJson plan world bindings
  let initialWhole := CallReturnExecution.wholeStorageJson world bindings
  let mut rows : Array Json := #[]
  let mut stopped : Option String := none
  for (transaction, index) in transactions.zipIdx do
    if stopped.isNone then
      let common := [("id", toJson transaction.id), ("index", toJson index)]
      match CallChoiceExecution.run (registry plan bindings) plan.parent world bindings.parent bindings.caller
          (inputData bindings transaction.input) fuel with
      | .completed outcome finalWorld _ =>
          world := finalWorld
          rows := rows.push (Json.mkObj (common ++ outcomeFields outcome ++ [
            ("committedAccounts", accountsJson plan world bindings),
            ("accountStorage", CallReturnExecution.wholeStorageJson world bindings),
            ("logs", toJson ([] : List Json))]))
          match outcome with
          | .trapped _ => stopped := some transaction.id
          | _ => pure ()
      | .outOfFuel _ =>
          rows := rows.push (stoppedRow plan common "out-of-fuel" world bindings)
          stopped := some transaction.id
      | .unresolved _ =>
          rows := rows.push (stoppedRow plan common "resolution-failure" world bindings)
          stopped := some transaction.id
      | .inputLimit _ =>
          rows := rows.push (stoppedRow plan common "input-limit" world bindings)
          stopped := some transaction.id
      | .callLimit _ =>
          rows := rows.push (stoppedRow plan common "call-limit" world bindings)
          stopped := some transaction.id
  return Json.mkObj [("schema", toJson historySchema), ("bindings", NestedCallExecution.bindingsJson bindings),
    ("fuelPerTransaction", toJson fuel), ("initialAccounts", initial), ("initialAccountStorage", initialWhole),
    ("transactions", .arr rows), ("finalAccounts", accountsJson plan world bindings),
    ("finalAccountStorage", CallReturnExecution.wholeStorageJson world bindings),
    ("status", toJson (if stopped.isNone then "complete" else "incomplete")),
    ("stoppedAt", stopped.map toJson |>.getD Json.null),
    ("unexecuted", toJson ((transactions.drop rows.size).map (·.id)))]

/-! ### The byte-level model -/

/-- The argument of position `position`: `mix·256` plus the input's byte
`position`. -/
def argumentOf (mix input : Word) (position : Nat) : Word :=
  mix * Word.ofNatModulo 256 + Word.ofNatModulo (input.val / 2 ^ (8 * position) % 256)

/-- Whether bit `bit` of `value` is set. -/
def bitOf (value : Word) (bit : Nat) : Bool := value.val / 2 ^ bit % 2 == 1

/-- A loop's limit: its two control bits' value, at most its bound. -/
def limitOf (input : Word) (index bound : Nat) : Nat := min (input.val / 2 ^ CallBranch.controlBit index % 4) bound

/-- One call's prescribed outcome: its position, whether it returned, and its
data's length. -/
structure CallRow where
  position : Nat
  returned : Bool
  length : Nat
  deriving BEq, Repr

/-- One modelled transaction: whether it reverts, its 32 output bytes, its calls'
prescribed outcomes, and the parent's and child's committed slots. -/
structure ModelRow where
  reverted : Bool
  output : ByteArray
  calls : List CallRow
  parent : List Word
  child : List Word

/-- The state of one transaction's walk through the sites. -/
private structure Walk where
  mix : Word
  child : List Word
  buffer : ByteArray
  written : List Word
  calls : Array CallRow

/-- The call at `position` in `site`: the child's step, writes and data, and the
four reads after the call. -/
private def callAt (plan : CheckedPlan) (fuel : Nat) (input : Word) (site : Site) (position : Nat) (walk : Walk) :
    Option Walk := do
  let x := argumentOf walk.mix input position
  let o := walk.child.getD 0 Word.zero
  let c := walk.child.getD 1 Word.zero + Word.ofNatModulo 1
  let r ← CallReturnExecution.stepResult plan.step fuel (x + o)
  let returned := !revertsOf x
  let data := childData r c x (lengthOf x)
  let ok := if returned then Word.ofNatModulo 1 else Word.zero
  let m := Word.ofNatModulo data.size
  let first := firstWord data
  let copied := windowWord data site.callWindow
  let slot := CallBranch.positionSlot plan.sites position
  let written := (((walk.written.set slot (ok + Word.ofNatModulo 2 * m)).set (slot + 1) first).set (slot + 2) m).set
    (slot + 3) copied
  return ⟨walk.mix + first + m + copied, if returned then [r, c] else walk.child, data, written,
    walk.calls.push ⟨position, returned, data.size⟩⟩

/-- Site `index`: the size before it, a branch's call when its bit is set or a
loop's calls while its counter is below its limit and the latest size differs
from its stop length, then the size and the exit window after it. -/
private def siteAt (plan : CheckedPlan) (fuel : Nat) (input : Word) (index : Nat) (site : Site) (start : Walk) :
    Option Walk := do
  let first := CallBranch.firstPosition plan.sites index
  let entered := start.written.set (CallBranch.siteSlot index) (Word.ofNatModulo start.buffer.size)
  let mut walk := { start with written := entered }
  match site.kind with
  | .branch =>
      if bitOf input (CallBranch.controlBit index) then
        walk ← callAt plan fuel input site first walk
  | .loop =>
      let limit := limitOf input index site.bound
      for counter in List.range site.bound do
        if counter < limit && walk.buffer.size != site.stop then
          walk ← callAt plan fuel input site (first + counter) walk
  let size := Word.ofNatModulo walk.buffer.size
  let copied := windowWord walk.buffer site.exitWindow
  let exited := (walk.written.set (CallBranch.siteSlot index + 1) size).set (CallBranch.siteSlot index + 2) copied
  return { walk with written := exited, mix := walk.mix + size + copied }

/-- The rows the sources prescribe: slot 0's accumulator and `z = 0`; each
site's reads and calls in program order, with the step evaluated alone; the
call count and the sum; and bit 30's revert, which keeps every prior slot. -/
def model (plan : CheckedPlan) (fuel : Nat) (transactions : List Transaction) : Option (List ModelRow) := Id.run do
  let sites := plan.sites
  let count := CallBranch.parentSlotCount sites
  let mut parent : List Word := List.replicate count Word.zero
  let mut child : List Word := List.replicate CallBranch.childSlotCount Word.zero
  let mut rows : Array ModelRow := #[]
  for transaction in transactions do
    let input := transaction.input
    let start := (List.replicate count Word.zero).set 0 (parent.getD 0 Word.zero + input)
    let mut walk : Walk :=
      ⟨Word.ofNatModulo (input.val / 2 ^ 32), child, ByteArray.empty, start, #[]⟩
    for (site, index) in sites.zipIdx do
      let some next := siteAt plan fuel input index site walk | return none
      walk := next
    let written := walk.written.set (CallBranch.countSlot sites) (Word.ofNatModulo walk.calls.size)
    let total := written.foldl (· + ·) Word.zero
    if bitOf input CallBranch.revertBit then
      rows := rows.push ⟨true, encodeWordBytesBE total, walk.calls.toList, parent, child⟩
    else
      parent := written
      child := walk.child
      rows := rows.push ⟨false, encodeWordBytesBE total, walk.calls.toList, parent, child⟩
  return some rows.toList

end Solcore.Synthesis.Stateful.CallBranchExecution
end

section
-- leanmerge: from Solcore.Synthesis.Source.CallBranchCases
/-! A call-branch case retains the original checked Core contracts, the plan's
sites and a role-based transaction sequence. Every replay reconstructs the
contracts from the plan. Each transaction records the calls it makes and the
parent's revert, computed by the byte-level model; saved outcomes are never an
oracle, and the choice chain selects the committed worlds. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.CallBranch
open Lean Solcore.Core Solcore.Synthesis.Core
open Solcore.Synthesis.Core.CallBranch (CheckedPlan Site Kind)
open Solcore.Synthesis.Core.CallSequence (Window)
open Solcore.Synthesis.Stateful.CallBranchExecution (Transaction Bindings CallRow)

def caseSchema : String := "solcore-lean.semantic-call-branch-case.v1"
def planSchema : String := "solcore-lean.call-branch-plan.v1"
def profileVersion : String := "stateful-call-branches-v1/call-branch-seed-v1"
def templateVersion : String := "std-raw-call-branch-loop-sites-step-revert-odd-class-v1"
def corpusSchema : String := "solcore-lean.semantic-call-branch-corpus.v1"

abbrev validTransactions := Storage.validTransactions

def offsetBank : List Nat := Solcore.Synthesis.Source.CallSequence.offsetBank
def widthBank : List Nat := Solcore.Synthesis.Source.CallSequence.widthBank
def lengthBank : List Nat := Solcore.Synthesis.Source.CallSequence.lengthBank

/-- Random steps and the child's shell stay within the largest step budget. -/
def maxStepNodes : Nat := 512

private def w (value : Nat) : Word := Word.ofNatModulo value

/-- The child's shell and its step, which a node budget bounds. -/
def budgetNodes (plan : CheckedPlan) : Nat :=
  CallSequence.childShellNodes + Wire.programNodes plan.step.program

/-- The parent's phases: the call phase and the resume program. -/
def phasePrograms (plan : CheckedPlan) : List Wire.Program := [plan.callProgram, plan.resumeProgram]

def bounded (plan : CheckedPlan) : Bool :=
  Wire.programNodes plan.childProgram ≤ CallBranch.maxChildNodes &&
    (phasePrograms plan).all (Wire.programNodes · ≤ CallBranch.maxPhaseNodes)

structure CheckedScenario where private mk ::
  plan : CheckedPlan
  transactions : List Transaction
  valid : validTransactions transactions
  withinBounds : bounded plan = true

def checkedScenario (plan : CheckedPlan) (transactions : List Transaction) : Except String CheckedScenario := do
  if valid : validTransactions transactions then
    if withinBounds : bounded plan = true then
      return ⟨plan, transactions, valid, withinBounds⟩
    else throw "call-branch contracts exceed the 1024-node child or 2048-node phase limit"
  else throw s!"call-branch scenario requires 1..{Stateful.Sequence.maxTransactions} transactions with distinct valid IDs"

/-! ### Plans -/

def windowJson (window : Window) : Json :=
  Json.mkObj [("offset", toJson window.offset), ("width", toJson window.width)]

def kindName : Kind → String
  | .branch => "branch"
  | .loop => "loop"

def siteJson (site : Site) : Json := Json.mkObj [
  ("kind", toJson (kindName site.kind)), ("bound", toJson site.bound), ("stop", toJson site.stop),
  ("callWindow", windowJson site.callWindow), ("exitWindow", windowJson site.exitWindow)]

def planJson (plan : CheckedPlan) : Json := Json.mkObj [
  ("schema", toJson planSchema), ("sites", toJson (plan.sites.map siteJson)),
  ("stepProgram", Wire.encodeProgram plan.step.program)]

private def decodeWindow (json : Json) : Except String Window := do
  return {offset := ← json.getObjValAs? Nat "offset", width := ← json.getObjValAs? Nat "width"}

private def decodeSite (json : Json) : Except String Site := do
  let kind ← match ← json.getObjValAs? String "kind" with
    | "branch" => pure Kind.branch
    | "loop" => pure Kind.loop
    | _ => throw "a site is a branch or a loop"
  let bound ← json.getObjValAs? Nat "bound"
  let stop ← json.getObjValAs? Nat "stop"
  let callWindow ← decodeWindow (← json.getObjVal? "callWindow")
  let exitWindow ← decodeWindow (← json.getObjVal? "exitWindow")
  return ⟨kind, bound, stop, callWindow, exitWindow⟩

def checkedPlan (json : Json) : Except String CheckedPlan := do
  unless (← json.getObjValAs? String "schema") = planSchema do throw "unsupported call-branch plan schema"
  let sites ← (← (← json.getObjVal? "sites").getArr?).toList.mapM decodeSite
  let step ← Aggregate.checkedFunction (← json.getObjVal? "stepProgram")
  let some plan := CheckedPlan.ofParts? step sites
    | throw "call-branch plan needs one to three valid sites of at most three positions, and full host-Core admission"
  unless json == planJson plan do throw "call-branch plan differs from its canonical checked representation"
  return plan

/-! ### Transactions and their prescribed outcomes -/

/-- Each transaction's calls and whether the parent reverts, from the model. -/
def prescribed (plan : CheckedPlan) (fuel : Nat) (transactions : List Transaction) :
    Except String (List (List CallRow × Bool)) := do
  let some rows := Stateful.CallBranchExecution.model plan fuel transactions
    | throw "call-branch model exhausted Core fuel"
  return rows.map fun row => (row.calls, row.reverted)

def callRowJson (row : CallRow) : Json := Json.mkObj [
  ("position", toJson row.position), ("status", toJson (if row.returned then "returned" else "reverted")),
  ("length", toJson row.length)]

def transactionJson (tx : Transaction) (calls : List CallRow) (reverts : Bool) : Json := Json.mkObj [
  ("id", toJson tx.id), ("input", toJson (toString tx.input.val)),
  ("value", toJson "0"), ("target", toJson "parent"), ("callee", toJson "child"),
  ("calls", toJson (calls.map callRowJson)), ("parentReverts", toJson reverts)]

def transactionsJson (plan : CheckedPlan) (fuel : Nat) (transactions : List Transaction) : Except String Json := do
  let outcomes ← prescribed plan fuel transactions
  return toJson ((transactions.zip outcomes).map fun (tx, (calls, reverts)) => transactionJson tx calls reverts)

def decodeTransactions (plan : CheckedPlan) (fuel : Nat) (json : Json) : Except String (List Transaction) := do
  let transactions ← CallReturn.decodeSequence json
  unless json == (← transactionsJson plan fuel transactions) do
    throw "transactions differ from their canonical ID, input, role metadata or prescribed outcomes"
  return transactions

/-! ### Cases -/

def programsJson (plan : CheckedPlan) : Json := Json.mkObj [
  ("parentCall", Wire.encodeProgram plan.callProgram),
  ("parentResume", Wire.encodeProgram plan.resumeProgram),
  ("child", Wire.encodeProgram plan.childProgram)]

def observedSlotsJson (plan : CheckedPlan) : Json := Json.mkObj [
  ("parent", toJson ((Stateful.CallBranchExecution.parentSlots plan).map fun slot => toString slot.val)),
  ("child", toJson (Stateful.CallBranchExecution.childSlots.map fun slot => toString slot.val))]

def makeCase (scenario : CheckedScenario) (emitted : CallReturn.EmittedContracts) (origin : Json) (fuel : Nat)
    (revision : GeneratorRevision := .v1) (mask : FeatureMask := FeatureMask.all) : Except String Json := do
  return Json.mkObj [
    ("schema", toJson caseSchema), ("callBranchPlan", planJson scenario.plan),
    ("programs", programsJson scenario.plan),
    ("sources", Json.mkObj [("parent", toJson emitted.parentSource), ("child", toJson emitted.childSource)]),
    ("transactions", ← transactionsJson scenario.plan fuel scenario.transactions),
    ("initialState", CallReturn.initialStateJson), ("observedSlots", observedSlotsJson scenario.plan),
    ("provenance", Json.mkObj <| swarmField revision mask ++ [
      ("origin", origin), ("profileVersion", toJson profileVersion),
      ("functionVersion", toJson CallSequence.childVersion), ("parentVersion", toJson CallBranch.parentVersion),
      ("templateVersion", toJson templateVersion),
      ("stepProfileVersion", toJson Aggregate.profileVersion),
      ("stepFunctionVersion", toJson Aggregates.version),
      ("stepTemplateVersion", toJson Aggregate.templateVersion),
      ("generatorVersion", toJson revision.version),
      ("emitterVersion", toJson emitterVersion), ("wrapperVersion", toJson wrapperVersion),
      ("features", toJson scenario.plan.step.features)]),
    ("contracts", CallReturn.contractsJson), ("executionFuel", toJson fuel)]

def emitCase (scenario : CheckedScenario) (origin : Json) (fuel : Nat)
    (revision : GeneratorRevision := .v1) (mask : FeatureMask := FeatureMask.all) : Except String Json := do
  unless fuel ≤ 10000000 do throw "execution fuel exceeds limit"
  let emitted ← (emit scenario.plan).mapError reprStr
  makeCase scenario emitted origin fuel revision mask

private def decodeProgram (json : Json) : Except String Wire.Program :=
  (Wire.decodeProgramWithBudget {maxDepth := 512, maxNodes := CallBranch.maxPhaseNodes, maxIntegerBytes := 4096}
    json).mapError (fun
    | .protocol error => error.toJson.compress
    | .exhausted exhaustion => "Core decode budget exceeded: " ++ reprStr exhaustion)

private def sameProgram (json : Json) (expected : Wire.Program) : Except String Unit := do
  let program ← decodeProgram json
  unless Wire.encodeProgram program == Wire.encodeProgram expected do
    throw "saved original Core program differs from its canonical call-branch plan"

/-- Every origin must reconstruct the fixed host contracts, including imports
and reductions. Arbitrary well-typed programs are not admissible
replacements. -/
def caseProgram (json : Json) : Except String CheckedScenario := do
  unless (← json.getObjValAs? String "schema") = caseSchema do throw "unsupported semantic call-branch case schema"
  let plan ← checkedPlan (← json.getObjVal? "callBranchPlan")
  let fuel ← json.getObjValAs? Nat "executionFuel"
  unless fuel ≤ 10000000 do throw "saved execution fuel exceeds limit"
  let transactions ← decodeTransactions plan fuel (← json.getObjVal? "transactions")
  let originals ← json.getObjVal? "programs"
  sameProgram (← originals.getObjVal? "parentCall") plan.callProgram
  sameProgram (← originals.getObjVal? "parentResume") plan.resumeProgram
  sameProgram (← originals.getObjVal? "child") plan.childProgram
  unless originals == programsJson plan do throw "saved program roles are not canonical"
  unless (← json.getObjVal? "initialState") == CallReturn.initialStateJson do
    throw "initial accounts must be empty and unfunded"
  unless (← json.getObjVal? "observedSlots") == observedSlotsJson plan do
    throw "observed slots must be the parent's 0 to B + 4P and the child's 0 and 1"
  checkedScenario plan transactions

def observe (scenario : CheckedScenario) (bindings : Bindings) (fuel : Nat) : Json :=
  Stateful.CallBranchExecution.observe scenario.plan scenario.transactions bindings fuel

/-! ### Generation -/

/-- SplitMix64's finalizer. The generator's draws are affine in its start, so
consecutive seeds would otherwise start streams whose draws step by a fixed
residue. -/
private def mixed (value : Nat) : Nat :=
  let z := value % 2 ^ 64
  let z := (z ^^^ (z >>> 30)) * 0xbf58476d1ce4e5b9 % 2 ^ 64
  let z := (z ^^^ (z >>> 27)) * 0x94d049bb133111eb % 2 ^ 64
  z ^^^ (z >>> 31)

/-- High halves of successive draws from the stream that starts at the mixed
`seed` xor `domain`, each below its bound. -/
private def boundedDraws (seed : Seed) (domain : Nat) (bounds : List Nat) : List Nat := Id.run do
  let mut state := Seed.ofNat (mixed (seed.toNat ^^^ domain))
  let mut values : Array Nat := #[]
  for bound in bounds do
    let (value, next) := state.draw
    values := values.push (value.toNat / 2 ^ 32 % bound)
    state := next
  return values.toList

/-- Per site: the kind, a loop's bound draw, a stop selector and a uniform stop,
then per window an offset selector and a uniform offset, a width selector and a
uniform width. -/
def siteBounds : List Nat := [2, 6, 20, 97] ++ (List.replicate 2 [18, 97, 8, 33]).flatten

/-- The site count, then three sites' draws. -/
def planBounds : List Nat := [3] ++ (List.replicate 3 siteBounds).flatten

def planChoices (seed : Seed) : List Nat := boundedDraws seed 0x6272632d706c616e planBounds

/-- The bank entry when the selector names one, otherwise the uniform draw. -/
private def banked (bank : List Nat) (selector uniform : Nat) : Nat :=
  if selector < bank.length then bank.getD selector 0 else uniform

/-- One to three sites, each a branch or a loop whose bound is uniform from one
to the positions left; sites stop once three positions are used. -/
def generatedSites (seed : Seed) : List Site := Id.run do
  let choices := planChoices seed
  let mut sites : Array Site := #[]
  let mut used := 0
  for index in List.range (1 + choices.getD 0 0) do
    if used < CallBranch.maxCalls then
      let at_ := fun position => choices.getD (1 + siteBounds.length * index + position) 0
      let spot := fun first : Nat => (⟨banked offsetBank (at_ first) (at_ (first + 1)),
        banked widthBank (at_ (first + 2)) (at_ (first + 3))⟩ : Window)
      let site : Site := if at_ 0 == 0 then ⟨.branch, 1, 0, spot 4, spot 8⟩
        else ⟨.loop, 1 + at_ 1 % (CallBranch.maxCalls - used), banked lengthBank (at_ 2) (at_ 3), spot 4, spot 8⟩
      sites := sites.push site
      used := used + site.bound
  return sites.toList

/-- Per transaction: per position the revert draw, a length selector and a
uniform length; per site a control draw; the parent's revert draw; and seven
32-bit parts of `input >> 32`. -/
def transactionBounds : List Nat :=
  (List.replicate 3 [3, 20, 97]).flatten ++ List.replicate 3 4 ++ [4] ++ List.replicate 7 (2 ^ 32)

def sequenceBounds : List Nat := (List.replicate 3 transactionBounds).flatten

def sequenceChoices (seed : Seed) : List Nat := boundedDraws seed 0x6272632d74786e73 sequenceBounds

/-- An input from its draws: each position's class byte `2L + revert`, each
site's control bits, the parent's revert at bit 30 and the high part from bit
32. A branch takes one bit and a loop two. -/
def inputOf (sites : List Site) (draws : List Nat) : Word :=
  let positions := CallBranch.positions sites
  let classes := (List.range positions).map fun position =>
    let at_ := fun offset => draws.getD (3 * position + offset) 0
    2 * banked lengthBank (at_ 1) (at_ 2) + (if at_ 0 == 0 then 1 else 0)
  let low := classes.zipIdx.foldl (fun total (value, position) => total + value * 2 ^ (8 * position)) 0
  let control := sites.zipIdx.foldl (fun total (site, index) =>
    let draw := draws.getD (9 + index) 0
    let bits := match site.kind with
      | .branch => draw % 2
      | .loop => draw
    total + bits * 2 ^ CallBranch.controlBit index) 0
  let reverts := if draws.getD 12 0 == 0 then 2 ^ CallBranch.revertBit else 0
  let high := (List.range 7).foldl (fun total part => total * 2 ^ 32 + draws.getD (13 + part) 0) 0
  w (high * 2 ^ 32 + reverts + control + low)

def blockTransactions (sites : List Site) (seed : Seed) (first : Nat) : List Transaction :=
  let choices := sequenceChoices seed
  (List.range 3).map fun index =>
    ⟨"tx-" ++ toString (first + index), inputOf sites (choices.drop (transactionBounds.length * index))⟩

/-- The first `count` transactions of the seed's consecutive blocks. -/
def generatedTransactions (sites : List Site) (seed : Seed) (count : Nat := 3) : List Transaction :=
  Stateful.Sequence.blocks (blockTransactions sites) seed count

/-- The child's shell lies inside the budget with the step, which the complete
measure bounds again. -/
def generatedScenario (seed : Seed) (nodes : Nat) (revision : GeneratorRevision := .v1)
    (transactions : Nat := 3) : Except String (CheckedScenario × Json) := do
  Stateful.Sequence.checkCount transactions
  let sites := generatedSites seed
  let shell := CallSequence.childShellNodes
  unless nodes ≤ maxStepNodes && shell < nodes do
    throw "node budget is too small for the call-branch child or exceeds 512"
  let (step, stepOrigin) ← Aggregate.generatedFunction seed (nodes - shell) revision
  let some plan := CheckedPlan.ofParts? step sites | throw "generated call-branch plan failed full Core admission"
  let scenario ← checkedScenario plan (generatedTransactions sites seed transactions)
  unless budgetNodes scenario.plan ≤ nodes do throw "call-branch child exceeds its requested node budget"
  return (scenario, Stateful.Sequence.recordCount (Json.mkObj [
    ("kind", toJson "call-branch-generated"), ("seed", toJson (toString seed.toNat)),
    ("finalSeed", ← stepOrigin.getObjVal? "finalSeed"), ("maxProgramNodes", toJson nodes),
    ("stepOrigin", stepOrigin), ("planChoices", toJson (planChoices seed)),
    ("sequenceChoices", toJson (Stateful.Sequence.blockChoices sequenceChoices seed transactions))]) transactions)

private def rowStatus (row : Json) : Option String := (row.getObjValAs? String "status").toOption

/-- The history must complete with the model's outcomes. -/
def validateGenerated (scenario : CheckedScenario) (fuel : Nat) : Except String Unit := do
  Aggregate.inputSensitive scenario.plan.step fuel
  let observed := observe scenario Solcore.Synthesis.Stateful.NestedCallExecution.fixtureBindings fuel
  let rows ← observed.getObjValAs? (List Json) "transactions"
  unless (← observed.getObjValAs? String "status") = "complete" do
    if rows.any (fun row => rowStatus row == some "out-of-fuel") then throw "call-branch history exhausted Core fuel"
    else throw "call-branch history stopped without a permitted root completion"
  let some expected := Stateful.CallBranchExecution.model scenario.plan fuel scenario.transactions
    | throw "call-branch history exhausted Core fuel"
  unless rows.map rowStatus == expected.map (fun row => some (if row.reverted then "reverted" else "returned")) do
    throw "call-branch history did not follow its prescribed outcomes"

def generateCases (firstSeed : Seed) (nodes count attempts fuel : Nat)
    (revision : GeneratorRevision := .v1) (transactions : Nat := 3) : Json := Id.run do
  let mut cases : Array Json := #[]
  let mut excluded : Array Json := #[]
  let mut attempted := 0
  for index in List.range attempts do
    if cases.size < count then
      attempted := attempted + 1
      let seed := Seed.ofNat (firstSeed.toNat + index)
      let result := do
        unless fuel ≤ 10000000 do throw "execution fuel exceeds limit"
        let (scenario, origin) ← generatedScenario seed nodes revision transactions
        let emitted ← (emit scenario.plan).mapError reprStr
        validateGenerated scenario fuel
        makeCase scenario emitted (origin.setObjVal! "validationFuel" (toJson fuel)) fuel revision (revision.caseMask seed)
      match result with
      | .error error =>
          let resource := error == "boundary observation exhausted Core fuel" ||
            error == "call-branch history exhausted Core fuel" || error == "call-branch model exhausted Core fuel"
          excluded := excluded.push (Json.mkObj [
            ("seed", toJson (toString seed.toNat)), ("stage", toJson "call-branch-profile"),
            ("reason", toJson error),
            ("code", toJson (if resource then "validation-out-of-fuel" else "profile-excluded")),
            ("category", toJson (if resource then "inconclusive-resource" else "excluded"))])
      | .ok case => cases := cases.push case
  return Json.mkObj [("schema", toJson corpusSchema),
    ("requested", toJson count), ("attempted", toJson attempted),
    ("status", toJson (if cases.size = count then "complete" else "generation-exhausted")),
    ("excluded", .arr excluded), ("cases", .arr cases)]

/-! ### Reductions -/

/-- The windows' offsets and widths and the loops' stop lengths. -/
def siteWeight (plan : CheckedPlan) : Nat :=
  plan.sites.foldl (fun total site => total + site.callWindow.offset + site.callWindow.width +
    site.exitWindow.offset + site.exitWindow.width + site.stop) 0

def inputWeight (scenario : CheckedScenario) : Nat :=
  scenario.transactions.foldl (fun total transaction => total + transaction.input.val) 0

def scenarioComplexity (scenario : CheckedScenario) : Complexity := complexity scenario.plan.childProgram.body

/-- Transaction count, site count, positions, the windows and stops, the child's
size and literals, then the inputs. Every axis is a natural number and the
comparison is strictly lexicographic. -/
def StrictlySmaller (candidate source : CheckedScenario) : Prop :=
  candidate.transactions.length < source.transactions.length ∨
  (candidate.transactions.length = source.transactions.length ∧
    (candidate.plan.sites.length < source.plan.sites.length ∨
    (candidate.plan.sites.length = source.plan.sites.length ∧
      (candidate.plan.positions < source.plan.positions ∨
      (candidate.plan.positions = source.plan.positions ∧
        (siteWeight candidate.plan < siteWeight source.plan ∨
        (siteWeight candidate.plan = siteWeight source.plan ∧
          ((scenarioComplexity candidate).StrictlySmaller (scenarioComplexity source) ∨
          (scenarioComplexity candidate = scenarioComplexity source ∧
            inputWeight candidate < inputWeight source)))))))))

instance (candidate source : CheckedScenario) : Decidable (StrictlySmaller candidate source) := by
  unfold StrictlySmaller
  infer_instance

structure Reduction (source : CheckedScenario) where private mk ::
  candidate : CheckedScenario
  sameHelperCount : candidate.plan.step.helpers.length = source.plan.step.helpers.length
  sameBindings : Aggregate.bindingInventory candidate.plan.step = Aggregate.bindingInventory source.plan.step
  stableIds : (candidate.transactions.map (·.id)).Sublist (source.transactions.map (·.id))
  strict : StrictlySmaller candidate source

private def sealReduction (source : CheckedScenario) (step : Aggregates.CheckedDAG) (sites : List Site)
    (transactions : List Transaction) : Option (Reduction source) := do
  let plan ← CheckedPlan.ofParts? step sites
  let candidate ← (checkedScenario plan transactions).toOption
  if count : candidate.plan.step.helpers.length = source.plan.step.helpers.length then
    if bindings : Aggregate.bindingInventory candidate.plan.step = Aggregate.bindingInventory source.plan.step then
      if ids : (candidate.transactions.map (·.id)).Sublist (source.transactions.map (·.id)) then
        if strict : StrictlySmaller candidate source then some ⟨candidate, count, bindings, ids, strict⟩
        else none
      else none
    else none
  else none

/-- The earlier entries of a bank before `value`, or the whole bank when it is
not in it, below `value`. -/
private def earlier (bank : List Nat) (value : Nat) : List Nat :=
  (bank.take ((bank.idxOf? value).getD bank.length)).filter (· < value)

/-- A window's smaller variants: an earlier offset, then an earlier or zero
width. -/
private def smallerWindows (spot : Window) : List Window :=
  (earlier offsetBank spot.offset).map (fun offset => {spot with offset}) ++
    (earlier widthBank spot.width ++ (if spot.width > 0 then [0] else [])).eraseDups.map fun width => {spot with width}

/-- An input's smaller variants: the parent's revert cleared, the high part
cleared, each control bit cleared, and per class byte its revert cleared and
its length an earlier bank entry, then zero. -/
def smallerInputs (input : Word) : List Word :=
  let value := input.val
  let byte := fun position => value / 2 ^ (8 * position) % 256
  let replace := fun position (next : Nat) => w (value - byte position * 2 ^ (8 * position) + next * 2 ^ (8 * position))
  let revert := if value / 2 ^ CallBranch.revertBit % 2 == 1 then [w (value - 2 ^ CallBranch.revertBit)] else []
  let high := if value ≥ 2 ^ 32 then [w (value % 2 ^ 32)] else []
  let controls := (List.range 6).filterMap fun offset =>
    let bit := 24 + offset
    if value / 2 ^ bit % 2 == 1 then some (w (value - 2 ^ bit)) else none
  let classes := (List.range CallBranch.maxCalls).flatMap fun position =>
    let class_ := byte position
    let length := min (class_ / 2) CallSequence.capacity
    (if class_ % 2 == 1 then [replace position (class_ - 1)] else []) ++
      ((earlier lengthBank length ++ (if length > 0 then [0] else [])).eraseDups.map fun shorter =>
        replace position (2 * shorter + class_ % 2))
  revert ++ high ++ controls ++ classes

/-- One-transaction removals, the last site dropped, a loop's bound lowered,
earlier or narrower windows and earlier stops, step reductions, then per
transaction each smaller input. Candidates still need execution to establish
that they preserve a finding. -/
def reductions (source : CheckedScenario) : List (Reduction source) := Id.run do
  let sites := source.plan.sites
  let mut raw : List (Aggregates.CheckedDAG × List Site × List Transaction) := []
  -- Removing one transaction comes first, from the last back: a long
  -- sequence loses the tail beyond a difference before the candidate limit.
  for index in (List.range source.transactions.length).reverse do
    raw := raw ++ [(source.plan.step, sites,
      (source.transactions.zipIdx.filter (fun (_, current) => current != index)).map Prod.fst)]
  if sites.length > 1 then
    raw := raw ++ [(source.plan.step, sites.dropLast, source.transactions)]
  for (site, index) in sites.zipIdx do
    if site.kind == .loop && site.bound > 1 then
      raw := raw ++ [(source.plan.step, sites.set index {site with bound := site.bound - 1}, source.transactions)]
  for (site, index) in sites.zipIdx do
    for spot in smallerWindows site.callWindow do
      raw := raw ++ [(source.plan.step, sites.set index {site with callWindow := spot}, source.transactions)]
    for spot in smallerWindows site.exitWindow do
      raw := raw ++ [(source.plan.step, sites.set index {site with exitWindow := spot}, source.transactions)]
    for stop in earlier lengthBank site.stop do
      raw := raw ++ [(source.plan.step, sites.set index {site with stop}, source.transactions)]
  for reduced in Aggregate.reductions ⟨source.plan.step, Word.zero⟩ do
    raw := raw ++ [(reduced.candidate.function, sites, source.transactions)]
  for (transaction, index) in source.transactions.zipIdx do
    for input in smallerInputs transaction.input do
      let transactions := source.transactions.set index {transaction with input}
      raw := raw ++ [(source.plan.step, sites, transactions)]
  let mut seen : List String := []
  let mut result := []
  for (step, sites, transactions) in raw do
    if let some reduced := sealReduction source step sites transactions then
      let identity := (Json.mkObj [("plan", planJson reduced.candidate.plan),
        ("transactions", toJson (reduced.candidate.transactions.map fun tx => toString tx.input.val ++ tx.id))]).compress
      if !seen.contains identity then
        seen := identity :: seen
        result := result ++ [reduced]
  return result

private def sequenceJson (transactions : List Transaction) : Json :=
  toJson (transactions.map fun tx => Json.mkObj [("id", toJson tx.id), ("input", toJson (toString tx.input.val))])

private def reducedOrigin (parent : CheckedScenario) : Json := Json.mkObj [
  ("kind", toJson "reduced"), ("parentPlan", planJson parent.plan),
  ("parentPrograms", programsJson parent.plan), ("parentTransactions", sequenceJson parent.transactions)]

def replayCase (json : Json) (fuel : Nat) : Except String Json := do
  unless fuel ≤ 10000000 do throw "execution fuel exceeds limit"
  let admitted ← caseProgram json
  let provenance ← json.getObjVal? "provenance"
  let revision := savedRevision provenance
  let mask ← savedMask provenance revision
  for (name, expected) in [
      ("generatorVersion", revision.version), ("profileVersion", profileVersion),
      ("functionVersion", CallSequence.childVersion), ("parentVersion", CallBranch.parentVersion),
      ("templateVersion", templateVersion),
      ("stepProfileVersion", Aggregate.profileVersion), ("stepFunctionVersion", Aggregates.version),
      ("stepTemplateVersion", Aggregate.templateVersion),
      ("emitterVersion", emitterVersion), ("wrapperVersion", wrapperVersion)] do
    unless (← provenance.getObjValAs? String name) = expected do throw (name ++ " changed")
  let origin ← provenance.getObjVal? "origin"
  let emitted ← (emit admitted.plan).mapError reprStr
  let sources ← json.getObjVal? "sources"
  unless (← sources.getObjValAs? String "parent") = emitted.parentSource &&
      (← sources.getObjValAs? String "child") = emitted.childSource &&
      sources == Json.mkObj [("parent", toJson emitted.parentSource), ("child", toJson emitted.childSource)] do
    throw "saved sources differ from call-branch plan emission"
  unless (← json.getObjVal? "contracts") == CallReturn.contractsJson do
    throw "saved contract metadata differs from call-branch wrappers"
  unless (← provenance.getObjVal? "features") == toJson admitted.plan.step.features do throw "saved features differ from checked step"
  let kind ← origin.getObjValAs? String "kind"
  if kind = "call-branch-generated" then
    let seedText ← origin.getObjValAs? String "seed"
    unless seedText.length ≤ 20 do throw "invalid saved seed"
    let some seed := seedText.toNat? | throw "invalid saved seed"
    unless seed < 2 ^ 64 && toString seed = seedText do throw "noncanonical saved seed"
    unless mask == revision.caseMask (Seed.ofNat seed) do throw "saved swarm mask differs from its generation seed"
    let (expected, expectedOrigin) ← generatedScenario (Seed.ofNat seed) (← origin.getObjValAs? Nat "maxProgramNodes") revision
      (← Stateful.Sequence.savedCount origin)
    let validationFuel ← origin.getObjValAs? Nat "validationFuel"
    unless validationFuel ≤ 10000000 do throw "saved validation fuel exceeds limit"
    unless origin == expectedOrigin.setObjVal! "validationFuel" (toJson validationFuel) do
      throw "saved origin differs from generated call-branch provenance"
    unless planJson expected.plan == planJson admitted.plan &&
        sequenceJson expected.transactions == sequenceJson admitted.transactions do
      throw "saved plan or transaction sequence differs from its generation seed"
    validateGenerated expected validationFuel
  else if kind = "imported" then
    unless origin == Json.mkObj [("kind", toJson "imported")] do throw "noncanonical imported origin"
  else if kind = "reduced" then
    let parentPlan ← checkedPlan (← origin.getObjVal? "parentPlan")
    let parentTransactions ← CallReturn.decodeSequence (← origin.getObjVal? "parentTransactions")
    let parent ← checkedScenario parentPlan parentTransactions
    unless (← origin.getObjVal? "parentPrograms") == programsJson parent.plan do
      throw "reduction parent programs differ from their plan"
    unless (sealReduction parent admitted.plan.step admitted.plan.sites admitted.transactions).isSome do
      throw "reduction does not preserve bindings/IDs or decrease the complete scenario"
    unless origin == reducedOrigin parent do throw "noncanonical reduced origin"
  else throw "unsupported call-branch case origin"
  makeCase admitted emitted origin fuel revision mask

def shrinkCases (json : Json) (limit fuel : Nat) : Except String Json := do
  let _ ← replayCase json fuel
  let source ← caseProgram json
  -- Reductions inherit the parent case's recorded G0 revision and swarm mask.
  let provenance ← json.getObjVal? "provenance"
  let revision := savedRevision provenance
  let mask ← savedMask provenance revision
  let cases ← ((reductions source).take limit).mapM fun reduced =>
    emitCase reduced.candidate (reducedOrigin source) fuel revision mask
  return Json.mkObj [("schema", toJson corpusSchema), ("cases", toJson cases)]

/-! ### Imported scenarios -/

/-- An imported plan and transaction sequence. -/
def checkedImport (plan : CheckedPlan) (transactions : List Transaction) : Except String CheckedScenario :=
  checkedScenario plan transactions

end Solcore.Synthesis.Source.CallBranch
end
