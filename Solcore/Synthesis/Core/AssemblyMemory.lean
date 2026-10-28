import Solcore.Synthesis.Core.WordFunction
import Solcore.Synthesis.Core.Shrink
import Solcore.Core.Wire.Conversions
import Solcore.Frontend.RustHull.Keccak

/-! The original Core reference of an inline Yul memory plan: a step function
and a schedule over the 96-byte window above the free-memory pointer. The
reference keeps no memory. The window is three let-bound Words with byte
placement as shifts and masks, and the optional hash is a let-bound closure
over two read Words built from the Core Keccak-f[1600] permutation and digest
builders of the Hull import path, the builders of the mapping profile's
closure. Nothing here reads the Yul text. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Core.AssemblyMemory

open Solcore.Core (Word)
open Solcore.Core.Wire
open Solcore.Frontend.RustHull

def version : String := "core-assembly-memory-v1"

/-- The window's bytes; word accesses start in 0..64 and byte writes in 0..95. -/
def windowBytes : Nat := 96
def hashLengths : List Nat := [0, 1, 31, 32, 33, 64]
def maximumStages : Nat := 3

inductive Width where
  | word
  | byte
  deriving Repr, BEq, DecidableEq, Inhabited

namespace Width

def name : Width → String
  | .word => "word"
  | .byte => "byte"

def ofString? : String → Option Width
  | "word" => some .word
  | "byte" => some .byte
  | _ => none

end Width

/-- Read a Word, then write the step's result on it as a Word or one byte. -/
structure Stage where
  read : Nat
  width : Width
  write : Nat
  deriving Repr, BEq, DecidableEq, Inhabited

structure Hash where
  offset : Nat
  length : Nat
  deriving Repr, BEq, DecidableEq, Inhabited

structure Schedule where
  stages : List Stage
  final : Nat
  hash : Option Hash
  deriving Repr, BEq, DecidableEq, Inhabited

namespace Schedule

def admitted (schedule : Schedule) : Bool :=
  1 ≤ schedule.stages.length && schedule.stages.length ≤ maximumStages &&
  schedule.stages.all (fun stage => stage.read ≤ 64 &&
    match stage.width with
    | .word => stage.write ≤ 64
    | .byte => stage.write < windowBytes) &&
  schedule.final ≤ 64 &&
  match schedule.hash with
  | none => true
  | some hash => hashLengths.contains hash.length && hash.offset + hash.length ≤ windowBytes

/-- Zero without a hash, else one more than the length's position. -/
def hashRank (schedule : Schedule) : Nat :=
  match schedule.hash with
  | none => 0
  | some hash => hashLengths.idxOf hash.length + 1

def offsets (schedule : Schedule) : List Nat :=
  schedule.stages.flatMap (fun stage => [stage.read, stage.write]) ++ [schedule.final] ++
    (schedule.hash.map (·.offset)).toList

def deltaSum (schedule : Schedule) : Nat := (schedule.offsets.map (· % 32)).sum

end Schedule

/-- Byte `position` of the 64-byte message `first ++ second`, big-endian. -/
private def messageByte (first second : Solcore.Core.Expr) (position : Nat) : Solcore.Core.Expr :=
  if position < 32 then .binary .wordByte (Keccak.number position) first
  else .binary .wordByte (Keccak.number (position - 32)) second

/-- Lane `chunk` of the first `length` message bytes, little-endian as Keccak
absorbs it; bytes past the prefix are absent. -/
private def prefixLane (first second : Solcore.Core.Expr) (length chunk : Nat) : Solcore.Core.Expr :=
  (List.range 8).foldl (fun lane index =>
    if 8 * chunk + index < length then
      .binary .wordOr lane (Keccak.shift (messageByte first second (8 * chunk + index)) (8 * index))
    else lane) (Keccak.number 0)

/-- The absorbed state of one 136-byte rate block holding the first `length`
bytes of `first ++ second`, Ethereum's `0x01` domain byte at offset `length`
and the final `0x80` at offset 135. At length 64 this is the mapping profile's
block. -/
def prefixBlock (first second : Solcore.Core.Expr) (length : Nat) : Solcore.Core.Expr :=
  Keccak.packet ((List.range 25).map fun index =>
    let padding := (if index = length / 8 then 2 ^ (8 * (length % 8)) else 0) +
      (if index = 16 then 2 ^ 63 else 0)
    if 8 * index < length then
      if padding = 0 then prefixLane first second length index
      else .binary .wordOr (prefixLane first second length index) (Keccak.number padding)
    else Keccak.number padding)

/-- `fun (first, second) => keccak256(first ++ second)[..length]` in ordinary Core. -/
def coreHash (length : Nat) : Solcore.Core.Expr :=
  .lambda (.product .word .word) .word
    (.letE (.first (.var 0))
      (.letE (.second (.var 1))
        (.letE (Keccak.permute (prefixBlock (.var 1) (.var 0) length)) (Keccak.digest (.var 0)))))

/-- The closure as a Wire expression. A failed conversion would leave an
ill-typed `Unit` that full admission rejects, never a different hash. -/
def hashClosure (length : Nat) : Expr := (Expr.ofCore? (coreHash length)).getD .unit

private def word (value : Nat) : Expr := .word (Word.ofNatModulo value)
private def shl (value : Expr) (bits : Nat) : Expr := .binary .wordShl value (word bits)
private def shr (value : Expr) (bits : Nat) : Expr := .binary .wordShr value (word bits)
private def band (left right : Expr) : Expr := .binary .wordAnd left right
private def bor (left right : Expr) : Expr := .binary .wordOr left right

/-- The first `count` bytes of a Word, and its last `count` bytes. -/
def high (count : Nat) : Nat := 2 ^ 256 - 2 ^ (8 * (32 - count))
def low (count : Nat) : Nat := 2 ^ (8 * count) - 1

/-- Let-bound values in binding order and the binding of each window Word. A
reference is valid in the next initializer or in the final body. -/
private structure Builder where
  bindings : Array Expr := #[]
  words : List Nat := []

namespace Builder

def ref (builder : Builder) (position : Nat) : Expr := .var (builder.bindings.size - 1 - position)

def bind (builder : Builder) (value : Expr) : Builder × Nat :=
  ({builder with bindings := builder.bindings.push value}, builder.bindings.size)

def close (builder : Builder) (body : Expr) : Expr :=
  builder.bindings.foldr (fun value rest => .letE value rest) body

/-- Words past the window are zero. -/
def wordAt (builder : Builder) (index : Nat) : Expr :=
  match builder.words[index]? with
  | some position => builder.ref position
  | none => word 0

def setWord (builder : Builder) (index position : Nat) : Builder :=
  {builder with words := builder.words.set index position}

/-- The big-endian Word at byte `offset` of the window. -/
def load (builder : Builder) (offset : Nat) : Expr :=
  let index := offset / 32
  let delta := offset % 32
  if delta = 0 then builder.wordAt index
  else if index + 1 < 3 then
    bor (shl (builder.wordAt index) (8 * delta)) (shr (builder.wordAt (index + 1)) (8 * (32 - delta)))
  else shl (builder.wordAt index) (8 * delta)

/-- A Word write of the value bound at `value`. -/
def store (builder : Builder) (offset value : Nat) : Builder :=
  let index := offset / 32
  let delta := offset % 32
  if delta = 0 then builder.setWord index value
  else
    let (builder, first) := builder.bind
      (bor (band (builder.wordAt index) (word (high delta))) (shr (builder.ref value) (8 * delta)))
    let builder := builder.setWord index first
    let (builder, second) := builder.bind
      (bor (band (builder.wordAt (index + 1)) (word (low (32 - delta))))
        (shl (builder.ref value) (8 * (32 - delta))))
    builder.setWord (index + 1) second

/-- A byte write of the low byte of the value bound at `value`. -/
def store8 (builder : Builder) (offset value : Nat) : Builder :=
  let index := offset / 32
  let bits := 8 * (31 - offset % 32)
  let (builder, updated) := builder.bind
    (bor (band (builder.wordAt index) (word (2 ^ 256 - 1 - 255 * 2 ^ bits)))
      (shl (band (builder.ref value) (word 255)) bits))
  builder.setWord index updated

end Builder

/-- The reference program of `step`, a closed Word-to-Word lambda, under a
schedule at an input: the closure first when the schedule hashes, then the
step, the input and the prologue Words, then each stage's read, its step
application and its write, and finally the step on the final read, plus the
hash of the Words read at the hash offset and 32 bytes later. -/
def program (step : Expr) (schedule : Schedule) (input : Word) : Program := Id.run do
  let mut builder : Builder := {}
  let mut closure : Option Nat := none
  if let some hash := schedule.hash then
    let (next, position) := builder.bind (hashClosure hash.length)
    builder := next
    closure := some position
  let (next, function) := builder.bind step
  builder := next
  let (next, argument) := builder.bind (.word input)
  builder := next
  let (next, applied) := builder.bind (.apply (builder.ref function) (builder.ref argument))
  builder := next
  let (next, complement) := builder.bind (.unary .wordNot (builder.ref argument))
  builder := {next with words := [argument, applied, complement]}
  for stage in schedule.stages do
    let (next, read) := builder.bind (builder.load stage.read)
    builder := next
    let (next, value) := builder.bind (.apply (builder.ref function) (builder.ref read))
    builder := next
    builder := match stage.width with
      | .word => builder.store stage.write value
      | .byte => builder.store8 stage.write value
  let (next, read) := builder.bind (builder.load schedule.final)
  builder := next
  let result : Expr := .apply (builder.ref function) (builder.ref read)
  let body := match schedule.hash, closure with
    | some hash, some position =>
        .binary .wordAdd result (.apply (builder.ref position)
          (.pair (builder.load hash.offset)
            (if hash.length > 32 then builder.load (hash.offset + 32) else word 0)))
    | _, _ => result
  return {resultType := .word, dataDefinitions := [], body := builder.close body}

end Solcore.Synthesis.Core.AssemblyMemory
