import Solcore.Frontend.RustHull.Memory

/-! Ethereum Keccak-256 compiled to ordinary Core. The permutation uses 64-bit
lanes represented by masked words; absorption and padding run on the Core
machine, with the same suspension and resumption behavior as other code. -/
set_option autoImplicit false

namespace Solcore.Frontend.RustHull.Keccak
open Core

def number (value : Nat) : Expr := .word (Word.ofNatModulo value)
def xor (left right : Expr) : Expr := .binary .wordXor left right
def add (left right : Expr) : Expr := .binary .wordAdd left right
def shift (value : Expr) (distance : Nat) : Expr :=
  .binary .wordShl value (number distance)
def move (expression : Expr) (depth : Nat) : Expr :=
  expression.rename fun index => index + depth
def packet : List Expr → Expr
  | [] => .unit
  | [value] => value
  | value :: rest => .pair value (packet rest)
def field (index : Nat) : Nat → Expr → Expr
  | 0, _ => .unit
  | 1, value => value
  | count + 2, value => if index = 0 then .first value
      else field (index - 1) (count + 1) (.second value)
def types : List Ty → Ty
  | [] => .unit
  | [type] => type
  | type :: rest => .product type (types rest)

def stateType : Ty := types (List.replicate 25 .word)
def lane (index : Nat) (state : Expr) : Expr := field index 25 state
def zeroState : Expr := packet (List.replicate 25 (number 0))

def constants : List Nat := [
  0x0000000000000001, 0x0000000000008082,
  0x800000000000808a, 0x8000000080008000,
  0x000000000000808b, 0x0000000080000001,
  0x8000000080008081, 0x8000000000008009,
  0x000000000000008a, 0x0000000000000088,
  0x0000000080008009, 0x000000008000000a,
  0x000000008000808b, 0x800000000000008b,
  0x8000000000008089, 0x8000000000008003,
  0x8000000000008002, 0x8000000000000080,
  0x000000000000800a, 0x800000008000000a,
  0x8000000080008081, 0x8000000000008080,
  0x0000000080000001, 0x8000000080008008]

def rotations : List Nat := [
   0,  1, 62, 28, 27,
  36, 44,  6, 55, 20,
   3, 10, 43, 25, 39,
  41, 45, 15, 21,  8,
  18,  2, 61, 56, 14]

def rotate (value : Expr) (distance : Nat) : Expr :=
  if distance = 0 then value
  else .binary .wordAnd
    (.binary .wordOr (shift value distance)
      (.binary .wordShr value (number (64 - distance))))
    (number (2 ^ 64 - 1))

def destination (index : Nat) : Nat :=
  index / 5 + 5 * ((2 * (index % 5) + 3 * (index / 5)) % 5)

def source (index : Nat) : Nat :=
  ((List.range 25).find? (fun candidate => destination candidate = index)).getD 0

def roundBody : Expr :=
  let parities := (List.range 5).map fun column =>
    (List.range 5).foldl (fun parity row =>
      xor parity (lane (column + 5 * row) (.first (.var column)))) (number 0)
  let deltas := (List.range 5).map fun column =>
    xor (.var (4 - ((column + 4) % 5) + column))
      (rotate (.var (4 - ((column + 1) % 5) + column)) 1)
  let rotated := (List.range 25).map fun index =>
    rotate (xor (lane index (.first (.var (10 + index))))
      (.var (4 - index % 5 + index))) (rotations[index]?.getD 0)
  let b := fun index => Expr.var (24 - source index)
  let lanes := (List.range 25).map fun index =>
    let x := index % 5
    let y := index / 5
    let value := xor (b index)
      (.binary .wordAnd (.unary .wordNot (b (((x + 1) % 5) + 5 * y)))
        (b (((x + 2) % 5) + 5 * y)))
    if index = 0 then xor value (.second (.var 35)) else value
  (parities ++ deltas ++ rotated).foldr Expr.letE (packet lanes)

def roundCalls : Nat → List Nat → Expr
  | _, [] => .var 0
  | depth, constant :: rest =>
      .letE (.apply (.var (depth + 1)) (.pair (.var 0) (number constant)))
        (roundCalls (depth + 1) rest)

/-- Apply all 24 Keccak-f1600 rounds to a 25-lane Core value. -/
def permute (state : Expr) : Expr :=
  .letE (.lambda (.product stateType .word) stateType roundBody)
    (.letE (state.weakenAt 0) (roundCalls 0 constants))

def paddedByte (mapping offset remaining : Expr) (index : Nat) : Expr :=
  .ifE (.binary .wordGt remaining (number index))
    (Memory.readMemoryByte mapping (add offset (number index)))
    (LanguageResult.success
      (add (.ifE (.binary .wordEq remaining (number index)) (number 1) (number 0))
        (number (if index = 135 then 128 else 0))))

def readLane : Nat → Nat → Expr → Expr → Expr → Expr → Expr
  | 0, _, _, _, _, accumulator => LanguageResult.success accumulator
  | count + 1, index, mapping, offset, remaining, accumulator =>
      LanguageResult.bind .word (paddedByte mapping offset remaining index)
        (readLane count (index + 1) (mapping.weakenAt 0) (offset.weakenAt 0)
          (remaining.weakenAt 0)
          (.binary .wordOr (accumulator.weakenAt 0) (shift (.var 0) (8 * (index % 8)))))

def absorbBlock (mapping offset remaining state : Expr) : Expr :=
  let computations := (List.range 17).map fun index =>
    readLane 8 (8 * index) (move mapping index) (move offset index)
      (move remaining index) (number 0)
  let lanes := (List.range 25).map fun index =>
    if index < 17 then xor (lane index (move state 17)) (.var (16 - index))
    else lane index (move state 17)
  computations.foldr (LanguageResult.bind stateType) (LanguageResult.success (packet lanes))

def digest (state : Expr) : Expr :=
  (List.range 32).foldl (fun output index =>
    .binary .wordOr output
      (shift (.binary .wordByte (number (31 - index % 8)) (lane (index / 8) state))
        (8 * (31 - index)))) (number 0)

def parameterType : Ty :=
  types [WordMapping.type, .word, .word, stateType]

def absorbBody : Expr :=
  LanguageResult.bind .word
    (absorbBlock (field 0 4 (.var 0)) (field 1 4 (.var 0))
      (field 2 4 (.var 0)) (field 3 4 (.var 0)))
    (.letE (permute (.var 0))
      (.ifE (.binary .wordGt (number 136) (field 2 4 (.var 2)))
        (LanguageResult.success (digest (.var 0)))
        (WordMapping.invoke parameterType .word (.var 3)
          (packet [field 0 4 (.var 2), add (field 1 4 (.var 2)) (number 136),
            .binary .wordSub (field 2 4 (.var 2)) (number 136), .var 0]))))

/-- Hash a memory byte range using Ethereum's 0x01 domain suffix. Memory expands
for the input range only. Padding is computed inside Core and never written to
memory. Zero-length inputs do not touch the size cell, even at a large offset. -/
def hash (memoryReference sizeReference offset length : Expr) : Expr :=
  .letE (packet [memoryReference, sizeReference, offset, length])
    (LanguageResult.bind .word
      (Memory.touch (field 1 4 (.var 0)) (field 2 4 (.var 0)) (field 3 4 (.var 0)))
      (WordMapping.runHelper parameterType .word absorbBody
        (packet [.loadCell (field 0 4 (.var 1)), field 2 4 (.var 1),
          field 3 4 (.var 1), zeroState])))

end Solcore.Frontend.RustHull.Keccak
