import Solcore.Frontend.RustHull.MemoryCopySemantics

/-! Independent Keccak-256 over packed source memory. Lanes use little-endian
bytes, the rate is 136 bytes, and padding uses the Ethereum domain suffix. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.KeccakSemantics
open Core

abbrev State := List Word

def lane (state : State) (index : Nat) : Word := state[index]?.getD Word.zero

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

def rotate (value : Word) (distance : Nat) : Word :=
  if distance = 0 then value
  else ((value.shiftLeft (Word.ofNatModulo distance)).bitOr
    (value.shiftRight (Word.ofNatModulo (64 - distance)))).bitAnd (Word.ofNatModulo (2 ^ 64 - 1))

def parity (state : State) (column : Nat) : Word :=
  (List.range 5).foldl (fun value row => value.bitXor (lane state (column + 5 * row))) Word.zero

def delta (state : State) (column : Nat) : Word :=
  (parity state ((column + 4) % 5)).bitXor (rotate (parity state ((column + 1) % 5)) 1)

def rotated (state : State) (index : Nat) : Word :=
  rotate ((lane state index).bitXor (delta state (index % 5))) (rotations[index]?.getD 0)

/-- Inverse of the lane permutation (x, y) ↦ (y, 2*x + 3*y mod 5). -/
def source (index : Nat) : Nat := (index % 5 + 3 * (index / 5)) % 5 + 5 * (index % 5)

def round (state : State) (constant : Nat) : State :=
  (List.range 25).map fun index =>
    let x := index % 5
    let y := index / 5
    let value := (rotated state (source index)).bitXor
      (((rotated state (source (((x + 1) % 5) + 5 * y))).bitNot).bitAnd
        (rotated state (source (((x + 2) % 5) + 5 * y))))
    if index = 0 then value.bitXor (Word.ofNatModulo constant) else value

def permute (state : State) : State := constants.foldl round state

def paddedByte (words : MemorySemantics.Entries) (offset remaining : Word) (index : Nat) : Word :=
  if remaining > Word.ofNatModulo index then
    MemoryCopySemantics.readByte words (offset.add (Word.ofNatModulo index))
  else (if remaining == Word.ofNatModulo index then Word.ofNatModulo 1 else Word.zero).add
    (Word.ofNatModulo (if index = 135 then 128 else 0))

def readLane : Nat → Nat → MemorySemantics.Entries → Word → Word → Word → Word
  | 0, _, _, _, _, accumulator => accumulator
  | count + 1, index, words, offset, remaining, accumulator =>
      readLane count (index + 1) words offset remaining
        (accumulator.bitOr ((paddedByte words offset remaining index).shiftLeft (Word.ofNatModulo (8 * (index % 8)))))

def absorbBlock (words : MemorySemantics.Entries) (offset remaining : Word) (state : State) : State :=
  (List.range 25).map fun index =>
    if index < 17 then (lane state index).bitXor (readLane 8 (8 * index) words offset remaining Word.zero)
    else lane state index

def digest (state : State) : Word :=
  (List.range 32).foldl (fun output index => output.bitOr
    ((Word.byteAt (Word.ofNatModulo (31 - index % 8)) (lane state (index / 8))).shiftLeft
      (Word.ofNatModulo (8 * (31 - index))))) Word.zero

inductive Absorb (words : MemorySemantics.Entries) : Word → Word → State → Word → Prop where
  | last (offset remaining : Word) (state : State)
      (short : Word.ofNatModulo 136 > remaining) :
      Absorb words offset remaining state (digest (permute (absorbBlock words offset remaining state)))
  | more {offset remaining : Word} {state : State} {result : Word}
      (full : ¬Word.ofNatModulo 136 > remaining)
      (rest : Absorb words (offset.add (Word.ofNatModulo 136)) (remaining.sub (Word.ofNatModulo 136))
        (permute (absorbBlock words offset remaining state)) result) :
      Absorb words offset remaining state result

inductive Hash (offset length : Word) : MemorySemantics.State → Semantics.Result Semantics.Value →
    MemorySemantics.State → Prop where
  | overflow {initial : MemorySemantics.State}
      (touched : MemorySemantics.touchSize? initial.size offset length = none) :
      Hash offset length initial MemorySemantics.overflow initial
  | done {initial : MemorySemantics.State} {size result : Word}
      (touched : MemorySemantics.touchSize? initial.size offset length = some size)
      (absorbed : Absorb initial.words offset length (List.replicate 25 Word.zero) result) :
      Hash offset length initial (.value (.word result)) {initial with size := size}

inductive Builtin : String → Ty → List Semantics.Value → MemorySemantics.State →
    Semantics.Result Semantics.Value → MemorySemantics.State → Prop where
  | hash {type : Ty} {offset length : Word} {initial final : MemorySemantics.State}
      {result : Semantics.Result Semantics.Value}
      (executed : Hash offset length initial result final) :
      Builtin "keccak256" type [.word offset, .word length] initial result final

end Solcore.Frontend.RustHull.KeccakSemantics
