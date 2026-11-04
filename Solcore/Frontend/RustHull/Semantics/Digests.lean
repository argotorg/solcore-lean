import Solcore.Frontend.RustHull.Semantics.Memory

/-!
# Hull digest semantics

Keccak-256, SHA-256 and RIPEMD-160 over source memory, each written from its published definition.
Main declarations: `KeccakSemantics.Hash`, `KeccakSemantics.Builtin`, `Sha256Semantics`,
`Ripemd160Semantics`.
-/

section
-- leanmerge: from Solcore.Frontend.RustHull.KeccakSemantics
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
end

section
-- leanmerge: from Solcore.Frontend.RustHull.Ripemd160Semantics
/-! Independent RIPEMD-160 over packed source memory, following the designers'
definition (Dobbertin, Bosselaers and Preneel; rmd160.txt). Each 32-bit word is
held in the low bits of a Word: complements stay within 32 bits and every sum
is reduced modulo 2^32. Message words and the bit length are little-endian.
Padding appends the byte 0x80, zero bytes and the 64-bit bit length, using a
second block when the marker leaves no room. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.Ripemd160Semantics
open Core

/-- The chaining words h0…h4, or the working words A…E of one line. -/
abbrev State := List Word

def lane (state : State) (index : Nat) : Word := state[index]?.getD Word.zero

def initial : State := [0x67452301, 0xefcdab89, 0x98badcfe, 0x10325476, 0xc3d2e1f0].map Word.ofNatModulo

def mask32 (value : Word) : Word := value.bitAnd (Word.ofNatModulo (2 ^ 32 - 1))

/-- Addition modulo 2^32, applied left to right. -/
def sum32 (values : List Word) : Word := mask32 (values.foldl Word.add (Word.ofNatModulo 0))

/-- NOT on a 32-bit word. -/
def not32 (value : Word) : Word := mask32 value.bitNot

/-- rol_n on a 32-bit word. -/
def rotateLeft (value : Word) (distance : Nat) : Word :=
  mask32 ((value.shiftLeft (Word.ofNatModulo distance)).bitOr (value.shiftRight (Word.ofNatModulo (32 - distance))))

/-- f(j, x, y, z) for the sixteen-step round `round = j / 16`. -/
def nonlinear : Nat → Word → Word → Word → Word
  | 0, x, y, z => (x.bitXor y).bitXor z
  | 1, x, y, z => (x.bitAnd y).bitOr ((not32 x).bitAnd z)
  | 2, x, y, z => (x.bitOr (not32 y)).bitXor z
  | 3, x, y, z => (x.bitAnd z).bitOr (y.bitAnd (not32 z))
  | _, x, y, z => x.bitXor (y.bitOr (not32 z))

/-- K(j) and K'(j), one constant per sixteen-step round. -/
def leftConstants : List Nat := [0x00000000, 0x5a827999, 0x6ed9eba1, 0x8f1bbcdc, 0xa953fd4e]
def rightConstants : List Nat := [0x50a28be6, 0x5c4dd124, 0x6d703ef3, 0x7a6d76e9, 0x00000000]

/-- r(j) and r'(j): the message word selected by each step. -/
def leftWords : List Nat := [
  0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15,
  7, 4, 13, 1, 10, 6, 15, 3, 12, 0, 9, 5, 2, 14, 11, 8,
  3, 10, 14, 4, 9, 15, 8, 1, 2, 7, 0, 6, 13, 11, 5, 12,
  1, 9, 11, 10, 0, 8, 12, 4, 13, 3, 7, 15, 14, 5, 6, 2,
  4, 0, 5, 9, 7, 12, 2, 10, 14, 1, 3, 8, 11, 6, 15, 13]
def rightWords : List Nat := [
  5, 14, 7, 0, 9, 2, 11, 4, 13, 6, 15, 8, 1, 10, 3, 12,
  6, 11, 3, 7, 0, 13, 5, 10, 14, 15, 8, 12, 4, 9, 1, 2,
  15, 5, 1, 3, 7, 14, 6, 9, 11, 8, 12, 2, 10, 0, 4, 13,
  8, 6, 4, 1, 3, 11, 15, 0, 5, 12, 2, 13, 9, 7, 10, 14,
  12, 15, 10, 4, 1, 5, 8, 7, 6, 2, 13, 14, 0, 3, 9, 11]

/-- s(j) and s'(j): the left rotation of each step. -/
def leftRotations : List Nat := [
  11, 14, 15, 12, 5, 8, 7, 9, 11, 13, 14, 15, 6, 7, 9, 8,
  7, 6, 8, 13, 11, 9, 7, 15, 7, 12, 15, 9, 11, 7, 13, 12,
  11, 13, 6, 7, 14, 9, 13, 15, 14, 8, 13, 6, 5, 12, 7, 5,
  11, 12, 14, 15, 14, 15, 9, 8, 9, 14, 5, 6, 8, 6, 5, 12,
  9, 15, 5, 11, 6, 8, 13, 12, 5, 12, 13, 14, 11, 8, 5, 6]
def rightRotations : List Nat := [
  8, 9, 9, 11, 13, 15, 15, 5, 7, 7, 8, 11, 14, 14, 12, 6,
  9, 13, 15, 7, 12, 8, 9, 11, 7, 7, 12, 7, 6, 15, 13, 11,
  9, 7, 15, 11, 8, 6, 6, 14, 12, 13, 5, 14, 13, 13, 7, 5,
  15, 5, 8, 11, 14, 14, 6, 14, 6, 9, 12, 9, 12, 5, 15, 8,
  8, 5, 12, 9, 12, 5, 14, 6, 8, 13, 6, 5, 15, 13, 11, 11]

/-- T := rol_s(A + f(B, C, D) + X + K) + E; then A := E, E := D,
D := rol_10(C), C := B and B := T. -/
def step (round constant rotation : Nat) (state : State) (word : Word) : State :=
  let t := sum32 [rotateLeft (sum32 [lane state 0, nonlinear round (lane state 1) (lane state 2) (lane state 3),
    word, Word.ofNatModulo constant]) rotation, lane state 4]
  [lane state 4, t, lane state 1, rotateLeft (lane state 2) 10, lane state 3]

def messageWord (block : List Word) (index : Nat) : Word := block[index]?.getD Word.zero

/-- Step j of both lines. The right line uses f(79 - j, …). -/
def steps (block : List Word) (lines : State × State) (index : Nat) : State × State :=
  (step (index / 16) (leftConstants[index / 16]?.getD 0) (leftRotations[index]?.getD 0) lines.1
      (messageWord block (leftWords[index]?.getD 0)),
    step (4 - index / 16) (rightConstants[index / 16]?.getD 0) (rightRotations[index]?.getD 0) lines.2
      (messageWord block (rightWords[index]?.getD 0)))

/-- Eighty steps of both lines, then the final combination with the chaining
words: h0 := h1 + C + D', h1 := h2 + D + E', h2 := h3 + E + A',
h3 := h4 + A + B', h4 := h0 + B + C'. -/
def compress (state : State) (block : List Word) : State :=
  let lines := (List.range 80).foldl (steps block) (state, state)
  [sum32 [lane state 1, lane lines.1 2, lane lines.2 3], sum32 [lane state 2, lane lines.1 3, lane lines.2 4],
    sum32 [lane state 3, lane lines.1 4, lane lines.2 0], sum32 [lane state 4, lane lines.1 0, lane lines.2 1],
    sum32 [lane state 0, lane lines.1 1, lane lines.2 2]]

/-- The 64-bit little-endian bit length occupies the last eight bytes of the
final block; the marker byte follows the message once. -/
def paddedByte (words : MemorySemantics.Entries) (offset remaining bits : Word) (markerUsed : Bool)
    (index : Nat) : Word :=
  if remaining > Word.ofNatModulo index then
    MemoryCopySemantics.readByte words (offset.add (Word.ofNatModulo index))
  else if (if remaining == Word.ofNatModulo index then !markerUsed else false) then Word.ofNatModulo 128
  else if index < 56 then Word.ofNatModulo 0
  else if Word.ofNatModulo 56 > remaining then (Word.ofNatModulo (31 - (index - 56))).byteAt bits
  else Word.ofNatModulo 0

/-- Four padded bytes form one little-endian message word. -/
def readWord (words : MemorySemantics.Entries) (offset remaining bits : Word) (markerUsed : Bool) :
    Nat → Nat → Word → Word
  | 0, _, accumulator => accumulator
  | count + 1, index, accumulator =>
      readWord words offset remaining bits markerUsed count (index + 1)
        (accumulator.bitOr ((paddedByte words offset remaining bits markerUsed index).shiftLeft
          (Word.ofNatModulo (8 * (index % 4)))))

def readBlock (words : MemorySemantics.Entries) (offset remaining bits : Word) (markerUsed : Bool) : List Word :=
  (List.range 16).map fun index =>
    readWord words offset remaining bits markerUsed 4 (4 * index) (Word.ofNatModulo 0)

/-- The twenty digest bytes h0…h4, each word little-endian, in the low 160 bits. -/
def digest (state : State) : Word :=
  (List.range 20).foldl (fun result index => (result.shiftLeft (Word.ofNatModulo 8)).bitOr
    ((Word.ofNatModulo (31 - index % 4)).byteAt (lane state (index / 4)))) (Word.ofNatModulo 0)

def bitLength (length : Word) : Word :=
  (length.mul (Word.ofNatModulo 8)).bitAnd (Word.ofNatModulo (2 ^ 64 - 1))

/-- Full blocks are compressed in order. A final short block holds the marker
and, when at most 55 message bytes remain, the bit length; otherwise one more
block holds the zero padding and the bit length. -/
inductive Absorb (words : MemorySemantics.Entries) (bits : Word) :
    Word → Word → State → Bool → Word → Prop where
  | last {offset remaining : Word} {state : State} {markerUsed : Bool}
      (short : ¬remaining > Word.ofNatModulo 63) (fits : ¬remaining > Word.ofNatModulo 55) :
      Absorb words bits offset remaining state markerUsed
        (digest (compress state (readBlock words offset remaining bits markerUsed)))
  | spill {offset remaining : Word} {state : State} {markerUsed : Bool} {result : Word}
      (short : ¬remaining > Word.ofNatModulo 63) (spills : remaining > Word.ofNatModulo 55)
      (rest : Absorb words bits offset (Word.ofNatModulo 0)
        (compress state (readBlock words offset remaining bits markerUsed)) true result) :
      Absorb words bits offset remaining state markerUsed result
  | more {offset remaining : Word} {state : State} {markerUsed : Bool} {result : Word}
      (full : remaining > Word.ofNatModulo 63)
      (rest : Absorb words bits (offset.add (Word.ofNatModulo 64)) (remaining.sub (Word.ofNatModulo 64))
        (compress state (readBlock words offset remaining bits markerUsed)) false result) :
      Absorb words bits offset remaining state markerUsed result

/-- The digest of `length` bytes of `words` starting at `offset`. -/
abbrev Digest (words : MemorySemantics.Entries) (offset length result : Word) : Prop :=
  Absorb words (bitLength length) offset length initial false result

end Solcore.Frontend.RustHull.Ripemd160Semantics
end

section
-- leanmerge: from Solcore.Frontend.RustHull.Sha256Semantics
/-! Independent SHA-256 over packed source memory, following FIPS 180-4,
sections 4.1.2, 4.2.2, 5.1.1, 5.3.3 and 6.2. Each 32-bit quantity is held in
the low bits of a Word and every sum is reduced modulo 2^32. Message words are
big-endian. Padding appends the byte 0x80, zero bytes and the 64-bit
big-endian bit length, using a second block when the marker leaves no room. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.Sha256Semantics
open Core

abbrev State := List Word

def lane (state : State) (index : Nat) : Word := state[index]?.getD Word.zero

def initial : State := [0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a,
  0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19].map Word.ofNatModulo

def constants : List Nat := [
  0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
  0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
  0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
  0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
  0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
  0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
  0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
  0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2]

def mask32 (value : Word) : Word := value.bitAnd (Word.ofNatModulo (2 ^ 32 - 1))

/-- Addition modulo 2^32, applied left to right. -/
def sum32 (values : List Word) : Word := mask32 (values.foldl Word.add (Word.ofNatModulo 0))

/-- ROTL^n on a 32-bit value; ROTR^n is ROTL^(32 - n). -/
def rotateLeft (value : Word) (distance : Nat) : Word :=
  mask32 ((value.shiftLeft (Word.ofNatModulo distance)).bitOr (value.shiftRight (Word.ofNatModulo (32 - distance))))

def rotateRight (value : Word) (distance : Nat) : Word := rotateLeft value (32 - distance)

def xor3 (first second third : Word) : Word := (first.bitXor second).bitXor third

/-- σ₀, σ₁, Σ₀ and Σ₁ of section 4.1.2. -/
def small0 (value : Word) : Word :=
  xor3 (rotateRight value 7) (rotateRight value 18) (value.shiftRight (Word.ofNatModulo 3))
def small1 (value : Word) : Word :=
  xor3 (rotateRight value 17) (rotateRight value 19) (value.shiftRight (Word.ofNatModulo 10))
def large0 (value : Word) : Word := xor3 (rotateRight value 2) (rotateRight value 13) (rotateRight value 22)
def large1 (value : Word) : Word := xor3 (rotateRight value 6) (rotateRight value 11) (rotateRight value 25)

/-- Ch and Maj of section 4.1.2. -/
def choose (x y z : Word) : Word := (x.bitAnd y).bitXor (x.bitNot.bitAnd z)
def majority (x y z : Word) : Word := xor3 (x.bitAnd y) (x.bitAnd z) (y.bitAnd z)

/-- One step of section 6.2.2, part 3, for message word W(t) and constant K(t). -/
def round (state : State) (word : Word) (constant : Nat) : State :=
  let t1 := sum32 [lane state 7, large1 (lane state 4), choose (lane state 4) (lane state 5) (lane state 6),
    Word.ofNatModulo constant, word]
  let t2 := sum32 [large0 (lane state 0), majority (lane state 0) (lane state 1) (lane state 2)]
  [sum32 [t1, t2], lane state 0, lane state 1, lane state 2, sum32 [lane state 3, t1],
    lane state 4, lane state 5, lane state 6]

/-- Extend a schedule held newest first: W(t) = σ₁(W(t-2)) + W(t-7) +
σ₀(W(t-15)) + W(t-16). -/
def extend : Nat → List Word → List Word
  | 0, recent => recent
  | count + 1, recent =>
      extend count (sum32 [small1 (recent[1]?.getD Word.zero), recent[6]?.getD Word.zero,
        small0 (recent[14]?.getD Word.zero), recent[15]?.getD Word.zero] :: recent)

/-- The 64 message-schedule words W(0)…W(63) of a sixteen-word block. -/
def schedule (block : List Word) : List Word := (extend 48 block.reverse).reverse

/-- Section 6.2.2, parts 2 to 4: the rounds and the final chaining addition. -/
def compress (state : State) (block : List Word) : State :=
  let final := ((schedule block).zip constants).foldl (fun current (word, constant) => round current word constant) state
  (List.range 8).map fun index => sum32 [lane state index, lane final index]

/-- The 64-bit big-endian bit length occupies the last eight bytes of the final
block; the marker byte follows the message once. -/
def paddedByte (words : MemorySemantics.Entries) (offset remaining bits : Word) (markerUsed : Bool)
    (index : Nat) : Word :=
  if remaining > Word.ofNatModulo index then
    MemoryCopySemantics.readByte words (offset.add (Word.ofNatModulo index))
  else if (if remaining == Word.ofNatModulo index then !markerUsed else false) then Word.ofNatModulo 128
  else if index < 56 then Word.ofNatModulo 0
  else if Word.ofNatModulo 56 > remaining then (Word.ofNatModulo (24 + (index - 56))).byteAt bits
  else Word.ofNatModulo 0

/-- Four padded bytes form one big-endian message word. -/
def readWord (words : MemorySemantics.Entries) (offset remaining bits : Word) (markerUsed : Bool) :
    Nat → Nat → Word → Word
  | 0, _, accumulator => accumulator
  | count + 1, index, accumulator =>
      readWord words offset remaining bits markerUsed count (index + 1)
        (accumulator.bitOr ((paddedByte words offset remaining bits markerUsed index).shiftLeft
          (Word.ofNatModulo (8 * (3 - index % 4)))))

def readBlock (words : MemorySemantics.Entries) (offset remaining bits : Word) (markerUsed : Bool) : List Word :=
  (List.range 16).map fun index =>
    readWord words offset remaining bits markerUsed 4 (4 * index) (Word.ofNatModulo 0)

/-- The eight chaining words, concatenated big-endian. -/
def digest (state : State) : Word :=
  (List.range 8).foldl (fun result index => (result.shiftLeft (Word.ofNatModulo 32)).bitOr (lane state index))
    (Word.ofNatModulo 0)

def bitLength (length : Word) : Word :=
  (length.mul (Word.ofNatModulo 8)).bitAnd (Word.ofNatModulo (2 ^ 64 - 1))

/-- Full blocks are compressed in order. A final short block holds the marker
and, when at most 55 message bytes remain, the bit length; otherwise one more
block holds the zero padding and the bit length. -/
inductive Absorb (words : MemorySemantics.Entries) (bits : Word) :
    Word → Word → State → Bool → Word → Prop where
  | last {offset remaining : Word} {state : State} {markerUsed : Bool}
      (short : ¬remaining > Word.ofNatModulo 63) (fits : ¬remaining > Word.ofNatModulo 55) :
      Absorb words bits offset remaining state markerUsed
        (digest (compress state (readBlock words offset remaining bits markerUsed)))
  | spill {offset remaining : Word} {state : State} {markerUsed : Bool} {result : Word}
      (short : ¬remaining > Word.ofNatModulo 63) (spills : remaining > Word.ofNatModulo 55)
      (rest : Absorb words bits offset (Word.ofNatModulo 0)
        (compress state (readBlock words offset remaining bits markerUsed)) true result) :
      Absorb words bits offset remaining state markerUsed result
  | more {offset remaining : Word} {state : State} {markerUsed : Bool} {result : Word}
      (full : remaining > Word.ofNatModulo 63)
      (rest : Absorb words bits (offset.add (Word.ofNatModulo 64)) (remaining.sub (Word.ofNatModulo 64))
        (compress state (readBlock words offset remaining bits markerUsed)) false result) :
      Absorb words bits offset remaining state markerUsed result

/-- The digest of `length` bytes of `words` starting at `offset`. -/
abbrev Digest (words : MemorySemantics.Entries) (offset length result : Word) : Prop :=
  Absorb words (bitLength length) offset length initial false result

end Solcore.Frontend.RustHull.Sha256Semantics
end
