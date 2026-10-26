import Solcore.Frontend.RustHull.MemoryCopySemantics

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
