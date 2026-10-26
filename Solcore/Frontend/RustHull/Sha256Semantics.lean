import Solcore.Frontend.RustHull.MemoryCopySemantics

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
