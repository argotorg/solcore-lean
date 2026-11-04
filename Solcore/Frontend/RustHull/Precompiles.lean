import Solcore.Frontend.RustHull.Memory

/-!
# Digests and precompiles on Core

Keccak-256, SHA-256, RIPEMD-160, secp256k1 and P-256 compiled to ordinary Core, and the static
precompile dispatch. Main declarations: `Keccak.hash`, `Sha256.hash`, `Ripemd160.hash`,
`Precompiles.staticCall`.
-/

section
-- leanmerge: from Solcore.Frontend.RustHull.HashBlocks
/-! Core block streaming shared by SHA-256 and RIPEMD-160. Input stays in packed
memory; the marker, zero padding and 64-bit bit count are generated in Core. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.HashBlocks
open Core

def number (value : Nat) : Expr := .word (Word.ofNatModulo value)
def add (left right : Expr) : Expr := .binary .wordAdd left right
def xor (left right : Expr) : Expr := .binary .wordXor left right
def shift (value : Expr) (distance : Nat) : Expr := .binary .wordShl value (number distance)
def move (expression : Expr) (depth : Nat) : Expr := expression.rename fun index => index + depth
def mask32 (value : Expr) : Expr := .binary .wordAnd value (number (2 ^ 32 - 1))
def sum32 (values : List Expr) : Expr := mask32 (values.foldl add (number 0))
def rotateLeft (value : Expr) (distance : Nat) : Expr :=
  mask32 (.binary .wordOr (shift value distance) (.binary .wordShr value (number (32 - distance))))
def rotateRight (value : Expr) (distance : Nat) : Expr := rotateLeft value (32 - distance)

def packet : List Expr → Expr
  | [] => .unit
  | [value] => value
  | value :: rest => .pair value (packet rest)
def types : List Ty → Ty
  | [] => .unit
  | [type] => type
  | type :: rest => .product type (types rest)
def field (index : Nat) : Nat → Expr → Expr
  | 0, _ => .unit
  | 1, value => value
  | count + 2, value => if index = 0 then .first value
      else field (index - 1) (count + 1) (.second value)

def blockType : Ty := types (List.replicate 16 .word)

structure Algorithm where
  stateType : Ty
  initial : Expr
  compress : Expr → Expr → Expr
  digest : Expr → Expr
  littleEndian : Bool

private def paddedByte (littleEndian : Bool) (mapping offset remaining bits markerUsed : Expr)
    (index : Nat) : Expr :=
  .ifE (.binary .wordGt remaining (number index))
    (Memory.readMemoryByte mapping (add offset (number index)))
    (LanguageResult.success
      (.ifE (.ifE (.binary .wordEq remaining (number index)) (.unary .boolNot markerUsed) (.bool false))
        (number 128)
        (if index < 56 then number 0
          else .ifE (.binary .wordGt (number 56) remaining)
            (.binary .wordByte (number (if littleEndian then 31 - (index - 56) else 24 + (index - 56))) bits)
            (number 0))))

private def readWord (littleEndian : Bool) : Nat → Nat → Expr → Expr → Expr → Expr → Expr → Expr → Expr
  | 0, _, _, _, _, _, _, accumulator => LanguageResult.success accumulator
  | count + 1, index, mapping, offset, remaining, bits, markerUsed, accumulator =>
      LanguageResult.bind .word (paddedByte littleEndian mapping offset remaining bits markerUsed index)
        (readWord littleEndian count (index + 1) (mapping.weakenAt 0) (offset.weakenAt 0)
          (remaining.weakenAt 0) (bits.weakenAt 0) (markerUsed.weakenAt 0)
          (.binary .wordOr (accumulator.weakenAt 0)
            (shift (.var 0) (8 * (if littleEndian then index % 4 else 3 - index % 4)))))

private def readBlock (littleEndian : Bool) (parameters : Expr) : Expr :=
  let computations := (List.range 16).map fun index =>
    let params := move parameters index
    readWord littleEndian 4 (4 * index) (field 0 6 params) (field 1 6 params)
      (field 2 6 params) (field 3 6 params) (field 5 6 params) (number 0)
  computations.foldr (LanguageResult.bind blockType)
    (LanguageResult.success (packet ((List.range 16).map fun index => .var (15 - index))))

private def parameterType (algorithm : Algorithm) : Ty :=
  types [WordMapping.type, .word, .word, .word, algorithm.stateType, .bool]

private def absorbBody (algorithm : Algorithm) : Expr :=
  LanguageResult.bind .word (readBlock algorithm.littleEndian (.var 0))
    (.letE (algorithm.compress (field 4 6 (.var 1)) (.var 0))
      (let params := Expr.var 2
       let next := fun offset remaining marker =>
         WordMapping.invoke (parameterType algorithm) .word (.var 3)
           (packet [field 0 6 params, offset, remaining, field 3 6 params, .var 0, marker])
       .ifE (.binary .wordGt (field 2 6 params) (number 63))
         (next (add (field 1 6 params) (number 64))
           (.binary .wordSub (field 2 6 params) (number 64)) (.bool false))
         (.ifE (.binary .wordGt (field 2 6 params) (number 55))
           (next (field 1 6 params) (number 0) (.bool true))
           (LanguageResult.success (algorithm.digest (.var 0))))))

/-- Digest bytes are returned in a Word, with zero high bits for shorter hashes.
Only input bytes expand memory; padding never changes user memory. -/
def hash (algorithm : Algorithm) (memoryReference sizeReference offset length : Expr) : Expr :=
  .letE (packet [memoryReference, sizeReference, offset, length])
    (LanguageResult.bind .word
      (Memory.touch (field 1 4 (.var 0)) (field 2 4 (.var 0)) (field 3 4 (.var 0)))
      (WordMapping.runHelper (parameterType algorithm) .word (absorbBody algorithm)
        (packet [.loadCell (field 0 4 (.var 1)), field 2 4 (.var 1), field 3 4 (.var 1),
          .binary .wordAnd (.binary .wordMul (field 3 4 (.var 1)) (number 8)) (number (2 ^ 64 - 1)),
          algorithm.initial, .bool false])))

end Solcore.Frontend.RustHull.HashBlocks
end

section
-- leanmerge: from Solcore.Frontend.RustHull.Keccak
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
end

section
-- leanmerge: from Solcore.Frontend.RustHull.Secp256k1
/-! secp256k1 recovery compiled to ordinary Core operations. Domain parameters
follow SEC 2 v2 §2.4.1. Jacobian formulas follow the Explicit-Formulas Database
(madd-2004-hmv and dbl-2009-l); zero-Z denotes infinity. Ethereum recovery
conditions follow execution-specs' ecrecover precompile. No host cryptographic
operation participates in evaluation.

References:
https://www.secg.org/sec2-v2.pdf
https://www.hyperelliptic.org/EFD/g1p/auto-shortw-jacobian-0.html
https://github.com/ethereum/execution-specs/blob/forks/amsterdam/src/ethereum/forks/cancun/vm/precompiled_contracts/ecrecover.py
-/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.Secp256k1
open Core

def prime : Nat := 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffc2f
def order : Nat := 0xfffffffffffffffffffffffffffffffebaaedce6af48a03bbfd25e8cd0364141
def generatorX : Nat := 0x79be667ef9dcbbac55a06295ce870b07029bfcdb2dce28d959f2815b16f81798
def generatorY : Nat := 0x483ada7726a3c4655da4fbfc0e1108a8fd17b448a68554199c47d08ffb10d4b8

def pointType : Ty := .product .word (.product .word .word)
def affineType : Ty := .product .word .word
def optionType (type : Ty) : Ty := .sum .unit type

private def packet : List Expr → Expr
  | [] => .unit
  | [value] => value
  | value :: rest => .pair value (packet rest)
private def types : List Ty → Ty
  | [] => .unit
  | [type] => type
  | type :: rest => .product type (types rest)
private def field (index : Nat) : Nat → Expr → Expr
  | 0, _ => .unit
  | 1, value => value
  | count + 2, value => if index = 0 then .first value
      else field (index - 1) (count + 1) (.second value)

/-- Construction-time binder levels keep captured Core variables stable as
arithmetic temporaries are introduced. This is only an expression builder. -/
private abbrev Code := Nat → Expr
private def number (value : Nat) : Code := fun _ => .word (Word.ofNatModulo value)
private def arg : Code := fun depth => .var depth
private def self : Code := fun depth => .var (depth + 1)
private def bind (value : Code) (body : Code → Code) : Code := fun depth =>
  .letE (value depth) (body (fun here => .var (here - depth - 1)) (depth + 1))
private def bindResult (type : Ty) (value : Code) (body : Code → Code) : Code := fun depth =>
  LanguageResult.bind type (value depth)
    (body (fun here => .var (here - depth - 1)) (depth + 1))
private def success (value : Code) : Code := fun depth => LanguageResult.success (value depth)
private def noneC (type : Ty) : Code := fun _ => .inLeft type .unit
private def someC (value : Code) : Code := fun depth => .inRight .unit (value depth)
private def tuple (values : List Code) : Code := fun depth => packet (values.map (· depth))
private def part (index count : Nat) (value : Code) : Code := fun depth => field index count (value depth)
private def binary (op : BinaryOp) (a b : Code) : Code := fun depth => .binary op (a depth) (b depth)
private def eq (a b : Code) : Code := binary .wordEq a b
private def gt (a b : Code) : Code := binary .wordGt a b
private def choose (test yes no : Code) : Code := fun depth => .ifE (test depth) (yes depth) (no depth)
private def mulMod (a b modulus : Code) : Code := fun depth => .ternary .wordMulMod (a depth) (b depth) (modulus depth)
private def addMod (a b modulus : Code) : Code := fun depth => .ternary .wordAddMod (a depth) (b depth) (modulus depth)
private def fmul (a b : Code) : Code := mulMod a b (number prime)
private def fadd (a b : Code) : Code := addMod a b (number prime)
private def fsub (a b : Code) : Code := fadd a (binary .wordSub (number prime) b)
private def square (a : Code) : Code := fmul a a
private def point (x y z : Code) : Code := tuple [x, y, z]
private def infinity : Code := point (number 0) (number 1) (number 0)

private def powParameter : Ty := types [.word, .word, .word, .word]
private def powBody : Expr :=
  let acc := part 0 4 arg
  let base := part 1 4 arg
  let exponent := part 2 4 arg
  let modulus := part 3 4 arg
  (choose (eq exponent (number 0)) (success acc)
    (fun depth => WordMapping.invoke powParameter .word (self depth)
      (tuple [choose (eq (binary .wordAnd exponent (number 1)) (number 0)) acc
          (mulMod acc base modulus),
        mulMod base base modulus, binary .wordShr exponent (number 1), modulus] depth))) 0

/-- Resumable repeated squaring with unrestricted 256-bit operands. -/
def powMod (base exponent modulus : Expr) : Expr :=
  .letE (packet [base, exponent, modulus])
    (WordMapping.runHelper powParameter .word powBody
      (packet [.binary .wordMod (.word (Word.ofNatModulo 1)) (field 2 3 (.var 0)),
        .binary .wordMod (field 0 3 (.var 0)) (field 2 3 (.var 0)),
        field 1 3 (.var 0), field 2 3 (.var 0)]))

private def pow (base exponent modulus : Code) : Code := fun depth =>
  powMod (base depth) (exponent depth) (modulus depth)

private def doubleCode (value : Code) : Code :=
  let x := part 0 3 value
  let y := part 1 3 value
  let z := part 2 3 value
  choose (eq z (number 0)) infinity <|
  choose (eq y (number 0)) infinity <|
  bind (square x) fun a =>
  bind (square y) fun b =>
  bind (square b) fun c =>
  bind (fmul (number 2) (fsub (fsub (square (fadd x b)) a) c)) fun d =>
  bind (fmul (number 3) a) fun e =>
  bind (fsub (square e) (fmul (number 2) d)) fun outX =>
  point outX (fsub (fmul e (fsub d outX)) (fmul (number 8) c)) (fmul (number 2) (fmul y z))

/-- Double a Jacobian point (X,Y,Z), treating zero Z as infinity. -/
def doublePoint (value : Expr) : Expr := .letE value (doubleCode arg 0)

private def mixedCode (value affine : Code) : Code :=
  let x := part 0 3 value
  let y := part 1 3 value
  let z := part 2 3 value
  let qx := part 0 2 affine
  let qy := part 1 2 affine
  choose (eq z (number 0)) (point qx qy (number 1)) <|
  bind (square z) fun zz =>
  bind (fsub (fmul qx zz) x) fun h =>
  bind (fsub (fmul qy (fmul z zz)) y) fun delta =>
  choose (eq h (number 0))
    (choose (eq delta (number 0)) (doubleCode value) infinity) <|
  bind (square h) fun hh =>
  bind (fmul h hh) fun hhh =>
  bind (fmul x hh) fun v =>
  bind (fsub (fsub (square delta) hhh) (fmul (number 2) v)) fun outX =>
  point outX (fsub (fmul delta (fsub v outX)) (fmul y hhh)) (fmul z h)

/-- Add a finite affine point to a Jacobian point, including equal/opposite points. -/
def addAffine (value affine : Expr) : Expr :=
  .letE (.pair value affine) (mixedCode (part 0 2 arg) (part 1 2 arg) 0)

private def jointParameter : Ty := types [pointType, affineType, affineType, .word, .word, .word]
private def jointBody : Expr :=
  let current := part 0 6 arg
  let first := part 1 6 arg
  let second := part 2 6 arg
  let a := part 3 6 arg
  let b := part 4 6 arg
  let remaining := part 5 6 arg
  (choose (eq remaining (number 0)) (success current) <|
    bind (binary .wordSub remaining (number 1)) fun bit =>
    bind (doubleCode current) fun doubled =>
    bind (choose (eq (binary .wordAnd (binary .wordShr a bit) (number 1)) (number 0))
      doubled (mixedCode doubled first)) fun updated =>
    bind (choose (eq (binary .wordAnd (binary .wordShr b bit) (number 1)) (number 0))
      updated (mixedCode updated second)) fun finalPoint =>
    fun depth => WordMapping.invoke jointParameter pointType (self depth)
      (tuple [finalPoint, first, second, a, b, bit] depth)) 0

/-- Compute a*P + b*Q with 256 resumable double/add rounds. Inputs P and Q are
finite affine curve points. The result remains in Jacobian coordinates. -/
def jointMultiply (first second a b : Expr) : Expr :=
  WordMapping.runHelper jointParameter pointType jointBody
    (packet [infinity 0, first, second, a, b, number 256 0])

private def normalizeCode (value : Code) : Code :=
  choose (eq (part 2 3 value) (number 0)) (success (noneC affineType)) <|
    bindResult (optionType affineType) (pow (part 2 3 value) (number (prime - 2)) (number prime)) fun inverse =>
    bind (square inverse) fun squared =>
    success (someC (tuple [fmul (part 0 3 value) squared,
      fmul (part 1 3 value) (fmul squared inverse)]))

/-- Convert a Jacobian result to affine coordinates or report infinity. -/
def normalize (value : Expr) : Expr := .letE value (normalizeCode arg 0)

private def recoverCode : Code :=
  let hash := part 0 4 arg
  let v := part 1 4 arg
  let r := part 2 4 arg
  let s := part 3 4 arg
  let absent := success (noneC affineType)
  let valid :=
    bind (fadd (fmul (square r) r) (number 7)) fun curve =>
    bindResult (optionType affineType) (pow curve (number ((prime + 1) / 4)) (number prime)) fun y =>
    choose (eq (square y) curve)
      (bind (choose (eq (binary .wordAnd y (number 1)) (binary .wordSub v (number 27)))
        y (fsub (number 0) y)) fun ry =>
       bindResult (optionType affineType) (pow r (number (order - 2)) (number order)) fun inverse =>
       bind (mulMod s inverse (number order)) fun a =>
       bind (mulMod (binary .wordSub (number order) (binary .wordMod hash (number order)))
         inverse (number order)) fun b =>
       bindResult (optionType affineType)
         (fun depth => jointMultiply (tuple [r, ry] depth)
           (tuple [number generatorX, number generatorY] depth) (a depth) (b depth)) fun result =>
       normalizeCode result)
      absent
  choose (eq v (number 27))
    (choose (eq r (number 0)) absent (choose (gt (number order) r)
      (choose (eq s (number 0)) absent (choose (gt (number order) s) valid absent)) absent))
    (choose (eq v (number 28))
      (choose (eq r (number 0)) absent (choose (gt (number order) r)
        (choose (eq s (number 0)) absent (choose (gt (number order) s) valid absent)) absent)) absent)

/-- Ethereum's recovery domain accepts high-s signatures; invalid inputs and
an infinite recovered point yield the inner `Unit` alternative. -/
def recoverPoint (hash v r s : Expr) : Expr :=
  .letE (packet [hash, v, r, s]) (recoverCode 0)

private def addressCode : Code :=
  bind (fun _ => .newCell WordMapping.type WordMapping.empty) fun memory =>
  bind (fun _ => .newCell .word (.word Word.zero)) fun size =>
  bindResult (optionType .word)
    (fun depth => Memory.mstore (memory depth) (size depth) (.word Word.zero) (part 0 2 arg depth)) fun _ =>
  bindResult (optionType .word)
    (fun depth => Memory.mstore (memory depth) (size depth) (number 32 depth) (part 1 2 arg depth)) fun _ =>
  bindResult (optionType .word)
    (fun depth => Keccak.hash (memory depth) (size depth) (number 0 depth) (number 64 depth)) fun digest =>
  success (someC (binary .wordAnd digest (number (2 ^ 160 - 1))))

/-- Recover the 160-bit Ethereum address. The outer LanguageResult carries
execution failures; the inner Unit + Word distinguishes empty output from a
successfully recovered address, including address zero. Scratch memory is private. -/
def recover (hash v r s : Expr) : Expr :=
  LanguageResult.bind (optionType .word) (recoverPoint hash v r s)
    (.caseE (.var 0) (LanguageResult.success (.inLeft .word .unit)) (addressCode 0))

end Solcore.Frontend.RustHull.Secp256k1
end

section
-- leanmerge: from Solcore.Frontend.RustHull.P256
/-! EIP-7951 P-256 signature verification using existing Core operations.
The only shared arithmetic helper is secp256k1's modulus-parameterized power
loop. This curve uses a=-3, so its doubling law is separate from secp256k1.

Domain parameters and validation: https://eips.ethereum.org/EIPS/eip-7951
Jacobian formulas (dbl-2001-b and madd-2004-hmv):
https://www.hyperelliptic.org/EFD/g1p/auto-shortw-jacobian-3.html
-/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.P256
open Core

def prime : Nat := 0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff
def order : Nat := 0xffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632551
def coefficientB : Nat := 0x5ac635d8aa3a93e7b3ebbd55769886bc651d06b0cc53b0f63bce3c3e27d2604b
def generatorX : Nat := 0x6b17d1f2e12c4247f8bce6e563a440f277037d812deb33a0f4a13945d898c296
def generatorY : Nat := 0x4fe342e2fe1a7f9b8ee7eb4a7c0f9e162bce33576b315ececbb6406837bf51f5
def pointType : Ty := .product .word (.product .word .word)
def affineType : Ty := .product .word .word
def optionType (type : Ty) : Ty := .sum .unit type

private def packet : List Expr → Expr
  | [] => .unit
  | [value] => value
  | value :: rest => .pair value (packet rest)
private def types : List Ty → Ty
  | [] => .unit
  | [type] => type
  | type :: rest => .product type (types rest)
private def field (index : Nat) : Nat → Expr → Expr
  | 0, _ => .unit
  | 1, value => value
  | count + 2, value => if index = 0 then .first value
      else field (index - 1) (count + 1) (.second value)

private abbrev Code := Nat → Expr
private def number (value : Nat) : Code := fun _ => .word (Word.ofNatModulo value)
private def boolean (value : Bool) : Code := fun _ => .bool value
private def arg : Code := fun depth => .var depth
private def self : Code := fun depth => .var (depth + 1)
private def bind (value : Code) (body : Code → Code) : Code := fun depth =>
  .letE (value depth) (body (fun here => .var (here - depth - 1)) (depth + 1))
private def bindResult (type : Ty) (value : Code) (body : Code → Code) : Code := fun depth =>
  LanguageResult.bind type (value depth)
    (body (fun here => .var (here - depth - 1)) (depth + 1))
private def success (value : Code) : Code := fun depth => LanguageResult.success (value depth)
private def noneC (type : Ty) : Code := fun _ => .inLeft type .unit
private def someC (value : Code) : Code := fun depth => .inRight .unit (value depth)
private def tuple (values : List Code) : Code := fun depth => packet (values.map (· depth))
private def part (index count : Nat) (value : Code) : Code := fun depth => field index count (value depth)
private def binary (op : BinaryOp) (a b : Code) : Code := fun depth => .binary op (a depth) (b depth)
private def eq (a b : Code) : Code := binary .wordEq a b
private def lt (a b : Code) : Code := binary .wordGt b a
private def choose (test yes no : Code) : Code := fun depth => .ifE (test depth) (yes depth) (no depth)
private def mulMod (a b modulus : Code) : Code := fun depth => .ternary .wordMulMod (a depth) (b depth) (modulus depth)
private def addMod (a b modulus : Code) : Code := fun depth => .ternary .wordAddMod (a depth) (b depth) (modulus depth)
private def fmul (a b : Code) : Code := mulMod a b (number prime)
private def fadd (a b : Code) : Code := addMod a b (number prime)
private def fsub (a b : Code) : Code := fadd a (binary .wordSub (number prime) b)
private def square (a : Code) : Code := fmul a a
private def point (x y z : Code) : Code := tuple [x, y, z]
private def infinity : Code := point (number 0) (number 1) (number 0)
private def pow (base exponent modulus : Code) : Code := fun depth =>
  Secp256k1.powMod (base depth) (exponent depth) (modulus depth)

private def doubleCode (value : Code) : Code :=
  let x := part 0 3 value
  let y := part 1 3 value
  let z := part 2 3 value
  choose (eq z (number 0)) infinity <|
  choose (eq y (number 0)) infinity <|
  bind (square z) fun delta =>
  bind (square y) fun gamma =>
  bind (fmul x gamma) fun beta =>
  bind (fmul (number 3) (fmul (fsub x delta) (fadd x delta))) fun alpha =>
  bind (fsub (square alpha) (fmul (number 8) beta)) fun outX =>
  point outX (fsub (fmul alpha (fsub (fmul (number 4) beta) outX))
    (fmul (number 8) (square gamma))) (fsub (fsub (square (fadd y z)) gamma) delta)

def doublePoint (value : Expr) : Expr := .letE value (doubleCode arg 0)

private def mixedCode (value affine : Code) : Code :=
  let x := part 0 3 value
  let y := part 1 3 value
  let z := part 2 3 value
  let qx := part 0 2 affine
  let qy := part 1 2 affine
  choose (eq z (number 0)) (point qx qy (number 1)) <|
  bind (square z) fun zz =>
  bind (fsub (fmul qx zz) x) fun h =>
  bind (fsub (fmul qy (fmul z zz)) y) fun delta =>
  choose (eq h (number 0))
    (choose (eq delta (number 0)) (doubleCode value) infinity) <|
  bind (square h) fun hh =>
  bind (fmul h hh) fun hhh =>
  bind (fmul x hh) fun v =>
  bind (fsub (fsub (square delta) hhh) (fmul (number 2) v)) fun outX =>
  point outX (fsub (fmul delta (fsub v outX)) (fmul y hhh)) (fmul z h)

def addAffine (value affine : Expr) : Expr :=
  .letE (.pair value affine) (mixedCode (part 0 2 arg) (part 1 2 arg) 0)

private def jointParameter : Ty := types [pointType, affineType, affineType, .word, .word, .word]
private def jointBody : Expr :=
  let current := part 0 6 arg
  let first := part 1 6 arg
  let second := part 2 6 arg
  let a := part 3 6 arg
  let b := part 4 6 arg
  let remaining := part 5 6 arg
  (choose (eq remaining (number 0)) (success current) <|
    bind (binary .wordSub remaining (number 1)) fun bit =>
    bind (doubleCode current) fun doubled =>
    bind (choose (eq (binary .wordAnd (binary .wordShr a bit) (number 1)) (number 0))
      doubled (mixedCode doubled first)) fun updated =>
    bind (choose (eq (binary .wordAnd (binary .wordShr b bit) (number 1)) (number 0))
      updated (mixedCode updated second)) fun finalPoint =>
    fun depth => WordMapping.invoke jointParameter pointType (self depth)
      (tuple [finalPoint, first, second, a, b, bit] depth)) 0

/-- A resumable 256-round joint multiplication. The two supplied affine points
must be finite points on P-256; `verify` validates the external public key. -/
def jointMultiply (first second a b : Expr) : Expr :=
  WordMapping.runHelper jointParameter pointType jointBody
    (packet [infinity 0, first, second, a, b, number 256 0])

private def normalizeCode (value : Code) : Code :=
  choose (eq (part 2 3 value) (number 0)) (success (noneC affineType)) <|
  bindResult (optionType affineType) (pow (part 2 3 value) (number (prime - 2)) (number prime)) fun inverse =>
  bind (square inverse) fun squared =>
  success (someC (tuple [fmul (part 0 3 value) squared,
    fmul (part 1 3 value) (fmul squared inverse)]))

def normalize (value : Expr) : Expr := .letE value (normalizeCode arg 0)

private def verifyCode : Code :=
  let hash := part 0 5 arg
  let r := part 1 5 arg
  let s := part 2 5 arg
  let qx := part 3 5 arg
  let qy := part 4 5 arg
  let invalid := success (boolean false)
  let calculate :=
    bindResult .bool (pow s (number (order - 2)) (number order)) fun inverse =>
    bindResult .bool (fun depth => jointMultiply
      (tuple [number generatorX, number generatorY] depth) (tuple [qx, qy] depth)
      (mulMod hash inverse (number order) depth) (mulMod r inverse (number order) depth)) fun result =>
    choose (eq (part 2 3 result) (number 0)) invalid <|
    bindResult .bool (pow (part 2 3 result) (number (prime - 2)) (number prime)) fun zInverse =>
    success (eq (binary .wordMod (fmul (part 0 3 result) (square zInverse)) (number order)) r)
  choose (lt (number 0) r)
    (choose (lt r (number order))
      (choose (lt (number 0) s)
        (choose (lt s (number order))
          (choose (lt qx (number prime))
            (choose (lt qy (number prime))
              (choose (choose (eq qx (number 0)) (eq qy (number 0)) (boolean false))
                invalid
                (choose (eq (square qy)
                  (fadd (fsub (fmul (square qx) qx) (fmul (number 3) qx)) (number coefficientB)))
                  calculate invalid)) invalid) invalid) invalid) invalid) invalid) invalid

/-- Verify the five decoded EIP-7951 words. Invalid points/signatures return
false. This explicitly rejects an infinite reconstructed point and compares
its affine x coordinate modulo the subgroup order. High-s signatures remain
valid, as required by EIP-7951. Input length and precompile gas are handled by
the surrounding call adapter. Every input expression is evaluated once. -/
def verify (hash r s publicX publicY : Expr) : Expr :=
  .letE (packet [hash, r, s, publicX, publicY]) (verifyCode 0)

end Solcore.Frontend.RustHull.P256
end

section
-- leanmerge: from Solcore.Frontend.RustHull.Ripemd160
/-! RIPEMD-160 compiled to ordinary Core, following the designers' specification:
https://homes.esat.kuleuven.be/~bosselae/ripemd/rmd160.txt. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.Ripemd160
open Core HashBlocks

def stateType : Ty := types (List.replicate 5 .word)
private def lane (index : Nat) (state : Expr) : Expr := field index 5 state
private def initial : Expr := packet ([0x67452301, 0xefcdab89, 0x98badcfe, 0x10325476, 0xc3d2e1f0].map number)
private def leftWords : List Nat := [
  0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15,
  7, 4, 13, 1, 10, 6, 15, 3, 12, 0, 9, 5, 2, 14, 11, 8,
  3, 10, 14, 4, 9, 15, 8, 1, 2, 7, 0, 6, 13, 11, 5, 12,
  1, 9, 11, 10, 0, 8, 12, 4, 13, 3, 7, 15, 14, 5, 6, 2,
  4, 0, 5, 9, 7, 12, 2, 10, 14, 1, 3, 8, 11, 6, 15, 13]
private def rightWords : List Nat := [
  5, 14, 7, 0, 9, 2, 11, 4, 13, 6, 15, 8, 1, 10, 3, 12,
  6, 11, 3, 7, 0, 13, 5, 10, 14, 15, 8, 12, 4, 9, 1, 2,
  15, 5, 1, 3, 7, 14, 6, 9, 11, 8, 12, 2, 10, 0, 4, 13,
  8, 6, 4, 1, 3, 11, 15, 0, 5, 12, 2, 13, 9, 7, 10, 14,
  12, 15, 10, 4, 1, 5, 8, 7, 6, 2, 13, 14, 0, 3, 9, 11]
private def leftRotations : List Nat := [
  11, 14, 15, 12, 5, 8, 7, 9, 11, 13, 14, 15, 6, 7, 9, 8,
  7, 6, 8, 13, 11, 9, 7, 15, 7, 12, 15, 9, 11, 7, 13, 12,
  11, 13, 6, 7, 14, 9, 13, 15, 14, 8, 13, 6, 5, 12, 7, 5,
  11, 12, 14, 15, 14, 15, 9, 8, 9, 14, 5, 6, 8, 6, 5, 12,
  9, 15, 5, 11, 6, 8, 13, 12, 5, 12, 13, 14, 11, 8, 5, 6]
private def rightRotations : List Nat := [
  8, 9, 9, 11, 13, 15, 15, 5, 7, 7, 8, 11, 14, 14, 12, 6,
  9, 13, 15, 7, 12, 8, 9, 11, 7, 7, 12, 7, 6, 15, 13, 11,
  9, 7, 15, 11, 8, 6, 6, 14, 12, 13, 5, 14, 13, 13, 7, 5,
  15, 5, 8, 11, 14, 14, 6, 14, 6, 9, 12, 9, 12, 5, 15, 8,
  8, 5, 12, 9, 12, 5, 14, 6, 8, 13, 6, 5, 15, 13, 11, 11]
private def leftConstants : List Nat := [0, 0x5a827999, 0x6ed9eba1, 0x8f1bbcdc, 0xa953fd4e]
private def rightConstants : List Nat := [0x50a28be6, 0x5c4dd124, 0x6d703ef3, 0x7a6d76e9, 0]

private def nonlinear (phase : Nat) (x y z : Expr) : Expr := match phase with
  | 0 => xor (xor x y) z
  | 1 => .binary .wordOr (.binary .wordAnd x y) (.binary .wordAnd (.unary .wordNot x) z)
  | 2 => xor (.binary .wordOr x (.unary .wordNot y)) z
  | 3 => .binary .wordOr (.binary .wordAnd x z) (.binary .wordAnd y (.unary .wordNot z))
  | _ => xor x (.binary .wordOr y (.unary .wordNot z))

private def step (phase constant rotation : Nat) (state message : Expr) : Expr :=
  let t := sum32 [rotateLeft (sum32 [lane 0 state,
    nonlinear phase (lane 1 state) (lane 2 state) (lane 3 state), message, number constant]) rotation,
    lane 4 state]
  let state := state.weakenAt 0
  .letE t (packet [lane 4 state, .var 0, lane 1 state, rotateLeft (lane 2 state) 10, lane 3 state])

/-- Compress a sixteen-word block using both eighty-step parallel lines. -/
def compress (state block : Expr) : Expr :=
  let rounds := (List.range 80).map fun index =>
    let message := Expr.second (.var (index + 1))
    .pair
      (step (index / 16) (leftConstants[index / 16]?.getD 0) (leftRotations[index]?.getD 0)
        (.first (.var 0)) (field (leftWords[index]?.getD 0) 16 message))
      (step (4 - index / 16) (rightConstants[index / 16]?.getD 0) (rightRotations[index]?.getD 0)
        (.second (.var 0)) (field (rightWords[index]?.getD 0) 16 message))
  let old := Expr.first (.var 81)
  let left := Expr.first (.var 0)
  let right := Expr.second (.var 0)
  let result := packet [sum32 [lane 1 old, lane 2 left, lane 3 right],
    sum32 [lane 2 old, lane 3 left, lane 4 right], sum32 [lane 3 old, lane 4 left, lane 0 right],
    sum32 [lane 4 old, lane 0 left, lane 1 right], sum32 [lane 0 old, lane 1 left, lane 2 right]]
  .letE (.pair state block)
    (.letE (.pair (.first (.var 0)) (.first (.var 0))) (rounds.foldr Expr.letE result))

private def digest (state : Expr) : Expr :=
  (List.range 20).foldl (fun result index =>
    .binary .wordOr (shift result 8)
      (.binary .wordByte (number (31 - index % 4)) (lane (index / 4) state))) (number 0)

/-- The 160-bit digest occupies the low bits, matching the EVM's 32-byte result. -/
def hash (memoryReference sizeReference offset length : Expr) : Expr :=
  HashBlocks.hash {stateType, initial, compress, digest, littleEndian := true}
    memoryReference sizeReference offset length

end Solcore.Frontend.RustHull.Ripemd160
end

section
-- leanmerge: from Solcore.Frontend.RustHull.Sha256
/-! SHA-256 expressed in ordinary Core using FIPS 180-4, sections 4.1.2,
4.2.2, 5.3.3 and 6.2: https://doi.org/10.6028/NIST.FIPS.180-4. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.Sha256
open Core HashBlocks

def stateType : Ty := types (List.replicate 8 .word)
private def lane (index : Nat) (state : Expr) : Expr := field index 8 state
private def initial : Expr := packet ([0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a,
  0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19].map number)
private def constants : List Nat := [
  0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
  0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
  0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
  0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
  0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
  0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
  0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
  0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2]

private def xor3 (a b c : Expr) : Expr := xor (xor a b) c
private def small0 (x : Expr) : Expr := xor3 (rotateRight x 7) (rotateRight x 18) (.binary .wordShr x (number 3))
private def small1 (x : Expr) : Expr := xor3 (rotateRight x 17) (rotateRight x 19) (.binary .wordShr x (number 10))
private def large0 (x : Expr) : Expr := xor3 (rotateRight x 2) (rotateRight x 13) (rotateRight x 22)
private def large1 (x : Expr) : Expr := xor3 (rotateRight x 6) (rotateRight x 11) (rotateRight x 25)
private def choose (x y z : Expr) : Expr := xor (.binary .wordAnd x y) (.binary .wordAnd (.unary .wordNot x) z)
private def majority (x y z : Expr) : Expr :=
  xor3 (.binary .wordAnd x y) (.binary .wordAnd x z) (.binary .wordAnd y z)

private def round (constant : Nat) : Expr :=
  let state := Expr.var 0
  let t1 := sum32 [lane 7 state, large1 (lane 4 state), choose (lane 4 state) (lane 5 state) (lane 6 state),
    number constant, .var 64]
  let t2 := sum32 [large0 (lane 0 (.var 1)), majority (lane 0 (.var 1)) (lane 1 (.var 1)) (lane 2 (.var 1))]
  .letE t1 (.letE t2 (packet [sum32 [.var 1, .var 0], lane 0 (.var 2), lane 1 (.var 2),
    lane 2 (.var 2), sum32 [lane 3 (.var 2), .var 1], lane 4 (.var 2), lane 5 (.var 2), lane 6 (.var 2)]))

/-- Compress one sixteen-word message block into an eight-word chaining state. -/
def compress (state block : Expr) : Expr :=
  let schedule := (List.range 64).map fun index =>
    if index < 16 then field index 16 (.second (.var index))
    else sum32 [small1 (.var 1), .var 6, small0 (.var 14), .var 15]
  let completed := packet ((List.range 8).map fun index => sum32 [lane index (.var 64), lane index (.var 0)])
  .letE (.pair state block)
    (schedule.foldr Expr.letE (.letE (.first (.var 64)) ((constants.map round).foldr Expr.letE completed)))

private def digest (state : Expr) : Expr :=
  (List.range 8).foldl (fun result index => .binary .wordOr (shift result 32) (lane index state)) (number 0)

def hash (memoryReference sizeReference offset length : Expr) : Expr :=
  HashBlocks.hash {stateType, initial, compress, digest, littleEndian := false}
    memoryReference sizeReference offset length

end Solcore.Frontend.RustHull.Sha256
end

section
-- leanmerge: from Solcore.Frontend.RustHull.Precompiles
/-! Ethereum precompiles 1–4 and EIP-7951 P256VERIFY at 0x100 expressed entirely
in existing Core operations.
The caller supplies distinct cells for memory, memory size, return data and
return-data size. Gas is the amount forwarded to the precompile; instruction
and caller memory-expansion charging belongs to the surrounding runtime.

Input padding, return lengths and costs follow go-ethereum's implementations:
https://github.com/ethereum/go-ethereum/blob/master/core/vm/contracts.go
https://github.com/ethereum/go-ethereum/blob/master/params/protocol_params.go
-/
set_option autoImplicit false

namespace Solcore.Frontend.RustHull.Precompiles
open Core

/-- Calls outside the implemented precompile set need account dispatch. -/
def unsupportedTargetReason : Word := Word.ofNatModulo 7

private def packet : List Expr → Expr
  | [] => .unit
  | [value] => value
  | value :: rest => .pair value (packet rest)
private def field (index : Nat) : Nat → Expr → Expr
  | 0, _ => .unit
  | 1, value => value
  | count + 2, value => if index = 0 then .first value
      else field (index - 1) (count + 1) (.second value)

private abbrev Code := Nat → Expr
private def number (value : Nat) : Code := fun _ => .word (Word.ofNatModulo value)
private def integer (value : Nat) : Code := fun _ => .integer (Int.ofNat value)
private def arg : Code := fun depth => .var depth
private def part (index count : Nat) (value : Code) : Code := fun depth => field index count (value depth)
private def bind (value : Code) (body : Code → Code) : Code := fun depth =>
  .letE (value depth) (body (fun here => .var (here - depth - 1)) (depth + 1))
private def bindResult (value : Code) (body : Code → Code) : Code := fun depth =>
  LanguageResult.bind .word (value depth)
    (body (fun here => .var (here - depth - 1)) (depth + 1))
private def success (value : Code) : Code := fun depth => LanguageResult.success (value depth)
private def unary (op : UnaryOp) (value : Code) : Code := fun depth => .unary op (value depth)
private def binary (op : BinaryOp) (a b : Code) : Code := fun depth => .binary op (a depth) (b depth)
private def choose (test yes no : Code) : Code := fun depth => .ifE (test depth) (yes depth) (no depth)
private def matchOption (value : Code) (none : Code) (some : Code → Code) : Code := fun depth =>
  .caseE (value depth) (none (depth + 1))
    (some (fun here => .var (here - depth - 1)) (depth + 1))
private def load (reference : Code) : Code := fun depth => .loadCell (reference depth)
private def store (reference value : Code) : Code := fun depth => .storeCell (reference depth) (value depth)
private def allocate (type : Ty) (value : Code) : Code := fun depth => .newCell type (value depth)
private def empty : Code := fun _ => WordMapping.empty
private def touch (size offset length : Code) : Code := fun depth =>
  Memory.touch (size depth) (offset depth) (length depth)
private def copy (memory size destination mapping source length : Code) : Code := fun depth =>
  Memory.copyPackedFrom (memory depth) (size depth) (destination depth)
    (mapping depth) (source depth) (length depth)

private def memory : Code := part 0 10 arg
private def memorySize : Code := part 1 10 arg
private def returnData : Code := part 2 10 arg
private def returnSize : Code := part 3 10 arg
private def gas : Code := part 4 10 arg
private def target : Code := part 5 10 arg
private def inputOffset : Code := part 6 10 arg
private def inputLength : Code := part 7 10 arg
private def outputOffset : Code := part 8 10 arg
private def outputLength : Code := part 9 10 arg

/-- Cost comparison uses unbounded Core integers, including the multiplication.
RIPEMD's cost can exceed a Word even for a representable memory range. -/
private def enoughGas (base perWord : Nat) : Code :=
  unary .boolNot (binary .integerLt (unary .wordToInteger gas)
    (binary .integerAdd (integer base)
      (binary .integerMul (integer perWord)
        (binary .integerDiv
          (binary .integerAdd (unary .wordToInteger inputLength) (integer 31)) (integer 32)))))

private def finish (mapping length : Code) : Code :=
  bind mapping fun snapshot =>
  bind (store returnData snapshot) fun _ =>
  bind (store returnSize length) fun _ =>
  bindResult (copy memory memorySize outputOffset snapshot (number 0)
    (choose (binary .wordGt length outputLength) outputLength length)) fun _ =>
  success (number 1)

private def finishWord (value : Code) : Code :=
  bindResult (fun depth => WordMapping.insert WordMapping.empty (number 0 depth) (value depth)) fun mapping =>
  finish mapping (number 32)

/-- The supplied length, not the caller memory contents beyond that length,
determines the zero padding for each recovery argument. -/
private def inputWord (snapshot : Code) (start : Nat) : Code :=
  choose (binary .wordGt inputLength (number start))
    (bindResult (fun depth => Memory.readMemoryWord (snapshot depth)
      (binary .wordAdd inputOffset (number start) depth)) fun value =>
      bind (binary .wordSub inputLength (number start)) fun remaining =>
      success (choose (binary .wordGt remaining (number 31)) value
        (binary .wordAnd value
          (binary .wordShl (number (wordModulus - 1))
            (binary .wordMul (binary .wordSub (number 32) remaining) (number 8))))))
    (success (number 0))

private def recover (snapshot : Code) : Code :=
  bindResult (inputWord snapshot 0) fun hash =>
  bindResult (inputWord snapshot 32) fun v =>
  bindResult (inputWord snapshot 64) fun r =>
  bindResult (inputWord snapshot 96) fun s =>
  bindResult (fun depth => Secp256k1.recover (hash depth) (v depth) (r depth) (s depth)) fun recovered =>
  matchOption recovered (success (number 1)) finishWord

private def verifyP256 (snapshot : Code) : Code :=
  choose (binary .wordEq inputLength (number 160))
    (bindResult (inputWord snapshot 0) fun hash =>
     bindResult (inputWord snapshot 32) fun r =>
     bindResult (inputWord snapshot 64) fun s =>
     bindResult (inputWord snapshot 96) fun x =>
     bindResult (inputWord snapshot 128) fun y =>
     bindResult (fun depth => P256.verify (hash depth) (r depth) (s depth) (x depth) (y depth)) fun valid =>
     choose valid (finishWord (number 1)) (success (number 1)))
    (success (number 1))

private def hash (operation : Expr → Expr → Expr → Expr → Expr) (snapshot : Code) : Code :=
  bind (allocate WordMapping.type snapshot) fun sourceMemory =>
  bind (allocate .word (number 0)) fun sourceSize =>
  bindResult (fun depth => operation (sourceMemory depth) (sourceSize depth)
    (inputOffset depth) (inputLength depth)) finishWord

private def identity (snapshot : Code) : Code :=
  bind (allocate WordMapping.type empty) fun resultMemory =>
  bind (allocate .word (number 0)) fun resultSize =>
  bindResult (copy resultMemory resultSize (number 0) snapshot inputOffset inputLength) fun _ =>
  finish (load resultMemory) inputLength

private def dispatch (snapshot : Code) : Code :=
  bind (binary .wordAnd target (number (2 ^ 160 - 1))) fun address =>
  choose (binary .wordEq address (number 1))
    (choose (enoughGas 3000 0) (recover snapshot) (success (number 0))) <|
  choose (binary .wordEq address (number 2))
    (choose (enoughGas 60 12) (hash Sha256.hash snapshot) (success (number 0))) <|
  choose (binary .wordEq address (number 3))
    (choose (enoughGas 600 120) (hash Ripemd160.hash snapshot) (success (number 0))) <|
  choose (binary .wordEq address (number 4))
    (choose (enoughGas 15 3) (identity snapshot) (success (number 0))) <|
  choose (binary .wordEq address (number 0x100))
    (choose (enoughGas 6900 0) (verifyP256 snapshot) (success (number 0)))
    (fun _ => LanguageResult.failure .word (.word unsupportedTargetReason))

private def callCode : Code :=
  bindResult (touch memorySize inputOffset inputLength) fun _ =>
  bindResult (touch memorySize outputOffset outputLength) fun _ =>
  bind (load memory) fun snapshot =>
  bind (store returnData empty) fun _ =>
  bind (store returnSize (number 0)) fun _ =>
  dispatch snapshot

/-- Call a supported precompile, evaluating every argument once. The retained
input snapshot permits overlapping input/output ranges. Complete packed return
data is recorded independently of the requested output length. Invalid recovery
returns success with no bytes; insufficient forwarded gas returns zero and no
bytes. Neither case overwrites the caller's output bytes. -/
def staticCall (memoryReference sizeReference returnDataReference returnSizeReference
    suppliedGas address sourceOffset sourceLength destinationOffset destinationLength : Expr) : Expr :=
  .letE (packet [memoryReference, sizeReference, returnDataReference, returnSizeReference,
    suppliedGas, address, sourceOffset, sourceLength, destinationOffset, destinationLength]) (callCode 0)

end Solcore.Frontend.RustHull.Precompiles
end
