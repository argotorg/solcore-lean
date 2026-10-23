import Solcore.Frontend.RustHull.Secp256k1

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
