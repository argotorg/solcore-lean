import Solcore.Frontend.RustHull.Keccak

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
