import Solcore.Frontend.RustHull.P256
import Solcore.Core.Machine
import Solcore.Core.Check
import Lean

set_option autoImplicit false
namespace Tests.RustHullP256
open Solcore.Core
open Solcore.Frontend.RustHull
open Lean (Json)

private def require (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)
private def word (n : Nat) : Expr := .word (Word.ofNatModulo n)
private def scalar (n : Nat) : Value := .word (Word.ofNatModulo n)
private def ok (value : Value) : Value := .inRight .word value
private def expect (label : String) (type : Ty) (body : Expr) (expected : Value) : IO Unit := do
  let program : Program := {resultType := type, dataDefinitions := Memory.definitions, body}
  match inferDetailed [] [] body Memory.definitions with
  | .error error => throw (IO.userError s!"P256 {label}: invalid Core: {reprStr error}")
  | .ok actualType => require (actualType == type) s!"P256 {label}: wrong Core result type"
  match program.runStateful 10000000 with
  | .done actual _ =>
      require (actual == expected) s!"P256 {label}: expected {reprStr expected}, got {reprStr actual}"
  | .outOfFuel _ => throw (IO.userError s!"P256 {label}: test fuel exhausted")
  | .fault error _ => throw (IO.userError s!"P256 {label}: {reprStr error}")

private def verify (h r s x y : Nat) : Expr := P256.verify (word h) (word r) (word s) (word x) (word y)
private def check (label : String) (h r s x y : Nat) (valid : Bool) : IO Unit :=
  expect label (LanguageResult.resultType .bool) (verify h r s x y) (ok (.bool valid))

private def knownSignatures : IO Unit := do
  let h := 0xabcdef00112233445566778899aabbccddeeff00112233445566778899aabbcc
  let r := 0xa29295460e251beea1bdc9b84b2f3fe8e3a3e4d872baa3c55b78c9e448190ea9
  let s := 0x2d854575b092b3732d3d73c8414bda17f907776894cff2e8e25e733d200f3f5c
  let x := 0x6079df2480f92e4cf526c08e32ab82aed6599fddb777a039612fe7c9ef0247ba
  let y := 0xe2b4793e7c77585508c4780e4e53a36deefbb3548f4380ee6df04863cfc54c2d
  check "pinned upstream valid" h r s x y true
  check "pinned upstream changed hash" (h + 1) r s x y false
  check "high-s counterpart remains valid" h r (P256.order - s) x y true
  for (badR, badS) in [(0, s), (P256.order, s), (wordModulus - 1, s),
      (r, 0), (r, P256.order), (r, wordModulus - 1)] do
    check "scalar bounds" h badR badS x y false
  for (badX, badY) in [(P256.prime, y), (x, P256.prime), (wordModulus - 1, y),
      (x, wordModulus - 1), (0, 0), (x, (y + 1) % P256.prime)] do
    check "public-key bounds and membership" h r s badX badY false
  check "nonce-one key-one signature" 1 P256.generatorX (P256.generatorX + 1)
    P256.generatorX P256.generatorY true
  check "maximum hash reduction" (wordModulus - 1) P256.generatorX
    ((wordModulus - 1 + P256.generatorX) % P256.order) P256.generatorX P256.generatorY true
  check "reconstructed infinity is rejected" 1 1 1 P256.generatorX (P256.prime - P256.generatorY) false

private def curve : IO Unit := do
  let generator := Expr.pair (word P256.generatorX) (word P256.generatorY)
  let jacobian := Expr.pair (word P256.generatorX) (.pair (word P256.generatorY) (word 1))
  -- Independently derived by OpenSSL's P-256 key derivation for scalar 2.
  let doubledX := 0x7cf27b188d034f7e8a52380304b51ac3c08969e277f21b35a60b48fc47669978
  let doubledY := 0x07775510db8ed040293d9ac69f7430dbba7dade63ce982299e04b79d227873d1
  let expected := ok (.inRight .unit (.pair (scalar doubledX) (scalar doubledY)))
  let type := LanguageResult.resultType (P256.optionType P256.affineType)
  expect "double G" type (P256.normalize (P256.doublePoint jacobian)) expected
  expect "equal-point mixed addition" type (P256.normalize (P256.addAffine jacobian generator)) expected
  expect "opposite-point mixed addition" type
    (P256.normalize (P256.addAffine jacobian
      (.pair (word P256.generatorX) (word (P256.prime - P256.generatorY)))))
    (ok (.inLeft P256.affineType .unit))
  expect "joint G+G" type
    (LanguageResult.bind (P256.optionType P256.affineType)
      (P256.jointMultiply generator generator (word 1) (word 1)) (P256.normalize (.var 0))) expected

private def nibble (char : Char) : Except String Nat :=
  if '0' ≤ char && char ≤ '9' then .ok (char.toNat - '0'.toNat)
  else if 'a' ≤ char && char ≤ 'f' then .ok (char.toNat - 'a'.toNat + 10)
  else if 'A' ≤ char && char ≤ 'F' then .ok (char.toNat - 'A'.toNat + 10)
  else .error "invalid hexadecimal digit"
private def hexWord (chars : List Char) : Except String Nat :=
  chars.foldlM (fun value char => do return value * 16 + (← nibble char)) 0
private def get {α : Type} (value : Except String α) : IO α :=
  match value with
  | .ok result => pure result
  | .error error => throw (IO.userError error)

/-- Maintained vectors select every distinct category from the EIP-7951
conformance set, including large reconstructed x, infinity, Shamir edge cases,
coordinate-zero points, malleability, and scalar bounds. -/
def referenceVectors (path : System.FilePath := "scripts/p256-vectors.json") : IO Unit := do
  let json ← get (Json.parse (← IO.FS.readFile path))
  let vectors ← get (json.getObjValAs? (List Json) "vectors")
  for vector in vectors do
    let name ← get (vector.getObjValAs? String "name")
    let input ← get (vector.getObjValAs? String "input")
    let valid ← get (vector.getObjValAs? Bool "valid")
    require (input.length == 320) s!"P256 reference {name}: input must contain five words"
    let words ← get ((List.range 5).mapM fun i => hexWord ((input.toList.drop (i * 64)).take 64))
    let [h, r, s, x, y] := words | throw (IO.userError "P256 reference word decoding failed")
    check name h r s x y valid

private def argumentsAndResume : IO Unit := do
  let tick (value : Nat) : Expr :=
    .letE (.storeCell (.var 0) (.binary .wordAdd (.loadCell (.var 0)) (word 1))) (word value)
  let body := Expr.letE (.newCell .word (word 0))
    (.pair (P256.verify (tick 1) (tick P256.generatorX) (tick (P256.generatorX + 1))
      (tick P256.generatorX) (tick P256.generatorY)) (.loadCell (.var 0)))
  let expected := Value.pair (ok (.bool true)) (scalar 5)
  expect "all arguments once" (.product (LanguageResult.resultType .bool) .word) body expected
  match runStateful 2000 (.initial body) with
  | .outOfFuel state =>
      match runStateful 10000000 state with
      | .done value _ => require (value == expected) "P256 resumption repeated inputs or changed the result"
      | _ => throw (IO.userError "P256 did not finish after resumption")
  | _ => throw (IO.userError "P256 resumption fixture did not suspend")

def run : IO Unit := do
  curve
  knownSignatures
  referenceVectors
  argumentsAndResume

end Tests.RustHullP256
