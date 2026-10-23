import Solcore.Frontend.RustHull.Secp256k1
import Solcore.Core.Machine
import Solcore.Core.Check

set_option autoImplicit false
namespace Tests.RustHullSecp256k1
open Solcore.Core
open Solcore.Frontend.RustHull

private def require (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)
private def word (n : Nat) : Expr := .word (Word.ofNatModulo n)
private def scalar (n : Nat) : Value := .word (Word.ofNatModulo n)
private def generator : Expr := .pair (word Secp256k1.generatorX) (word Secp256k1.generatorY)
private def jacobian : Expr := .pair (word Secp256k1.generatorX) (.pair (word Secp256k1.generatorY) (word 1))
private def ok (value : Value) : Value := .inRight .word value
private def someValue (value : Value) : Value := .inRight .unit value
private def absent (type : Ty) : Value := .inLeft type .unit

private def expect (label : String) (type : Ty) (body : Expr) (expected : Value) : IO Unit := do
  let program : Program := {resultType := type, dataDefinitions := Memory.definitions, body}
  match inferDetailed [] [] body Memory.definitions with
  | .error error => throw (IO.userError s!"secp256k1 {label}: invalid Core: {reprStr error}")
  | .ok actualType => require (actualType == type) s!"secp256k1 {label}: wrong Core result type"
  match program.runStateful 10000000 with
  | .done actual _ => do
    require (actual == expected) s!"secp256k1 {label}: expected {reprStr expected}, got {reprStr actual}"
  | .outOfFuel _ => throw (IO.userError s!"secp256k1 {label}: test fuel exhausted")
  | .fault error _ => throw (IO.userError s!"secp256k1 {label}: {reprStr error}")

private def recover (h v r s : Nat) : Expr := Secp256k1.recover (word h) (word v) (word r) (word s)
private def optionWord : Ty := LanguageResult.resultType (Secp256k1.optionType .word)

private def fieldAndCurve : IO Unit := do
  for (a, e, m, result) in [(2, 10, 17, 4), (5, 0, 1, 0), (5, 0, 0, 0), (0, 0, 17, 1)] do
    expect "modular power" (LanguageResult.resultType .word)
      (Secp256k1.powMod (word a) (word e) (word m)) (ok (scalar result))
  expect "field inverse" (LanguageResult.resultType .word)
    (Secp256k1.powMod (word 2) (word (Secp256k1.prime - 2)) (word Secp256k1.prime))
    (ok (scalar ((Secp256k1.prime + 1) / 2)))
  let doubledX := 0xc6047f9441ed7d6d3045406e95c07cd85c778e4b8cef3ca7abac09b95c709ee5
  let doubledY := 0x1ae168fea63dc339a3c58419466ceaeef7f632653266d0e1236431a950cfe52a
  let expected := ok (someValue (.pair (scalar doubledX) (scalar doubledY)))
  let optionAffine := LanguageResult.resultType (Secp256k1.optionType Secp256k1.affineType)
  expect "double generator" optionAffine (Secp256k1.normalize (Secp256k1.doublePoint jacobian)) expected
  expect "equal-point mixed addition" optionAffine (Secp256k1.normalize (Secp256k1.addAffine jacobian generator)) expected
  expect "opposite-point mixed addition" optionAffine
    (Secp256k1.normalize (Secp256k1.addAffine jacobian
      (.pair (word Secp256k1.generatorX) (word (Secp256k1.prime - Secp256k1.generatorY)))))
    (ok (absent Secp256k1.affineType))
  expect "joint scalar multiplication" optionAffine
    (LanguageResult.bind (Secp256k1.optionType Secp256k1.affineType)
      (Secp256k1.jointMultiply generator generator (word 1) (word 1))
      (Secp256k1.normalize (.var 0))) expected

private def recovery : IO Unit := do
  -- Pinned upstream tests/e2e/ecrecover/main.sol, private key one.
  let hash := 0xaabbccddeeff00112233445566778899aabbccddeeff00112233445566778899
  let r := 0xb3ba6dd3757d18f28736e84b1296af85362b7bdf4548710733c6325abf95311d
  let s := 0x3523e7d34da277c59af090e44cebddb10b73be11780f028d02cf5ae5f24109fc
  let address := 0x7e5f4552091a69125d5dfcb7b8c2659029395bdf
  expect "upstream valid recovery" optionWord (recover hash 27 r s) (ok (someValue (scalar address)))
  expect "high-s parity counterpart" optionWord (recover hash 28 r (Secp256k1.order - s))
    (ok (someValue (scalar address)))
  for (v, invalidR, invalidS) in [(1, r, s), (29, r, s), (283, r, s),
      (27, 0, s), (27, Secp256k1.order, s), (27, r, 0), (27, r, Secp256k1.order)] do
    expect "invalid signature components" optionWord (recover hash v invalidR invalidS)
      (ok (absent .word))
  expect "nonce-one signature" optionWord
    (recover 1 27 Secp256k1.generatorX (Secp256k1.generatorX + 1))
    (ok (someValue (scalar address)))
  expect "nonsquare recovery coordinate" optionWord (recover 1 27 5 1) (ok (absent .word))
  -- Independently checked against Anvil's precompile; vectors are retained in
  -- scripts/secp256k1-vectors.json. These cover both parities and hash reduction.
  expect "maximum hash, key two" optionWord
    (recover (wordModulus - 1) 28
      0x270c504ade45b9bf70ed7dd54f2f253671c4568e3b2a2319d2efc6942b58f796
      0x076b9b8b0449bc498635d324e2f50365964e65ef0fcbcec9b9941e69f91b0aaa)
    (ok (someValue (scalar 0x2b5ad5c4795c026514f8317c7a215e218dccd6cf)))
  expect "zero hash, key three" optionWord
    (recover 0 27
      0xe95058f48325b8b37415edd898822fcfc83d8fdc5e257d3c370c0304c42dd5f2
      0x6836450f27b3ccd9d0e86629627b28b61fcdaeab49d9099f4170ccd3b3258e81)
    (ok (someValue (scalar 0x6813eb9362372eef6200f3b1dbc3f819671cba69)))
  expect "infinite recovered point" optionWord (recover 1 27 Secp256k1.generatorX 1)
    (ok (absent .word))

private def resumptionAndArguments : IO Unit := do
  let address := 0x7e5f4552091a69125d5dfcb7b8c2659029395bdf
  let tick (value : Nat) : Expr :=
    .letE (.storeCell (.var 0) (.binary .wordAdd (.loadCell (.var 0)) (word 1))) (word value)
  let body := Expr.letE (.newCell .word (word 0))
    (.letE (Secp256k1.recover (tick 1) (tick 27)
      (tick Secp256k1.generatorX) (tick (Secp256k1.generatorX + 1)))
      (.pair (.var 0) (.loadCell (.var 1))))
  let expected := Value.pair (ok (someValue (scalar address))) (scalar 4)
  expect "arguments evaluated once; caller cell preserved"
    (.product optionWord .word) body expected
  match runStateful 2000 (.initial body) with
  | .outOfFuel state =>
      match runStateful 10000000 state with
      | .done value _ => require (value == expected) "recovery resumption repeated arguments or changed the address"
      | _ => throw (IO.userError "recovery did not finish after resumption")
  | _ => throw (IO.userError "recovery suspension fixture did not exhaust its initial fuel")

def run : IO Unit := do
  fieldAndCurve
  recovery
  resumptionAndArguments

end Tests.RustHullSecp256k1
