import Solcore.Frontend.RustHull.AccountInspection
import Solcore.Abi.Keccak256
import Solcore.Core.Machine

set_option autoImplicit false
namespace Tests.RustHullAccountInspection
open Solcore.Core Solcore.Frontend.RustHull

private def require (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)
private def word (value : Nat) : Solcore.Core.Expr := .word (Word.ofNatModulo value)
private def scalar (value : Nat) : Value := .word (Word.ofNatModulo value)
private def account (target : Nat) (code : Option (List UInt8)) (nonce : Nat := 0)
    (destroyed : Bool := false) : AccountState.Account :=
  { address := Word.ofNatModulo target, code, nonce := Word.ofNatModulo nonce, destroyed }
private def longCode : List UInt8 := (List.range 137).map fun index => UInt8.ofNat (index * 17 + 3)
private def hashValue (bytes : List UInt8) : Nat :=
  (Solcore.Abi.V1.Keccak256.hash bytes.toByteArray).data.foldl
    (fun value byte => value * 256 + byte.toNat) 0
private def catalog : List (AccountState.Account × Nat) :=
  [(account 10 (some []), 0), (account 11 (some []) 1, 0),
   (account 12 (some []), 0), (account 13 (some [0x61, 0x62, 0x63]) 1, 1),
   (account 14 none 1, 0), (account 15 (some [0x61, 0x62, 0x63]) 1 true, 1),
   (account 16 (some longCode) 1, 2)]
private def balances : WordMapping.Entries := [(Word.ofNatModulo 12, Word.ofNatModulo 7)]

/-- Bodies see size, memory, balances and world cells at indices zero to three. -/
private def initialized (body : Solcore.Core.Expr) : Solcore.Core.Expr :=
  .letE (.newCell AccountState.type (AccountState.literal catalog))
    (.letE (.newCell WordMapping.type (WordMapping.literal balances))
      (.letE (.newCell WordMapping.type WordMapping.empty)
        (.letE (.newCell .word (word 0)) body)))
private def program (result : Solcore.Core.Ty) (body : Solcore.Core.Expr) : Solcore.Core.Program := {
  dataDefinitions := AccountInspection.definitions
  resultType := LanguageResult.resultType result
  body := initialized body
}
private def expect (label : String) (result : Solcore.Core.Ty) (body : Solcore.Core.Expr) (value : Value)
    (memorySize : Nat := 0) : IO Unit := do
  let compiled := program result body
  require compiled.check s!"{label}: generated Core is ill-typed"
  match compiled.runStateful 3000000 with
  | .done actual store =>
      require (actual == value) s!"{label}: expected {reprStr value}, got {reprStr actual}"
      require (store[3]? == some (scalar memorySize)) s!"{label}: caller memory size changed unexpectedly"
      require (store[1]? == some (WordMapping.encode balances)) s!"{label}: balances changed"
  | other => throw (IO.userError s!"{label}: {reprStr other}")
private def succeeded (value : Nat) : Value := .inRight .word (scalar value)
private def failed (type : Solcore.Core.Ty) (reason : Nat) : Value := .inLeft type (scalar reason)
private def size (target : Nat) (complete : Bool := false) : Solcore.Core.Expr :=
  AccountInspection.size (.var 3) (.bool complete) (word target)
private def hash (target : Nat) (complete : Bool := false) : Solcore.Core.Expr :=
  AccountInspection.hash (.var 3) (.bool complete) (.var 2) (word target)
private def copy (target destination source length : Nat) (complete : Bool := false) : Solcore.Core.Expr :=
  AccountInspection.copy (.var 3) (.bool complete) (.var 1) (.var 0)
    (word target) (word destination) (word source) (word length)
private def copiedWord (target destination source length readOffset : Nat)
    (complete : Bool := false) : Solcore.Core.Expr :=
  LanguageResult.bind .word (copy target destination source length complete)
    (Memory.readMemoryWord (.loadCell (.var 2)) (word readOffset))

def run : IO Unit := do
  let emptyHash := 0xc5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470
  let abcHash := 0x4e03657aea45a94fc7d47ba826c8d667c0d1e6e33a64a036ec44f58fa12d6c45
  for target in [10, 11, 12] do
    expect s!"empty code size {target}" .word (size target) (succeeded 0)
  expect "registered code size" .word (size 13) (succeeded 3)
  expect "pending destruction retains size" .word (size 15) (succeeded 3)
  expect "size normalizes high address" .word (size (2 ^ 200 + 13)) (succeeded 3)
  expect "closed world absent size" .word (size 99 true) (succeeded 0)
  expect "open world absent size" .word (size 99) (failed .word 7)
  expect "supplied account lacks code size" .word (size 14) (failed .word 15)
  expect "closed world does not invent missing code" .word (size 14 true) (failed .word 15)
  expect "EIP161 empty account hash" .word (hash 10) (succeeded 0)
  expect "nonexistent hash" .word (hash 99 true) (succeeded 0)
  expect "nonce-only hash" .word (hash 11) (succeeded emptyHash)
  expect "funded code-empty hash" .word (hash 12) (succeeded emptyHash)
  expect "registered code hash" .word (hash 13) (succeeded abcHash)
  expect "pending destruction retains hash" .word (hash 15) (succeeded abcHash)
  expect "hash normalizes high address" .word (hash (2 ^ 200 + 13)) (succeeded abcHash)
  expect "open world absent hash" .word (hash 99) (failed .word 7)
  expect "unknown code hash" .word (hash 14) (failed .word 15)
  expect "multi-block code hash" .word (hash 16) (succeeded (hashValue longCode))
  let targetOnce := Solcore.Core.Expr.letE
    (.storeCell (.var 0) (.binary .wordAdd (.loadCell (.var 0)) (word 1))) (word 13)
  expect "size target evaluated once" .word
    (AccountInspection.size (.var 3) (.bool false) targetOnce) (succeeded 3) 1
  expect "hash target evaluated once" .word
    (AccountInspection.hash (.var 3) (.bool false) (.var 2) targetOnce) (succeeded abcHash) 1
  expect "copy code and zero-pad suffix" .word (copiedWord 13 0 1 5 0)
    (succeeded (0x6263 * 256 ^ 30)) 32
  expect "copy crosses memory word boundary" .word (copiedWord 13 31 0 3 31)
    (succeeded (0x616263 * 256 ^ 29)) 64
  expect "copy source cannot wrap" .word (copiedWord 13 0 (wordModulus - 1) 64 0)
    (succeeded 0) 64
  expect "copy absent known empty account" .word (copiedWord 99 0 0 32 0 true)
    (succeeded 0) 32
  expect "copy normalizes high address" .word (copiedWord (2 ^ 200 + 13) 0 0 3 0)
    (succeeded (0x616263 * 256 ^ 29)) 32
  expect "copy zero length huge offsets" .unit (copy 13 (wordModulus - 1) (wordModulus - 1) 0)
    (.inRight .word .unit)
  expect "copy unknown account preserves memory" .unit (copy 99 0 0 32) (failed .unit 7)
  expect "copy unknown image preserves memory" .unit (copy 14 0 0 32) (failed .unit 15)
  expect "copy destination range overflow" .unit (copy 13 (wordModulus - 1) 0 1) (failed .unit 6)
  let unregistered := {program .word (size 13) with dataDefinitions := Memory.definitions}
  require (!unregistered.check) "account operations accepted an unregistered world mapping definition"
  match (program .word (hash 16)).runStateful 100 with
  | .outOfFuel state =>
      match runStateful 3000000 state with
      | .done actual _ =>
          require (actual == succeeded (hashValue longCode))
            "account hash resumption changed the returned digest"
      | _ => throw (IO.userError "account hash resumption failed")
  | _ => throw (IO.userError "account hash did not suspend with the small budget")

end Tests.RustHullAccountInspection
