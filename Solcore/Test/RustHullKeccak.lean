import Solcore.Frontend.RustHull.Keccak
import Solcore.Abi.Keccak256
import Solcore.Core.Machine

set_option autoImplicit false

namespace Tests.RustHullKeccak
open Solcore.Core
open Solcore.Frontend.RustHull

private def require (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)
private def word (value : Nat) : Expr := .word (Word.ofNatModulo value)
private def scalar (value : Nat) : Value := .word (Word.ofNatModulo value)
private def entries (bytes : List UInt8) (offset : Nat) : WordMapping.Entries :=
  Memory.packBytes bytes offset
private def expectedHash (bytes : List UInt8) : Word :=
  let hashed := Solcore.Abi.V1.Keccak256.hash bytes.toByteArray
  Word.ofNatModulo (hashed.data.foldl (fun value byte => value * 256 + byte.toNat) 0)

private def program (bytes : List UInt8) (offset : Nat := 0) (length : Nat := bytes.length) : Program := {
  resultType := LanguageResult.resultType (.product .word .word)
  dataDefinitions := Memory.definitions
  body := .letE (.newCell WordMapping.type (WordMapping.literal (entries bytes offset)))
    (.letE (.newCell .word (word 0))
      (LanguageResult.bind (.product .word .word)
        (Keccak.hash (.var 1) (.var 0) (word offset) (word length))
        (LanguageResult.success (.pair (.var 0) (.loadCell (.var 1))))))
}

private def expect (label : String) (bytes : List UInt8) (offset : Nat := 0) : IO Unit := do
  let compiled := program bytes offset
  require compiled.check s!"Keccak {label}: generated Core is ill-typed"
  let size := if bytes.isEmpty then 0 else ((offset + bytes.length + 31) / 32) * 32
  let expected := Value.inRight .word (.pair (.word (expectedHash bytes)) (scalar size))
  match compiled.runStateful 10000000 with
  | .done value store =>
      require (value == expected) s!"Keccak {label}: expected {reprStr expected}, got {reprStr value}"
      require (store[0]? == some (WordMapping.encode (entries bytes offset)))
        s!"Keccak {label}: hashing or padding changed memory"
  | .outOfFuel _ => throw (IO.userError s!"Keccak {label}: insufficient test fuel")
  | .fault error _ => throw (IO.userError s!"Keccak {label}: {reprStr error}")

def run : IO Unit := do
  require (expectedHash [] == Word.ofNatModulo
    0xc5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470)
    "reference empty Keccak vector changed"
  let abc := "abc".toUTF8.data.toList
  require (expectedHash abc == Word.ofNatModulo
    0x4e03657aea45a94fc7d47ba826c8d667c0d1e6e33a64a036ec44f58fa12d6c45)
    "reference abc Keccak vector changed"
  expect "empty" []
  expect "abc" abc
  expect "unaligned abc" abc 7
  for size in [31, 32, 135, 136, 137] do
    let bytes := (List.range size).map fun index => UInt8.ofNat (17 * index + 3)
    expect s!"{size} bytes" bytes
  expect "zero length at largest offset" [] (wordModulus - 1)

  let suspended := (program abc).runStateful 100
  match suspended with
  | .outOfFuel state =>
      match runStateful 10000000 state with
      | .done value _ =>
          require (value == .inRight .word (.pair (.word (expectedHash abc)) (scalar 32)))
            "Keccak resumption changed the digest or memory size"
      | _ => throw (IO.userError "Keccak resumption did not finish")
  | _ => throw (IO.userError "Keccak test did not suspend")

  let overflow := program [] (wordModulus - 1) 1
  require overflow.check "Keccak overflow fixture is ill-typed"
  match overflow.runStateful 1000 with
  | .done value store =>
      require (value == .inLeft (.product .word .word) (.word Memory.overflowReason))
        "Keccak accepted an overflowing memory range"
      require (store[1]? == some (scalar 0)) "Keccak overflow expanded memory"
  | _ => throw (IO.userError "Keccak overflow fixture did not return a language failure")

end Tests.RustHullKeccak
