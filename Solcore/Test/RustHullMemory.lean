import Solcore.Frontend.RustHull.Memory
import Solcore.Core.Machine

set_option autoImplicit false

namespace Tests.RustHullMemory
open Solcore.Core
open Solcore.Frontend.RustHull

private def word (value : Nat) : Expr := .word (Word.ofNatModulo value)
private def scalar (value : Nat) : Value := .word (Word.ofNatModulo value)
private def require (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

/-- Test bodies see the size cell at zero and the memory cell at one. -/
private def memory (body : Expr) : Expr :=
  .letE (.newCell WordMapping.type WordMapping.empty)
    (.letE (.newCell .word (word 0)) body)

private def sequence (result : Ty) (action next : Expr) : Expr :=
  LanguageResult.bind result action (next.weakenAt 0)

private def withSize (action : Expr) : Expr :=
  LanguageResult.bind (.product .word .word) action
    (LanguageResult.success (.pair (.var 0) (.loadCell (.var 1))))

private def expect (label : String) (result : Ty) (body : Expr) (value : Value) : IO Unit := do
  let program : Program := {
    resultType := LanguageResult.resultType result
    body
    dataDefinitions := Memory.definitions
  }
  require program.check s!"{label}: memory helper produced ill-typed Core"
  match program.run 3000000 with
  | .done actual => require (actual == .inRight .word value) s!"{label}: expected {reprStr value}, got {reprStr actual}"
  | other => throw (IO.userError s!"{label}: {reprStr other}")

def run : IO Unit := do
  let maximum := wordModulus - 1
  let pattern := (List.range 32).foldl (fun value index => value * 256 + index + 1) 0
  expect "initial size" .word (memory (Memory.msize (.var 0))) (scalar 0)
  expect "zero-filled read expands size" (.product .word .word)
    (memory (withSize (Memory.mload (.var 1) (.var 0) (word 1))))
    (.pair (scalar 0) (scalar 64))
  expect "word round trip" .word
    (memory (sequence .word (Memory.mstore (.var 1) (.var 0) (word 0) (word pattern))
      (Memory.mload (.var 1) (.var 0) (word 0)))) (scalar pattern)
  expect "unaligned word round trip" (.product .word .word)
    (memory (sequence (.product .word .word)
      (Memory.mstore (.var 1) (.var 0) (word 1) (word pattern))
      (withSize (Memory.mload (.var 1) (.var 0) (word 1)))))
    (.pair (scalar pattern) (scalar 64))
  expect "unaligned zero prefix" .word
    (memory (sequence .word (Memory.mstore (.var 1) (.var 0) (word 1) (word pattern))
      (Memory.mload (.var 1) (.var 0) (word 0)))) (scalar (pattern / 256))
  expect "big endian first byte" .word
    (memory (sequence .word (Memory.mstore (.var 1) (.var 0) (word 0) (word pattern))
      (Memory.loadByte (.var 1) (.var 0) (word 0)))) (scalar 1)
  expect "mstore8 uses low byte" .word
    (memory (sequence .word (Memory.mstore8 (.var 1) (.var 0) (word 31) (word 0x1ab))
      (Memory.mload (.var 1) (.var 0) (word 0)))) (scalar 0xab)
  expect "byte overwrite preserves neighbors" .word
    (memory (sequence .word (Memory.mstore (.var 1) (.var 0) (word 0) (word pattern))
      (sequence .word (Memory.mstore8 (.var 1) (.var 0) (word 17) (word 0xab))
        (Memory.mload (.var 1) (.var 0) (word 0)))))
    (scalar (pattern + (0xab - 18) * 256 ^ 14))
  expect "cross-word byte overwrite" (.product .word .word)
    (memory (sequence (.product .word .word)
      (Memory.mstore (.var 1) (.var 0) (word 31) (word (0xab * 256 ^ 31)))
      (withSize (Memory.mload (.var 1) (.var 0) (word 0)))))
    (.pair (scalar 0xab) (scalar 64))
  expect "memory size never shrinks" .word
    (memory (sequence .word (Memory.touch (.var 0) (word 96) (word 1))
      (sequence .word (Memory.touch (.var 0) (word 0) (word 1)) (Memory.msize (.var 0)))))
    (scalar 128)
  expect "zero length ignores huge offset" .word
    (memory (sequence .word (Memory.touch (.var 0) (word maximum) (word 0))
      (Memory.msize (.var 0)))) (scalar 0)
  expect "calldata right padding" .word
    (Memory.readWord (WordMapping.literal [(Word.zero, Word.ofNatModulo 0x12),
      (Word.ofNatModulo 1, Word.ofNatModulo 0x34)]) (word 0))
    (scalar (0x1234 * 256 ^ 30))
  expect "calldata offset cannot wrap" .word
    (Memory.readWord (WordMapping.literal [(Word.zero, Word.ofNatModulo 0xff)]) (word maximum))
    (scalar 0)
  expect "copy overlaps to the right" .word
    (memory (sequence .word (Memory.mstore (.var 1) (.var 0) (word 0) (word pattern))
      (sequence .word (Memory.mcopy (.var 1) (.var 0) (word 1) (word 0) (word 31))
        (Memory.mload (.var 1) (.var 0) (word 0)))))
    (scalar (256 ^ 31 + pattern / 256))
  expect "copy overlaps to the left" .word
    (memory (sequence .word (Memory.mstore (.var 1) (.var 0) (word 0) (word pattern))
      (sequence .word (Memory.mcopy (.var 1) (.var 0) (word 0) (word 1) (word 31))
        (Memory.mload (.var 1) (.var 0) (word 0)))))
    (scalar ((pattern * 256) % wordModulus + 32))
  expect "copy to fresh word" (.product .word .word)
    (memory (sequence (.product .word .word)
      (Memory.mstore (.var 1) (.var 0) (word 0) (word pattern))
      (sequence (.product .word .word) (Memory.mcopy (.var 1) (.var 0) (word 32) (word 0) (word 32))
        (withSize (Memory.mload (.var 1) (.var 0) (word 32))))))
    (.pair (scalar pattern) (scalar 64))
  expect "copy unwritten zero bytes" (.product .word .word)
    (memory (sequence (.product .word .word)
      (Memory.mstore (.var 1) (.var 0) (word 0) (word pattern))
      (sequence (.product .word .word) (Memory.mcopy (.var 1) (.var 0) (word 0) (word 64) (word 32))
        (withSize (Memory.mload (.var 1) (.var 0) (word 0))))))
    (.pair (scalar 0) (scalar 96))
  expect "zero copy ignores huge offsets" .word
    (memory (sequence .word (Memory.mcopy (.var 1) (.var 0) (word maximum) (word maximum) (word 0))
      (Memory.msize (.var 0)))) (scalar 0)
  let calldata := WordMapping.literal [(Word.zero, Word.ofNatModulo 0x12),
    (Word.ofNatModulo 1, Word.ofNatModulo 0x34)]
  expect "calldata copy pads absent bytes" (.product .word .word)
    (memory (sequence (.product .word .word)
      (Memory.copyFrom (.var 1) (.var 0) (word 1) calldata (word 0) (word 3))
      (withSize (Memory.mload (.var 1) (.var 0) (word 0)))))
    (.pair (scalar (0x1234 * 256 ^ 29)) (scalar 32))
  expect "calldata copy never wraps its source offset" .word
    (memory (sequence .word
      (Memory.copyFrom (.var 1) (.var 0) (word 0) calldata (word maximum) (word 3))
      (Memory.mload (.var 1) (.var 0) (word 0)))) (scalar 0)
  expect "calldata source range does not expand memory" .word
    (memory (sequence .word
      (Memory.copyFrom (.var 1) (.var 0) (word 0) calldata (word 4096) (word 1))
      (Memory.msize (.var 0)))) (scalar 32)
  for offset in [maximum, wordModulus - 16, wordModulus - 32] do
    let program : Program := {
      resultType := .product (LanguageResult.resultType .unit) .word
      dataDefinitions := Memory.definitions
      body := memory (.pair (Memory.mstore (.var 1) (.var 0) (word offset) (word pattern))
        (.loadCell (.var 0)))
    }
    require program.check "overflow guard is ill-typed"
    match program.runStateful 10000 with
    | .done result store =>
        require (result == .pair (.inLeft .unit (.word Memory.overflowReason)) (scalar 0))
          "overflow wrapped the range or changed memory size"
        require (store[0]? == some (WordMapping.encode [])) "overflow changed byte memory"
    | other => throw (IO.userError s!"overflow did not terminate: {reprStr other}")

  let badCopy : Program := {
    resultType := .product (LanguageResult.resultType .unit) .word
    dataDefinitions := Memory.definitions
    body := memory (.pair
      (Memory.mcopy (.var 1) (.var 0) (word 0) (word maximum) (word 32)) (.loadCell (.var 0)))
  }
  require badCopy.check "copy overflow guard is ill-typed"
  match badCopy.runStateful 10000 with
  | .done result store =>
      require (result == .pair (.inLeft .unit (.word Memory.overflowReason)) (scalar 0))
        "copy touched the destination before rejecting its source range"
      require (store[0]? == some (WordMapping.encode [])) "copy overflow changed byte memory"
  | other => throw (IO.userError s!"copy overflow did not terminate: {reprStr other}")

  let resumable : Program := {
    resultType := LanguageResult.resultType .word
    dataDefinitions := Memory.definitions
    body := memory (sequence .word (Memory.mstore (.var 1) (.var 0) (word 0) (word pattern))
      (sequence .word (Memory.mcopy (.var 1) (.var 0) (word 1) (word 0) (word 31))
        (Memory.mload (.var 1) (.var 0) (word 0))))
  }
  require resumable.check "resumable copy is ill-typed"
  match resumable.runStateful 10000 with
  | .outOfFuel checkpoint =>
      require (runStateful 3000000 checkpoint == resumable.runStateful 3010000)
        "resuming memory copy repeated or lost a byte write"
  | _ => throw (IO.userError "copy fixture did not suspend")

  -- Each raw input can have effects. Capturing them must neither repeat a
  -- reference expression nor read stale memory after evaluating the value.
  let tick (result : Expr) : Expr :=
    .letE (.storeCell (.var 2) (.binary .wordAdd (.loadCell (.var 2)) (word 1)))
      (result.weakenAt 0)
  let once : Program := {
    resultType := .product (LanguageResult.resultType .unit) .word
    dataDefinitions := Memory.definitions
    body := .letE (.newCell .word (word 0))
      (memory (.pair (Memory.mstore8 (tick (.var 1)) (tick (.var 0)) (tick (word 0)) (tick (word 0xab)))
        (.loadCell (.var 2))))
  }
  require once.check "effectful memory arguments are ill-typed"
  match once.runStateful 100000 with
  | .done result store =>
      require (result == .pair (.inRight .word .unit) (scalar 4)) "memory argument effects were repeated"
      require (store[1]? == some (WordMapping.encode [(Word.zero, Word.ofNatModulo 0xab)]))
        "memory reference changed during argument capture"
  | other => throw (IO.userError s!"effectful memory arguments: {reprStr other}")

end Tests.RustHullMemory
