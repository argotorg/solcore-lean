import Solcore.Frontend.RustHull.MemorySnapshot
import Solcore.Core.Machine

set_option autoImplicit false
namespace Tests.RustHullMemorySnapshot
open Solcore.Core
open Solcore.Frontend.RustHull hiding Expr Ty Program

private def require (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)
private def word (value : Nat) : Word := Word.ofNatModulo value
private def number (value : Nat) : Solcore.Core.Expr := .word (word value)
private def entries : Value → Except String WordMapping.Entries
  | .constructed constructor .unit =>
      if constructor == WordMapping.nilConstructor then pure [] else .error "wrong nil constructor"
  | .constructed constructor (.pair (.pair (.word key) (.word value)) tail) => do
      unless constructor == WordMapping.consConstructor do throw "wrong cons constructor"
      pure ((key, value) :: (← entries tail))
  | _ => .error "invalid packed snapshot"
private def decoded : StatefulRunResult → IO WordMapping.Entries
  | .done (.inRight _ value) _ => match entries value with
      | .ok result => pure result
      | .error error => throw (IO.userError error)
  | other => throw (IO.userError s!"snapshot failed: {reprStr other}")
private def program (mapping : WordMapping.Entries) (offset length : Nat) : Program := {
  dataDefinitions := MemorySnapshot.definitions
  resultType := LanguageResult.resultType WordMapping.type
  body := MemorySnapshot.extract (WordMapping.literal mapping) (number offset) (number length)
}
private def execute (label : String) (mapping : WordMapping.Entries) (offset length : Nat)
    (fuel : Nat := 1000000) : IO WordMapping.Entries := do
  let compiled := program mapping offset length
  require compiled.check s!"{label}: ill-typed snapshot"
  let actual ← decoded (compiled.runStateful fuel)
  for index in List.range (length + 32) do
    let expected := if index < length && offset + index < wordModulus then
      Memory.lookupByte mapping (word (offset + index)) else Word.zero
    require (Memory.lookupByte actual (word index) == expected) s!"{label}: wrong byte at {index}"
  pure actual

private def rangeTests : IO Unit := do
  let mapping := Memory.packBytes ((List.range 147).map fun index => UInt8.ofNat (index * 17 + 3))
  for offset in [0, 32, 96, 2048] do
    for length in [0, 1, 31, 32, 33, 63, 64, 65] do
      discard (execute s!"aligned {offset}/{length}" mapping offset length)
  for offset in [1, 31, 33, 127] do
    for length in [0, 1, 31, 32, 33, 65] do
      discard (execute s!"unaligned {offset}/{length}" mapping offset length)
  let duplicate := [(word 9, word 55), (word 1, Word.zero), (word 1, Word.maximum),
    (word 2, Word.maximum), (word 0, word 8), (word 2, word 1), (word 3, word 7)]
  let actual ← execute "duplicates retain first-match order" duplicate 32 33
  let mask := (Word.maximum.shiftRight (word 248)).shiftLeft (word 248)
  require (actual == [(word 0, Word.zero), (word 0, Word.maximum), (word 1, mask), (word 1, Word.zero)])
    "aligned filter changed duplicate order or retained unrelated entries"
  let complete ← execute "full words are unchanged" duplicate 32 64
  require (complete == [(word 0, Word.zero), (word 0, Word.maximum),
    (word 1, Word.maximum), (word 1, word 1)]) "full-word snapshot changed packed values"

private def boundaryTests : IO Unit := do
  let last := (wordModulus - 1) / 32
  let mapping := [(word last, Word.maximum), (word (last + 1), Word.maximum),
    (Word.zero, Word.maximum), (Word.maximum, Word.maximum)]
  discard (execute "aligned source cannot wrap" mapping (wordModulus - 32) 64)
  discard (execute "unaligned source cannot wrap" mapping (wordModulus - 4) 12)
  let empty ← execute "zero length ignores maximum offset" mapping (wordModulus - 1) 0
  require empty.isEmpty "zero length retained source entries"
  for length in [wordModulus - 31, wordModulus - 1] do
    let compiled := program mapping 0 length
    require compiled.check "overflow fixture is ill-typed"
    match compiled.runStateful 10000 with
    | .done (.inLeft _ (.word reason)) _ => require (reason == Memory.overflowReason) "wrong overflow reason"
    | other => throw (IO.userError s!"oversized destination accepted: {reprStr other}")
  let largest := program [] 0 (wordModulus - 32)
  require largest.check "largest representable snapshot is ill-typed"
  require (← decoded (largest.runStateful 10000)).isEmpty "empty largest snapshot changed contents"

private def onceAndResumeTests : IO Unit := do
  let mapping := Memory.packBytes ((List.range 65).map UInt8.ofNat)
  let tick (value : Solcore.Core.Expr) := Solcore.Core.Expr.letE
    (.storeCell (.var 0) (.binary .wordAdd (.loadCell (.var 0)) (number 1))) (value.weakenAt 0)
  let once : Program := {
    dataDefinitions := MemorySnapshot.definitions
    resultType := .product (LanguageResult.resultType WordMapping.type) .word
    body := .letE (.newCell .word (number 0))
      (.letE (MemorySnapshot.extract (tick (WordMapping.literal mapping)) (tick (number 32)) (tick (number 33)))
        (.pair (.var 0) (.loadCell (.var 1))))
  }
  require once.check "once-only inputs fixture is ill-typed"
  match once.runStateful 100000 with
  | .done (.pair (.inRight _ _) (.word count)) _ => require (count == word 3) "snapshot repeated an input"
  | other => throw (IO.userError s!"once-only inputs failed: {reprStr other}")
  let large := (List.range 320).map fun index => (word index, word (index + 1))
  let compiled := program large 0 10240
  require compiled.check "linear snapshot fixture is ill-typed"
  let expected := WordMapping.encode large
  match compiled.runStateful 100000 with
  | .done (.inRight _ value) _ => require (value == expected) "linear snapshot changed values"
  | other => throw (IO.userError s!"10 KiB aligned snapshot exceeded linear fuel budget: {reprStr other}")
  let rec resume : Nat → State → IO StatefulRunResult
    | 0, _ => throw (IO.userError "snapshot repeated-resume budget exhausted")
    | attempts + 1, state => match runStateful 113 state with
      | .outOfFuel next => resume attempts next
      | result => pure result
  match compiled.runStateful 1 with
  | .outOfFuel checkpoint =>
      let actual ← decoded (← resume 1000 checkpoint)
      require (actual == large) "resumed snapshot changed entry order or values"
  | _ => throw (IO.userError "snapshot fixture did not suspend")

def run : IO Unit := do
  rangeTests
  boundaryTests
  onceAndResumeTests
  IO.println "Rust Hull memory snapshot tests passed"
end Tests.RustHullMemorySnapshot
