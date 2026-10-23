import Solcore.Frontend.RustHull.ImageComparison
import Solcore.Core.Machine

set_option autoImplicit false
namespace Tests.RustHullImageComparison
open Solcore Core Solcore.Frontend.RustHull
private def require (test : Bool) (label : String) : IO Unit :=
  unless test do throw (IO.userError label)
private def word (value : Nat) : Word := Word.ofNatModulo value
private def program (bytes : List UInt8) (mapping : WordMapping.Entries) (size : Nat)
    (suffix : Bool := false) : Core.Program := {
  body := ImageComparison.compareBytes bytes (WordMapping.literal mapping) (.word (word size)) suffix
  resultType := LanguageResult.resultType .bool
  dataDefinitions := Memory.definitions
}
private def expect (label : String) (source : Core.Program) (expected : Bool) : IO Unit := do
  require source.check s!"{label}: ill typed"
  match source.run 3000000 with
  | .done actual => require (actual == .inRight .word (.bool expected)) s!"{label}: {reprStr actual}"
  | other => throw (IO.userError s!"{label}: {reprStr other}")
def run : IO Unit := do
  let bytes := (List.range 97).map fun index => UInt8.ofNat (index + 3)
  let entries := Memory.packBytes bytes
  expect "exact image" (program bytes entries 97) true
  expect "entry order" (program bytes entries.reverse 97) true
  expect "length mismatch" (program bytes entries 98) false
  expect "argument suffix" (program bytes (Memory.packBytes (bytes ++ [99, 98])) 99 true) true
  expect "short prefix" (program bytes entries 96 true) false
  expect "missing nonzero word" (program bytes [] 97) false
  expect "missing zero words" (program (List.replicate 97 0) [] 97) true
  expect "empty image" (program [] entries 0) true
  expect "outside entries" (program bytes ((word 999, word 1) :: entries) 97) true
  let original := WordMapping.lookupEntries (word 0) entries
  expect "first duplicate wins" (program bytes ((word 0, original) :: (word 0, word 0) :: entries) 97) true
  expect "bad first duplicate" (program bytes ((word 0, word 0) :: entries) 97) false
  let zeros := Memory.packBytes (List.replicate 97 0)
  expect "nonzero extra input" (program (List.replicate 97 0) ((word 0, word 1) :: zeros) 97) false
  expect "ignored partial tail" (program [1] [(word 0, word (2 ^ 248 + 3))] 1) true
  let large := (List.range 24576).map fun index => UInt8.ofNat (index % 251 + 1)
  let big := program large (Memory.packBytes large) 24576
  expect "all deployed-code bitmap buckets" big true
  match big.runStateful 100 with
  | .outOfFuel state => require (runStateful 3000000 state == big.runStateful 3000100) "image comparison resume"
  | _ => throw (IO.userError "expected image comparison suspension")
end Tests.RustHullImageComparison
