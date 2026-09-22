import Solcore

/-! End-to-end checks for the phase-6 runtime call graph. -/

set_option autoImplicit false

namespace Tests.SourceRuntimeCallGraph

open Solcore Solcore.Frontend
open Solcore.Frontend.SourceProgramExecution

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

private def workspace (content : String) : Workspace.RawWorkspace := {
  entry := "main.solc"
  mainSources := [{ path := "main.solc", content }]
  externalLibraries := []
}

private def mainModule : IO Workspace.ModuleId := do
  match Workspace.CanonicalSourcePath.parse "main.solc" with
  | some path => pure { library := .main, path := path.modulePath }
  | none => throw (IO.userError "invalid runtime-call-graph module path")

private def limits (executionFuel : Nat := 512) : Limits := {
  checkingFuel := 4096
  specializationBudget := 32
  stagingFuel := 64
  executionFuel
}

private def word (value : Nat) : Core.Word :=
  Core.Word.ofNatModulo value

private def preservedStore : Core.Store := [
  .bool false,
  .word (word 91),
  .pair (.word (word 4)) (.bool true)
]

private def runNamed (content name : String) (inputs : List Core.Value)
    (executionFuel : Nat := 512) (store : Core.Store := []) :
    IO Core.StatefulRunResult := do
  let moduleId ← mainModule
  match SourceProgramExecution.run (workspace content)
      (Seed.named moduleId name) inputs (limits executionFuel) store with
  | .ok result => pure result
  | .error error => throw (IO.userError
      s!"runtime-call-graph `{name}` failed: {reprStr error}")

private def recursionSource : String := String.intercalate "\n" [
  "function countdown(value: Word) returns (Word) {",
  "  return value == 0 ? 7 : countdown(value - 1);",
  "}",
  "function factorial(value: Word) returns (Word) {",
  "  return value == 0 ? 1 : value * factorial(value - 1);",
  "}"
]

private def testRuntimeRecursion : IO Unit := do
  let countdown ← runNamed recursionSource "countdown" [.word (word 5)]
    512 preservedStore
  assertTrue (decide (countdown = .done (.word (word 7)) preservedStore))
    "runtime countdown changed its value or caller store"
  let factorial ← runNamed recursionSource "factorial" [.word (word 5)]
    512 preservedStore
  assertTrue (decide (factorial = .done (.word (word 120)) preservedStore))
    "runtime factorial did not execute its recursive call graph"
  let exhausted ← runNamed recursionSource "factorial" [.word (word 5)]
    2 preservedStore
  match exhausted with
  | .outOfFuel state =>
      assertTrue (decide (state.store = preservedStore))
        "runtime recursion lost the store when execution fuel expired"
  | result => throw (IO.userError
      s!"low execution fuel did not suspend recursion: {reprStr result}")

private def mutualSource : String := String.intercalate "\n" [
  "function even(value: Word) returns (Bool) {",
  "  return value == 0 ? true : odd(value - 1);",
  "}",
  "function odd(value: Word) returns (Bool) {",
  "  return value == 0 ? false : even(value - 1);",
  "}"
]

private def testMutualRecursion : IO Unit := do
  let evenSix ← runNamed mutualSource "even" [.word (word 6)]
  let oddSeven ← runNamed mutualSource "odd" [.word (word 7)]
  assertTrue (decide (evenSix = .done (.bool true) [] ∧
      oddSeven = .done (.bool true) []))
    "mutually recursive runtime definitions did not share one finite table"

private def closureSource : String := String.intercalate "\n" [
  "function invoke(f: function(Word) returns (Word), value: Word)",
  "    returns (Word) { return f(value); }",
  "function captured(base: Word, value: Word) returns (Word) {",
  "  let add = lam(item: Word) -> Word { return base + item; };",
  "  return invoke(add, value);",
  "}",
  "function multiple(base: Word, value: Word) returns (Word) {",
  "  let add = lam(left: Word, right: Word) -> Word {",
  "    return left + right;",
  "  };",
  "  return add(base, value);",
  "}"
]

private def testLexicalClosures : IO Unit := do
  let captured ← runNamed closureSource "captured"
    [.word (word 40), .word (word 2)]
  let multiple ← runNamed closureSource "multiple"
    [.word (word 19), .word (word 23)]
  assertTrue (decide (captured = .done (.word (word 42)) [] ∧
      multiple = .done (.word (word 42)) []))
    "lexical capture, higher-order passing, or multi-argument bundling changed"

private def globalValueSource : String := String.intercalate "\n" [
  "function increment(value: Word) returns (Word) { return value + 1; }",
  "function decrement(value: Word) returns (Word) { return value - 1; }",
  "function choose(flag: Bool, value: Word) returns (Word) {",
  "  let selected = flag ? increment : decrement;",
  "  return selected(value);",
  "}"
]

private def testGlobalFunctionValues : IO Unit := do
  let incremented ← runNamed globalValueSource "choose"
    [.bool true, .word (word 41)]
  let decremented ← runNamed globalValueSource "choose"
    [.bool false, .word (word 43)]
  assertTrue (decide (incremented = .done (.word (word 42)) [] ∧
      decremented = .done (.word (word 42)) []))
    "conditional global function references did not remain callable values"

def testSourceRuntimeCallGraph : IO Unit := do
  testRuntimeRecursion
  testMutualRecursion
  testLexicalClosures
  testGlobalFunctionValues
  IO.println "runtime call graph, recursion, and lexical closure checks GREEN"

end Tests.SourceRuntimeCallGraph
