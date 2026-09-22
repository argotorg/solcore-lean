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

private def runNamedExact (content name : String) (inputs : List Core.Value)
    (executionFuel : Nat := 512) (store : Core.Store := []) :
    IO SourceCoreDirectLinking.ExecutionResult := do
  let moduleId ← mainModule
  match SourceProgramExecution.runExact (workspace content)
      (Seed.named moduleId name) inputs (limits executionFuel) store with
  | .ok result => pure result
  | .error error => throw (IO.userError
      s!"exact runtime-call-graph `{name}` failed: {reprStr error}")

private def checkedProgram (content : String) : IO CheckedProgram := do
  match checkProgram (workspace content) with
  | .ok program => pure program
  | .error errors => throw (IO.userError
      s!"runtime-call-graph fixture failed checking: {reprStr errors}")

private def completePlan (program : CheckedProgram) (name : String) :
    IO SourceSpecializationWorklist.Plan := do
  let signature ← match program.signatures.functions.filter
      (fun signature => signature.name == name) with
    | [signature] => pure signature
    | signatures => throw (IO.userError
        s!"expected one signature named `{name}`, found {signatures.length}")
  let request : SourceSpecializationWorklist.Request := {
    declaration := signature.id
    parameterSubstitution := []
  }
  match SourceSpecializationWorklist.run program [request] 32 with
  | .ok (.complete plan) => pure plan
  | .ok outcome => throw (IO.userError
      s!"runtime-call-graph plan did not complete: {reprStr outcome}")
  | .error error => throw (IO.userError
      s!"runtime-call-graph worklist failed: {reprStr error}")

private def recursionSource : String := String.intercalate "\n" [
  "function countdown(value: Word) returns (Word) {",
  "  return value == 0 ? 7 : countdown(value - 1);",
  "}",
  "function factorial(value: Word) returns (Word) {",
  "  return value == 0 ? 1 : value * factorial(value - 1);",
  "}",
  "function indirectCountdown(value: Word) returns (Word) {",
  "  let next = indirectCountdown;",
  "  return value == 0 ? 9 : next(value - 1);",
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
  let indirect ← runNamed recursionSource "indirectCountdown"
    [.word (word 5)] 512 preservedStore
  assertTrue (decide (indirect = .done (.word (word 9)) preservedStore))
    "first-class self reference did not recurse through indirect dispatch"
  let exact ← runNamedExact recursionSource "countdown"
    [.word (word 5)] 512 preservedStore
  match exact with
  | .runtime (.done (.word value) store) =>
      assertTrue (decide (value = word 7 ∧ store = preservedStore))
        "exact graph completion lost its value or store"
  | result => throw (IO.userError
      s!"graph completion used the wrong exact carrier: {reprStr result}")
  let exhausted ← runNamedExact recursionSource "factorial"
    [.word (word 5)] 2 preservedStore
  match exhausted with
  | .runtime (.outOfFuel store) =>
      assertTrue (decide (store = preservedStore))
        "exact graph exhaustion lost the caller store"
  | result => throw (IO.userError
      s!"low graph fuel used a fabricated Core checkpoint: {reprStr result}")

private def modularLiteralSource : String := String.intercalate "\n" [
  "function wrapped(value: Word) returns (Word) {",
  "  return value == 0 ?",
  "    115792089237316195423570985008687907853269984665640564039457584007913129639936 :",
  "    wrapped(value - 1);",
  "}"
]

private def testModularRuntimeLiteral : IO Unit := do
  let result ← runNamed modularLiteralSource "wrapped" [.word (word 1)]
  assertTrue (decide (result = .done (.word Core.Word.zero) []))
    "runtime graph rejected or misdecoded an exactly modular Word literal"

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
  "}",
  "function makeAdder(base: Word)",
  "    returns (function(Word) returns (Word)) {",
  "  return lam(item: Word) -> Word { return base + item; };",
  "}",
  "function returned(base: Word, value: Word) returns (Word) {",
  "  let add = makeAdder(base);",
  "  return add(value);",
  "}"
]

private def testLexicalClosures : IO Unit := do
  let captured ← runNamed closureSource "captured"
    [.word (word 40), .word (word 2)]
  let multiple ← runNamed closureSource "multiple"
    [.word (word 19), .word (word 23)]
  let returned ← runNamed closureSource "returned"
    [.word (word 20), .word (word 22)]
  assertTrue (decide (captured = .done (.word (word 42)) [] ∧
      multiple = .done (.word (word 42)) [] ∧
      returned = .done (.word (word 42)) []))
    "lexical capture, function-valued return, or argument bundling changed"

private def testExactCoreClosureFault : IO Unit := do
  let malformed : Core.Value :=
    .closure .word .word (.var 1) []
  let result ← runNamedExact closureSource "invoke"
    [malformed, .word (word 7)] 128 preservedStore
  match result with
  | .runtime (.fault (.coreFault (.unboundVariable 1)) store) =>
      assertTrue (decide (store = preservedStore))
        "embedded Core fault lost its exact store"
  | other => throw (IO.userError
      s!"embedded Core fault was erased at the exact boundary: {reprStr other}")

private def testForgedCoreClosureResultRejected : IO Unit := do
  let forged : Core.Value :=
    .closure .word .word (.bool true) []
  let result ← runNamedExact closureSource "invoke"
    [forged, .word (word 7)] 128 preservedStore
  match result with
  | .runtime (.fault
      (.resultTypeMismatch .word (some .bool)) store) =>
      assertTrue (decide (store = preservedStore))
        "forged Core closure result rejection lost its exact store"
  | other => throw (IO.userError
      s!"forged Core closure result escaped its declared type: {reprStr other}")

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

private def erasedAritySource : String := String.intercalate "\n" [
  "function packed(pair: (Word, Word)) returns (Word) { return 1; }",
  "function split(left: Word, right: Word) returns (Word) { return 2; }",
  "function choose(flag: Bool, left: Word, right: Word) returns (Word) {",
  "  let selected = flag ? packed : split;",
  "  return selected(left, right);",
  "}"
]

/-- Source arity is not part of a structural function type.  A one-product
parameter function and a two-parameter function can therefore flow through the
same conditional value; the runtime bundle is unpacked for the selected body. -/
private def testErasedSourceArity : IO Unit := do
  let packed ← runNamed erasedAritySource "choose"
    [.bool true, .word (word 20), .word (word 22)]
  let split ← runNamed erasedAritySource "choose"
    [.bool false, .word (word 20), .word (word 22)]
  assertTrue (decide (packed = .done (.word (word 1)) [] ∧
      split = .done (.word (word 2)) []))
    "structurally equal function values did not normalize their argument bundle"

private def erasedUnitAritySource : String := String.intercalate "\n" [
  "function empty() returns (Word) { return 3; }",
  "function unit(value: ()) returns (Word) { return 4; }",
  "function callEmpty(flag: Bool) returns (Word) {",
  "  let selected = flag ? empty : unit;",
  "  return selected();",
  "}",
  "function callUnit(flag: Bool) returns (Word) {",
  "  let selected = flag ? empty : unit;",
  "  return selected(());",
  "}"
]

private def testErasedUnitArity : IO Unit := do
  let emptyWithoutUnit ← runNamed erasedUnitAritySource "callEmpty" [.bool true]
  let unitWithoutUnit ← runNamed erasedUnitAritySource "callEmpty" [.bool false]
  let emptyWithUnit ← runNamed erasedUnitAritySource "callUnit" [.bool true]
  let unitWithUnit ← runNamed erasedUnitAritySource "callUnit" [.bool false]
  assertTrue (decide (
      emptyWithoutUnit = .done (.word (word 3)) [] ∧
      unitWithoutUnit = .done (.word (word 4)) [] ∧
      emptyWithUnit = .done (.word (word 3)) [] ∧
      unitWithUnit = .done (.word (word 4)) []))
    "zero-parameter and one-Unit-parameter functions did not share Unit bundles"

private def changeTrueToFalse : List SourceInference.Node →
    List SourceInference.Node
  | [] => []
  | .expression node :: nodes =>
      let changed := match node.form with
        | .reference name (.builtinBoolean true) =>
            SourceInference.Node.expression {
              node with
              form := .reference name (.builtinBoolean false)
            }
        | _ => .expression node
      changed :: changeTrueToFalse nodes
  | node :: nodes => node :: changeTrueToFalse nodes

private def testTamperedPlanRejected : IO Unit := do
  let program ← checkedProgram
    "function value() returns (Bool) { return true; }"
  let plan ← completePlan program "value"
  let tampered ← match plan.specializations with
    | [specialized] =>
        let changedNodes := changeTrueToFalse
          specialized.function.typedBody.nodes
        if changedNodes == specialized.function.typedBody.nodes then
          throw (IO.userError "tamper fixture did not contain true")
        let changedFunction : SourceInference.CheckedFunction := {
          specialized.function with
          typedBody := {
            specialized.function.typedBody with nodes := changedNodes
          }
        }
        pure ({ plan with specializations := [{
          specialized with function := changedFunction
        }] } : SourceSpecializationWorklist.Plan)
    | specializations => throw (IO.userError
        s!"tamper fixture expected one specialization, found {specializations.length}")
  match SourceRuntimeLinking.link program (.complete tampered) with
  | .error (.invalidPlan (.nonCanonicalSpecialization _)) => pure ()
  | result => throw (IO.userError
      s!"runtime linker accepted an injected specialization body: {reprStr result}")

def testSourceRuntimeCallGraph : IO Unit := do
  testRuntimeRecursion
  testModularRuntimeLiteral
  testMutualRecursion
  testLexicalClosures
  testExactCoreClosureFault
  testForgedCoreClosureResultRejected
  testGlobalFunctionValues
  testErasedSourceArity
  testErasedUnitArity
  testTamperedPlanRejected
  IO.println "runtime call graph, recursion, and lexical closure checks GREEN"

end Tests.SourceRuntimeCallGraph
