import Solcore.Test.SourceCompilerFeatureSupport

/-! Public loop values/checkpoints and exact source allocation order use one
cached artifact. Internal native audits retain the generated cyclic loop cells. -/
set_option autoImplicit false
namespace Tests.SourceCompilerLoops
open Solcore Solcore.Frontend Tests.SourceCompilerFeatureSupport

private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := []
  mainSources := [{ path := "main.solc", content := String.intercalate "\n" [
    "function whileCount(start: Word) returns (Word, Word) {",
    "  let remaining: Word = start; let count: Word = 0;",
    "  while (remaining > 0) { remaining = remaining - 1; count = count + 1; }",
    "  return (remaining, count);",
    "}",
    "function forOrder(limit: Word) returns (Word, Word) {",
    "  let count: Word = 0;",
    "  for (let i: Word = 0; limit > i; i = i + 1) {",
    "    count = count + 1; if (i == 1) { continue; } count = count + 10;",
    "  } return (count, limit);",
    "}",
    "function forBreak(limit: Word) returns (Word) {",
    "  let i: Word = 17; for (let i: Word = 0; limit > i; i = i + 1) { break; } return i;",
    "}",
    "function nested() returns (Word) {",
    "  let count: Word = 0; for (let i: Word = 0; 2 > i; i = i + 1) {",
    "    for (let j: Word = 0; 2 > j; j = j + 1) { count = count + 1; }",
    "  } return count;",
    "}",
    "function absentCondition() returns (Word) { let missing: Bool; while (missing) { return 17; } return 0; }",
    "function absentPost() returns (Word) { let missing: Word; for (let i: Word = 0; true; i = missing) { continue; } return 0; }",
    "function absentInitializer() returns (Word) { let missing: Word; for (let i: Word = missing; true; i = i + 1) { break; } return 0; }",
    "function spin() { while (true) { continue; } }"
  ] }]
}

private def expectSuccess (entry : Entry) (arguments : List Value) (expected : Value)
    (cells : List Value) (type : Core.Ty) (loops : Nat) : IO Unit := do
  require ((← entry.run arguments) == expected) "public loop result changed"
  entry.checkCells arguments (cells.map fun value => (.word, some value))
  let complete ← entry.audit arguments
  let observed ← nativeObservation complete
  match observed with
  | .succeeded _ store => checkLoopCells store type loops
  | _ => throw (IO.userError "cached native loop did not finish")
  let pending ← entry.audit arguments 50
  match ← nativeObservation pending with
  | .outOfFuel _ => pure ()
  | _ => throw (IO.userError "native loop audit did not suspend")
  let resumed ← get "native loop resume" (pending.resume 300000)
  require ((← nativeObservation resumed) == observed)
    "loop resume changed its result or complete native store"
  entry.checkResume arguments expected 50

private def testExecution (program : CheckedProgram) : IO Unit := do
  let whileLoop ← compileNamed program "whileCount"
  expectSuccess whileLoop [scalar 3] (.product (scalar 0) (scalar 3))
    [scalar 3, scalar 0, scalar 3] (.product .word .word) 1
  let forLoop ← compileNamed program "forOrder"
  expectSuccess forLoop [scalar 3] (.product (scalar 23) (scalar 3))
    [scalar 3, scalar 23, scalar 3] (.product .word .word) 1
  expectSuccess forLoop [scalar 2] (.product (scalar 12) (scalar 2))
    [scalar 2, scalar 12, scalar 2] (.product .word .word) 1
  expectSuccess (← compileNamed program "forBreak") [scalar 3] (scalar 17)
    [scalar 3, scalar 17, scalar 0] .word 1
  expectSuccess (← compileNamed program "nested") [] (scalar 4)
    [scalar 4, scalar 2, scalar 2, scalar 2] .word 3

private def testFailures (program : CheckedProgram) : IO Unit := do
  for (name, loops) in ([("absentCondition", 1), ("absentPost", 1),
      ("absentInitializer", 0)] : List (String × Nat)) do
    let entry ← compileNamed program name
    let function ← match program.functions.find? (·.declaration == entry.key.declaration) with
      | some function => pure function
      | none => throw (IO.userError "loop declaration disappeared")
    let (node, binder) ← match function.typedBody.nodes.filterMap (fun
        | .expression node => match node.form with
          | .reference "missing" (.local binder) => some (node, binder)
          | _ => none
        | _ => none) with
      | [site] => pure site
      | _ => throw (IO.userError "loop failure lost its unique read occurrence")
    let invocation ← entry.invoke []
    match invocation.outcome with
    | .failed token _ =>
        require (token != Core.Word.zero && decide ((← invocation.diagnostic token) = some {
          error := .uninitializedLocal binder, site := .occurrence node.id.occurrence,
          span := some node.span })) "loop failure lost its exact source diagnostic"
    | _ => throw (IO.userError "loop did not report its failed read")
    let payload : TypeSystem.Ty := if name == "absentCondition" then .bool else .word
    entry.checkCells [] ([(payload, none)] ++
      if name == "absentPost" then [(.word, some (scalar 0))] else [])
    match ← nativeObservation (← entry.audit []) with
    | .failed _ store => checkLoopCells store .word loops
    | _ => throw (IO.userError "native loop failure changed")

private def testSuspension (program : CheckedProgram) : IO Unit := do
  let entry ← compileNamed program "spin"
  let invocation ← entry.invoke [] {executionOptions with executionFuel := 500}
  match invocation.outcome with
  | .outOfFuel checkpoint =>
      match ← checkpoint.resume 500 with
      | .outOfFuel _ => pure ()
      | _ => throw (IO.userError "resumed public spin unexpectedly finished")
  | _ => throw (IO.userError "public spin did not retain its checkpoint")

def run : IO Unit := do
  let program ← get "public loop checking" (checkProgram workspace)
  testExecution program
  testFailures program
  testSuspension program
end Tests.SourceCompilerLoops
