import Solcore.Frontend.SourceCompiler

/-! Public automatic and explicit Core compilation use ordinary Core for the
supported while/for fragment. Native stores include administrative closure cells;
these execution regressions do not assert source heap correspondence for them. -/

set_option autoImplicit false

namespace Tests.SourceCompilerLoops

open Solcore Solcore.Frontend Solcore.Frontend.SourceCompiler

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

private def word (value : Nat) : Core.Word := Core.Word.ofNatModulo value
private def scalar (value : Nat) : Core.Value := .word (word value)
private def present (value : Core.Value) : Core.Value := .inRight .unit value

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

private def execution : RunOptions := { executionFuel := 12000 }

private def compileNamed (program : CheckedProgram) (name : String)
    (preference : BackendPreference) : IO CompiledEntry := do
  let signature ← match program.signatures.functions.filter (·.name == name) with
    | [signature] => pure signature
    | _ => throw (IO.userError s!"public loop fixture missing: {name}")
  match compileChecked program (.declaration signature.id []) {
      specializationBudget := 64, stagingFuel := 128, backendPreference := preference } with
  | .ok compiled =>
      assertTrue (compiled.backend == .core) "supported source loop did not select Core"
      pure compiled
  | .error error => throw (IO.userError s!"public loop compilation rejected: {reprStr error}")

private def observation (result : Except RunError ExecutionResult) : IO Core.LanguageResult.Observation := do
  match result with
  | .ok (.coreLanguageResult value) => pure value
  | result => throw (IO.userError s!"public loop lost its Core language result: {reprStr result}")

private def expectSuccess (compiled : CompiledEntry) (arguments : List Core.Value)
    (expected : Core.Value) (ordinary : List (Nat × Core.Value))
    (administrative : List Nat) (length : Nat) : IO Unit := do
  let completed ← observation (compiled.runCore arguments execution)
  match completed with
  | .succeeded value store =>
      assertTrue (value == expected && store.length == length)
        "public loop changed result or allocation count"
      for (index, value) in ordinary do
        assertTrue (store[index]? == some value) s!"public loop shared cell {index} changed"
      for index in administrative do
        match store[index]? with
        | some (.inRight .unit (.closure .unit resultType _ captured)) =>
            assertTrue (captured[0]? == some (.cellRef
                (Core.OptionalCell.cellType (.function .unit resultType)) index))
              "public loop closure lost its cyclic self reference"
        | _ => throw (IO.userError "public loop lost its administrative closure cell")
  | result => throw (IO.userError s!"public loop failed: {reprStr result}")
  match ← observation (compiled.runCore arguments { execution with executionFuel := 50 }) with
  | .outOfFuel checkpoint =>
      assertTrue (Core.LanguageResult.observeResult (Core.runStateful 11950 checkpoint) == completed)
        "public loop resumption changed result or complete native store"
  | result => throw (IO.userError s!"public loop lost its resumable checkpoint: {reprStr result}")

private def testExecution (program : CheckedProgram) (preference : BackendPreference) : IO Unit := do
  let whileLoop ← compileNamed program "whileCount" preference
  expectSuccess whileLoop [scalar 3] (.pair (scalar 0) (scalar 3))
    [(0, present (scalar 3)), (1, present (scalar 0)), (2, present (scalar 3))] [3] 4
  let forLoop ← compileNamed program "forOrder" preference
  expectSuccess forLoop [scalar 3] (.pair (scalar 23) (scalar 3))
    [(0, present (scalar 3)), (1, present (scalar 23)), (2, present (scalar 3))] [3] 4
  expectSuccess forLoop [scalar 2] (.pair (scalar 12) (scalar 2))
    [(0, present (scalar 2)), (1, present (scalar 12)), (2, present (scalar 2))] [3] 4
  expectSuccess (← compileNamed program "forBreak" preference) [scalar 3] (scalar 17)
    [(0, present (scalar 3)), (1, present (scalar 17)), (2, present (scalar 0))] [3] 4
  expectSuccess (← compileNamed program "nested" preference) [] (scalar 4)
    [(0, present (scalar 4)), (1, present (scalar 2)),
      (3, present (scalar 2)), (5, present (scalar 2))] [2, 4, 6] 7

private def testFailures (program : CheckedProgram) (preference : BackendPreference) : IO Unit := do
  for (name, ordinaryCount, length) in ([
      ("absentCondition", 1, 2), ("absentPost", 2, 3), ("absentInitializer", 1, 1)] :
      List (String × Nat × Nat)) do
    let compiled ← compileNamed program name preference
    let function ← match program.functions.find? (·.declaration == compiled.key.declaration) with
      | some function => pure function
      | none => throw (IO.userError "public loop declaration disappeared")
    let (node, binder) ← match function.typedBody.nodes.filterMap (fun
        | .expression node => match node.form with
          | .reference "missing" (.local binder) => some (node, binder)
          | _ => none
        | _ => none) with
      | [site] => pure site
      | _ => throw (IO.userError "public loop failure lost its unique read occurrence")
    match ← observation (compiled.runCore [] execution) with
    | .failed token store =>
        let payloadTy : Core.Ty := if name == "absentCondition" then .bool else .word
        assertTrue (token != Core.Word.zero && store.length == length &&
          store[0]? == some (.inLeft payloadTy .unit))
          "public loop failure changed its reason or uninitialized cell"
        if ordinaryCount == 2 then
          assertTrue (store[1]? == some (present (scalar 0)))
            "failed for post changed the initialized induction cell"
        assertTrue (decide (compiled.coreFailureDiagnostic? token = some {
            error := .uninitializedLocal binder, site := .occurrence node.id.occurrence,
            span := some node.span })) "public loop failure lost its exact source diagnostic"
    | result => throw (IO.userError s!"public loop failed to report its read: {reprStr result}")

private def testSuspension (program : CheckedProgram) (preference : BackendPreference) : IO Unit := do
  let compiled ← compileNamed program "spin" preference
  match ← observation (compiled.runCore [] { execution with executionFuel := 500 }) with
  | .outOfFuel checkpoint =>
      match Core.LanguageResult.observeResult (Core.runStateful 500 checkpoint) with
      | .outOfFuel _ => pure ()
      | result => throw (IO.userError s!"resumed public spin unexpectedly finished: {reprStr result}")
  | result => throw (IO.userError s!"public spin did not retain its checkpoint: {reprStr result}")

def run : IO Unit := do
  let program ← match checkProgram workspace with
    | .ok program => pure program
    | .error errors => throw (IO.userError s!"public loop fixtures failed checking: {reprStr errors}")
  for preference in [BackendPreference.automatic, .core] do
    testExecution program preference
    testFailures program preference
    testSuspension program preference

end Tests.SourceCompilerLoops
