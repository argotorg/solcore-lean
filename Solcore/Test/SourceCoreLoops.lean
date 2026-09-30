import Solcore.Frontend.SourceCoreLoops
import Solcore.Frontend.SourceCoreFaultSites
import Solcore.Frontend.SourceCoreBasicEntry
import Solcore.Core.BoundedSafety

/-! Checked source while/for fixtures execute generated Core. Native stores are
checked with explicit administrative-cell positions; source heap correspondence
for those extra cells is not assumed. -/

#check_failure Solcore.Frontend.SourceTypedRuntime.run
#check_failure Solcore.Frontend.SourceTypedRuntime.Value

set_option autoImplicit false

namespace Tests.SourceCoreLoops

open Solcore Solcore.Frontend Solcore.Frontend.SourceInference

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
    "  while (remaining > 0) { let copy: Word = remaining; remaining = remaining - 1; count = count + 1; }",
    "  return (remaining, count);",
    "}",
    "function forOrder(limit: Word) returns (Word, Word) {",
    "  let count: Word = 0;",
    "  for (let i: Word = 0; limit > i; i = i + 1) {",
    "    count = count + 1; if (i == 1) { continue; } count = count + 10;",
    "  } return (count, limit);",
    "}",
    "function forBreak(limit: Word) returns (Word) {",
    "  let count: Word = 0; for (let i: Word = 0; limit > i; i = i + 1) { count = count + 1; break; }",
    "  return count;",
    "}",
    "function initializerScope(limit: Word) returns (Word) {",
    "  let i: Word = 17; for (let i: Word = 0; limit > i; i = i + 1) { } return i;",
    "}",
    "function postScope(limit: Word) returns (Word) {",
    "  let copy: Word = 99;",
    "  for (let i: Word = 0; limit > i; let copy: Word = i, i = copy + 1) { } return copy;",
    "}",
    "function nested() returns (Word, Word) {",
    "  let outer: Word = 2; let count: Word = 0; while (outer > 0) {",
    "    let inner: Word = 2; while (inner > 0) {",
    "      inner = inner - 1; if (inner == 1) { continue; } count = count + 1; break;",
    "    } outer = outer - 1;",
    "  } return (count, outer);",
    "}",
    "function returnInside(limit: Word) returns (Word) {",
    "  let remaining: Word = limit; while (remaining > 0) { return remaining; } return 0;",
    "}",
    "function absentCondition() returns (Word) { let missing: Bool; while (missing) { return 17; } return 0; }",
    "function absentPost() returns (Word) { let missing: Word; for (let i: Word = 0; true; i = missing) { continue; } return 0; }",
    "function absentInitializer() returns (Word) { let missing: Word; for (let i: Word = missing; true; i = i + 1) { break; } return 0; }",
    "function spin() { while (true) { continue; } }",
    "function compound(limit: Word) { for (let i: Word = 0; limit > i; i += 1) { } }"
  ] }]
}

private def named (program : CheckedProgram) (name : String) : IO CheckedFunction := do
  match program.functions.find? (fun function =>
    match program.environment.declaration? function.declaration with
    | some declaration => declaration.name == some name
    | none => false) with
  | some function => pure function
  | none => throw (IO.userError s!"missing loop fixture {name}")

private def roots (source : TypedSource) : IO (List StatementId) :=
  source.roots.mapM fun
    | .statement id => pure id
    | _ => throw (IO.userError "expected loop statement roots")

private def inputScope (source : TypedSource) : IO SourceCoreLoops.Scope :=
  source.inputs.foldlM (fun scope binder => do
    match SourceCoreBasic.lowerBinder source scope binder with
    | .ok type => pure ((binder.id, type) :: scope)
    | .error error => throw (IO.userError s!"loop input rejected: {reprStr error}")) []

private structure Compiled where
  function : CheckedFunction
  scope : SourceCoreLoops.Scope
  type : Core.Ty
  body : Core.Expr
  sites : SourceCoreFaultSites.Table

private def compile (function : CheckedFunction) (type : Core.Ty) : IO Compiled := do
  let scope ← inputScope function.typedBody
  let sites ← match SourceCoreFaultSites.prepare function.typedBody function.inferredBodyType with
    | .ok sites => pure sites
    | .error error => throw (IO.userError s!"loop fault table rejected: {reprStr error}")
  let body ← match SourceCoreLoops.lowerStatementsWithReasons 100
      ⟨function.solvedRequirements⟩ function.typedBody scope (← roots function.typedBody)
      type sites.reasonAt Core.Word.zero sites.escapedReason with
    | .ok body => pure body
    | .error error => throw (IO.userError s!"loop lowering rejected: {reprStr error}")
  assertTrue (decide (Core.infer? (SourceCoreLocalCell.coreContext scope) body =
    some (Core.LanguageResult.resultType type))) "generated loop body failed Core type checking"
  pure { function, scope, type, body, sites }

private def start (compiled : Compiled) (arguments : List Core.Value) : IO Core.State := do
  let inputs := compiled.scope.reverse
  assertTrue (inputs.length == arguments.length) "loop input arity mismatch"
  let store := arguments.map present
  let environment := (inputs.zipIdx.map fun ((_, type), index) =>
    Core.Value.cellRef (Core.OptionalCell.cellType type) index).reverse
  pure (.initial compiled.body environment store)

private def checkStore (compiled : Compiled) (store : Core.Store)
    (ordinary : List (Nat × Core.Value)) (administrative : List Nat) (length : Nat) : IO Unit := do
  assertTrue (store.length == length) "loop allocation count changed"
  for (index, expected) in ordinary do
    assertTrue (store[index]? == some expected) s!"loop binding at {index} changed"
  for index in administrative do
    match store[index]? with
    | some (.inRight .unit (.closure .unit _ _ captured)) =>
        assertTrue (captured[0]? == some
          (.cellRef (Core.OptionalCell.cellType (Core.LocalLoop.functionType compiled.type)) index))
          "administrative closure lost its self reference"
    | _ => throw (IO.userError "expected installed optional-function cell")

private def expectSuccess (compiled : Compiled) (arguments : List Core.Value) (expected : Core.Value)
    (ordinary : List (Nat × Core.Value)) (administrative : List Nat) (length : Nat) : IO Unit := do
  let initial ← start compiled arguments
  match Core.runStateful 12000 initial with
  | .done (.inRight .word value) store =>
      assertTrue (value == expected) "loop result or control transfer changed"
      checkStore compiled store ordinary administrative length
      match Core.runStateful 50 initial with
      | .outOfFuel checkpoint =>
          assertTrue (Core.runStateful 11950 checkpoint == .done (.inRight .word expected) store)
            "loop checkpoint resumption changed result or shared heap"
      | _ => throw (IO.userError "loop fixture must retain a checkpoint at fuel 50")
  | result => throw (IO.userError s!"loop did not complete successfully: {reprStr result}")

private def testExecution (program : CheckedProgram) : IO Unit := do
  expectSuccess (← compile (← named program "whileCount") (.product .word .word)) [scalar 3]
    (.pair (scalar 0) (scalar 3))
    [(0, present (scalar 3)), (1, present (scalar 0)), (2, present (scalar 3)),
      (4, present (scalar 3)), (5, present (scalar 2)), (6, present (scalar 1))] [3] 7
  expectSuccess (← compile (← named program "forOrder") (.product .word .word)) [scalar 3]
    (.pair (scalar 23) (scalar 3))
    [(0, present (scalar 3)), (1, present (scalar 23)), (2, present (scalar 3))] [3] 4
  expectSuccess (← compile (← named program "forBreak") .word) [scalar 3] (scalar 1)
    [(0, present (scalar 3)), (1, present (scalar 1)), (2, present (scalar 0))] [3] 4
  expectSuccess (← compile (← named program "initializerScope") .word) [scalar 2] (scalar 17)
    [(0, present (scalar 2)), (1, present (scalar 17)), (2, present (scalar 2))] [3] 4
  expectSuccess (← compile (← named program "postScope") .word) [scalar 3] (scalar 99)
    [(0, present (scalar 3)), (1, present (scalar 99)), (2, present (scalar 3)),
      (4, present (scalar 0)), (5, present (scalar 1)), (6, present (scalar 2))] [3] 7
  expectSuccess (← compile (← named program "nested") (.product .word .word)) []
    (.pair (scalar 2) (scalar 0))
    [(0, present (scalar 0)), (1, present (scalar 2)), (3, present (scalar 0)), (5, present (scalar 0))]
    [2, 4, 6] 7
  expectSuccess (← compile (← named program "returnInside") .word) [scalar 3] (scalar 3)
    [(0, present (scalar 3)), (1, present (scalar 3))] [2] 3

private def testFailure (program : CheckedProgram) (name : String)
    (ordinary : List (Nat × Core.Value)) (administrative : List Nat) (length : Nat) : IO Unit := do
  let compiled ← compile (← named program name) .word
  let missing ← match compiled.sites.reads.find? (fun site =>
      compiled.function.typedBody.nodes.any fun
        | .expression node => node.id == site.expression &&
          match node.form with
          | .reference "missing" (.local _) => true
          | _ => false
        | _ => false) with
    | some site => pure site
    | none => throw (IO.userError "missing precise loop read site")
  match Core.runStateful 12000 (← start compiled []) with
  | .done (.inLeft .word (.word code)) store =>
      assertTrue (code == missing.reason) "loop failure lost the exact read reason"
      match compiled.sites.diagnostic? code with
      | some diagnostic =>
          assertTrue (diagnostic.error == .uninitializedLocal missing.binder &&
            diagnostic.site == .occurrence missing.expression.occurrence &&
            diagnostic.span == some missing.span) "loop failure diagnostic changed"
      | none => throw (IO.userError "missing loop failure diagnostic")
      checkStore compiled store ordinary administrative length
  | result => throw (IO.userError s!"loop failure not retained: {reprStr result}")

private def testBoundaries (program : CheckedProgram) : IO Unit := do
  let spin ← compile (← named program "spin") .unit
  match Core.runStateful 500 (← start spin []) with
  | .outOfFuel checkpoint =>
      match Core.runStateful 500 checkpoint with
      | .outOfFuel _ => pure ()
      | _ => throw (IO.userError "resumed source spin should still suspend")
  | _ => throw (IO.userError "source spin should suspend without a machine fault")
  let compound ← named program "compound"
  let scope ← inputScope compound.typedBody
  match SourceCoreLoops.lowerStatements 100 ⟨compound.solvedRequirements⟩ compound.typedBody scope
      (← roots compound.typedBody) .unit (word 1) Core.Word.zero (word 2) with
  | .error (.unsupportedAssignmentOperator .add) => pure ()
  | result => throw (IO.userError s!"compound assignment profile changed: {reprStr result}")

private def preparedEntry (program : CheckedProgram) (name : String) :
    IO SourceCoreBasicEntry.Entry := do
  let signature ← match program.signatures.functions.filter (·.name == name) with
    | [signature] => pure signature
    | _ => throw (IO.userError s!"prepared loop fixture missing: {name}")
  let plan ← match SourceSpecializationWorklist.run program
      [{ declaration := signature.id, parameterSubstitution := [] }] 100 with
    | .ok (.complete plan) => pure plan
    | result => throw (IO.userError s!"prepared loop worklist failed: {reprStr result}")
  let prepared ← match SourceCoreBasicEntry.prepare program plan 100 (word 91) with
    | .ok prepared => pure prepared
    | .error error => throw (IO.userError s!"prepared loop lowering failed: {reprStr error}")
  match prepared.entries with
  | [entry] => pure entry
  | _ => throw (IO.userError "prepared loop seed order changed")

private def invoke (entry : SourceCoreBasicEntry.Entry) (arguments : List Core.Value)
    (fuel : Nat := 12000) : IO (SourceCoreBasicEntry.Result entry.resultType) := do
  match entry.run arguments fuel with
  | .ok result => pure result
  | .error error => throw (IO.userError s!"prepared loop invocation rejected: {reprStr error}")

private def testPreparedEntry (program : CheckedProgram) : IO Unit := do
  for (name, arguments, expected, length) in ([
      ("forOrder", [scalar 3], Core.Value.pair (scalar 23) (scalar 3), 4),
      ("initializerScope", [scalar 2], scalar 17, 4),
      ("nested", [], .pair (scalar 2) (scalar 0), 7)] :
      List (String × List Core.Value × Core.Value × Nat)) do
    let entry ← preparedEntry program name
    let completed ← invoke entry arguments
    match completed.observation with
    | .succeeded value store =>
        assertTrue (value == expected && store.length == length)
          "prepared loop changed scope, result or administrative allocations"
    | result => throw (IO.userError s!"prepared loop failed: {reprStr result}")
    let paused ← invoke entry arguments 50
    let checkpoint ← match paused.checkpoint? with
      | some checkpoint => pure checkpoint
      | none => throw (IO.userError "prepared loop must retain a typed checkpoint")
    assertTrue ((checkpoint.resume 11950).observation == completed.observation)
      "prepared loop resumption changed result or shared heap"
  let order ← preparedEntry program "forOrder"
  match (← invoke order [scalar 2]).observation with
  | .succeeded value store =>
      assertTrue (value == .pair (scalar 12) (scalar 2) &&
        store[0]? == some (present (scalar 2)) && store[2]? == some (present (scalar 2)))
        "reusing prepared loop code must allocate a fresh invocation frame"
  | result => throw (IO.userError s!"prepared loop reuse failed: {reprStr result}")
  for name in ["absentCondition", "absentPost", "absentInitializer"] do
    let entry ← preparedEntry program name
    let function ← named program name
    let missing ← match entry.faultSites.reads.find? (fun site =>
        function.typedBody.nodes.any fun
          | .expression node => node.id == site.expression &&
            match node.form with
            | .reference "missing" (.local _) => true
            | _ => false
          | _ => false) with
      | some site => pure site
      | none => throw (IO.userError "prepared loop lost its precise failing read")
    match (← invoke entry []).observation with
    | .failed token _ =>
        assertTrue (token == missing.reason) "prepared loop failure lost its reason"
        assertTrue (decide (entry.failureDiagnostic? token = some {
            error := .uninitializedLocal missing.binder,
            site := .occurrence missing.expression.occurrence, span := some missing.span }))
          "prepared loop failure lost its source binder, occurrence or span"
    | result => throw (IO.userError s!"prepared loop did not retain failure: {reprStr result}")
  let spin ← preparedEntry program "spin"
  let suspended ← invoke spin [] 500
  match suspended.checkpoint? with
  | some checkpoint =>
      match (checkpoint.resume 500).checkpoint? with
      | some _ => pure ()
      | none => throw (IO.userError "resumed prepared spin must still suspend")
  | none => throw (IO.userError "prepared spin must suspend without an internal fault")

def run : IO Unit := do
  let program ← match checkProgram workspace with
    | .ok program => pure program
    | .error errors => throw (IO.userError s!"loop source fixtures failed checking: {reprStr errors}")
  testExecution program
  testFailure program "absentCondition" [(0, .inLeft .bool .unit)] [1] 2
  testFailure program "absentPost" [(0, .inLeft .word .unit), (1, present (scalar 0))] [2] 3
  testFailure program "absentInitializer" [(0, .inLeft .word .unit)] [] 1
  testBoundaries program
  testPreparedEntry program

end Tests.SourceCoreLoops
