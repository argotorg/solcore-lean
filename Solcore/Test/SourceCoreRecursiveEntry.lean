import Solcore.Frontend.SourceCoreRecursiveEntry

#check_failure Solcore.Frontend.SourceTypedRuntime.run
#check_failure Solcore.Frontend.SourceTypedRuntime.Value

set_option autoImplicit false

namespace Tests.SourceCoreRecursiveEntry

open Solcore Solcore.Frontend Solcore.Frontend.SourceInference
open SourceCoreRecursiveEntry

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

private def word (value : Nat) : Core.Word := Core.Word.ofNatModulo value
private def scalar (value : Nat) : Core.Value := .word (word value)
private def present (value : Core.Value) : Core.Value := .inRight .unit value

private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := []
  mainSources := [{ path := "main.solc", content := String.intercalate "\n" [
    "function countdown(n: Word) returns (Word) { return n == 0 ? n : countdown(n - 1); }",
    "function even(n: Word) returns (Bool) { return n == 0 ? true : odd(n - 1); }",
    "function odd(n: Word) returns (Bool) { return n == 0 ? false : even(n - 1); }",
    "function positive(n: Word) returns (Bool) { return n > 0; }",
    "function decrement(n: Word) returns (Word) { return n - 1; }",
    "function spin() returns (Word) { return spin(); }",
    "function sumDown(n: Word) returns (Word) {",
    "  let total: Word = 0; while (positive(n)) { total = total + n; n = decrement(n); } return total;",
    "}",
    "function useLoop(n: Word) returns (Word) { return sumDown(n) + 1; }",
    "function zero() returns (Word) { return 7; }",
    "function increment(value: Word) returns (Word) { let next: Word = value + 1; return next; }",
    "function combine(a: Word, b: Word, c: Word) returns (Word) { return a + b + c; }",
    "function nested(value: Word) returns (Word) { return combine(zero(), increment(value), value) * 2; }",
    "function echoProduct(value: (Word, Bool)) returns (Word, Bool) { return value; }",
    "function productCall(value: Word) returns (Word, Bool) { return echoProduct((value, true)); }",
    "function failLeft() returns (Word) { let absent: Word; return absent; }",
    "function failRight() returns (Word) { let absent: Word; return absent; }",
    "function add(left: Word, right: Word) returns (Word) { return left + right; }",
    "function chooseFailure(flag: Bool) returns (Word) { return flag ? add(failLeft(), failRight()) : add(1, failRight()); }",
    "function leftValue() returns (Word) { let mark: Word = 31; return mark; }",
    "function rightValue() returns (Word) { let mark: Word = 47; return mark; }",
    "function ordered() returns (Word) { return add(leftValue(), rightValue()); }",
    "function empty() { }",
    "function staged(comptime value: Word) returns (Word) { return value; }",
    "function stagedResult(value: Word) returns (comptime<Word>) { return 1; }"
  ] }]
}

private def request (program : CheckedProgram) (name : String) : IO SourceSpecializationWorklist.Request := do
  match program.signatures.functions.filter (·.name == name) with
  | [signature] => pure { declaration := signature.id, parameterSubstitution := [] }
  | _ => throw (IO.userError s!"missing recursive-entry fixture {name}")

private def plan (program : CheckedProgram) (names : List String) : IO Plan := do
  let requests ← names.mapM (request program)
  match SourceSpecializationWorklist.run program requests 100 with
  | .ok (.complete plan) => pure plan
  | result => throw (IO.userError s!"recursive-entry plan failed: {reprStr result}")

private def prepared (program : CheckedProgram) (names : List String) : IO PreparedProgram := do
  let input ← plan program names
  match prepare program input 100 Core.Word.zero with
  | .ok program => pure program
  | .error error => throw (IO.userError s!"recursive-entry preparation failed: {reprStr error}")

private def firstEntry (prepared : PreparedProgram) : IO Entry :=
  match prepared.entries with
  | entry :: _ => pure entry
  | [] => throw (IO.userError "missing prepared entry")

private def execute (entry : Entry) (arguments : List Core.Value) (fuel : Nat := 20000) :
    IO (SourceCoreBasicEntry.Result entry.resultType) := do
  match entry.run arguments fuel with
  | .ok result => pure result
  | .error error => throw (IO.userError s!"prepared invocation rejected: {reprStr error}")

private def success (entry : Entry) (arguments : List Core.Value) (expected : Core.Value) : IO Core.Store := do
  match (← execute entry arguments).observation with
  | .succeeded value store =>
      assertTrue (value == expected) "recursive entry changed its returned value"
      pure store
  | result => throw (IO.userError s!"recursive entry did not succeed: {reprStr result}")

private def testRecursion (program : CheckedProgram) : IO Unit := do
  let selfProgram ← prepared program ["countdown"]
  let selfEntry ← firstEntry selfProgram
  let store ← success selfEntry [scalar 4] (scalar 0)
  assertTrue (store.drop (selfEntry.inputs.length + selfProgram.plan.specializations.length) ==
      [present (scalar 4), present (scalar 3), present (scalar 2), present (scalar 1), present (scalar 0)])
    "recursive source parameters were not allocated in invocation order"
  -- The same checked code is reused for another invocation.
  discard <| success selfEntry [scalar 1] (scalar 0)
  let suspended ← execute selfEntry [scalar 6] 10
  let checkpoint ← match suspended.checkpoint? with
    | some checkpoint => pure checkpoint
    | none => throw (IO.userError "recursive entry did not suspend on small fuel")
  let resumed := checkpoint.resume 20000
  let uninterrupted ← execute selfEntry [scalar 6] 20010
  assertTrue (resumed.observation == uninterrupted.observation) "checkpoint resumption changed the exact result/store"
  let mutualProgram ← prepared program ["even", "odd", "even"]
  assertTrue (mutualProgram.entries.length == 3) "duplicate seed order was lost"
  for (index, input, expected) in [(0, 4, true), (1, 4, false), (2, 3, false)] do
    let entry ← match mutualProgram.entries[index]? with
      | some entry => pure entry
      | none => throw (IO.userError "mutual seed missing")
    let store ← success entry [scalar input] (.bool expected)
    assertTrue (store.length == entry.inputs.length + mutualProgram.plan.specializations.length + input + 1)
      "mutual recursion changed its shared parameter store"

  let diverging ← firstEntry (← prepared program ["spin"])
  let suspended ← execute diverging [] 100
  match suspended.checkpoint? with
  | some checkpoint =>
      match (checkpoint.resume 100).observation with
      | .outOfFuel _ => pure ()
      | _ => throw (IO.userError "unbounded recursion was incorrectly completed")
  | none => throw (IO.userError "unbounded recursion was not represented by a typed checkpoint")

private def testCallsAndLoops (program : CheckedProgram) : IO Unit := do
  let loopEntry ← firstEntry (← prepared program ["useLoop"])
  discard <| success loopEntry [scalar 4] (scalar 11)
  discard <| success loopEntry [scalar 0] (scalar 1)
  let nestedProgram ← prepared program ["nested"]
  let nestedEntry ← firstEntry nestedProgram
  let store ← success nestedEntry [scalar 4] (scalar 32)
  assertTrue (store.drop (nestedEntry.inputs.length + nestedProgram.plan.specializations.length) ==
      [present (scalar 4), present (scalar 4), present (scalar 5),
       present (scalar 7), present (scalar 5), present (scalar 4)])
    "zero/one/three argument calls or mutable local allocation order changed"
  let productProgram ← prepared program ["productCall"]
  let productEntry ← firstEntry productProgram
  let store ← success productEntry [scalar 8] (.pair (scalar 8) (.bool true))
  assertTrue (store.drop (productEntry.inputs.length + productProgram.plan.specializations.length) ==
      [present (scalar 8), present (.pair (scalar 8) (.bool true))])
    "one product argument was split into two parameter cells"
  let orderedProgram ← prepared program ["ordered"]
  let orderedEntry ← firstEntry orderedProgram
  let store ← success orderedEntry [] (scalar 78)
  assertTrue (store.drop orderedProgram.plan.specializations.length ==
      [present (scalar 31), present (scalar 47), present (scalar 31), present (scalar 47)])
    "arguments or callee parameters were not evaluated/allocated in source order"
  let emptyEntry ← firstEntry (← prepared program ["empty"])
  discard <| success emptyEntry [] .unit

private def testDiagnostics (program : CheckedProgram) : IO Unit := do
  let compiled ← prepared program ["chooseFailure"]
  let entry ← firstEntry compiled
  let mut reasons : List Core.Word := []
  for (flag, name) in [(true, "failLeft"), (false, "failRight")] do
    let declaration := (← request program name).declaration
    match (← execute entry [.bool flag]).observation with
    | .failed reason store =>
        let site ← match entry.faultSites.reads.find? (fun site => decide (site.binder.owner = declaration)) with
          | some site => pure site
          | none => throw (IO.userError "callee diagnostic occurrence missing")
        assertTrue (reason == site.reason) "callee failure used another function's token"
        assertTrue (decide (entry.failureDiagnostic? reason = some {
          error := .uninitializedLocal site.binder
          site := .occurrence site.expression.occurrence
          span := some site.span
        })) "callee failure lost its exact binder, occurrence, or span"
        assertTrue (store.drop (entry.inputs.length + compiled.plan.specializations.length) ==
          [present (.bool flag), .inLeft .word .unit])
          "failed argument evaluated another callee or allocated add parameters"
        reasons := reason :: reasons
    | result => throw (IO.userError s!"callee uninitialized read did not fail: {reprStr result}")
  assertTrue (reasons.length == 2 && reasons[0]? != reasons[1]?) "distinct callee failures reused one diagnostic token"
  assertTrue (decide (entry.failureDiagnostic? (word 100000) = none)) "unknown failure token acquired a source location"

private def testBoundaries (program : CheckedProgram) : IO Unit := do
  for name in ["staged", "stagedResult"] do
    let input ← plan program [name]
    match prepare program input 100 Core.Word.zero with
    | .error _ => pure ()
    | .ok _ => throw (IO.userError "staged function entered the ordinary recursive profile")
  let input ← plan program ["countdown"]
  match prepare program { input with callEdges := [] } 100 Core.Word.zero with
  | .error (.preparation _) => pure ()
  | _ => throw (IO.userError "noncanonical recursive plan escaped preparation")
  match prepare program input 0 Core.Word.zero with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError "compilation traversal fuel was ignored")
  let entry ← firstEntry (← prepared program ["countdown"])
  for arguments in [[], [.bool true]] do
    match entry.run arguments 100 with
    | .error _ => pure ()
    | .ok _ => throw (IO.userError "recursive entry accepted malformed inputs")
  match entry.run [scalar 1] 100 [scalar 9] with
  | .error (.initialStoreUnsupported 1) => pure ()
  | _ => throw (IO.userError "recursive entry silently consumed an unsupported initial store")
  let emptyPlan ← plan program []
  match prepare program emptyPlan 100 Core.Word.zero with
  | .ok prepared => assertTrue prepared.entries.isEmpty "empty seed plan created an entry"
  | .error error => throw (IO.userError s!"empty seed plan rejected: {reprStr error}")

def run : IO Unit := do
  let program ← match checkProgram workspace with
    | .ok program => pure program
    | .error errors => throw (IO.userError s!"recursive source fixtures failed: {reprStr errors}")
  testRecursion program
  testCallsAndLoops program
  testDiagnostics program
  testBoundaries program

end Tests.SourceCoreRecursiveEntry
