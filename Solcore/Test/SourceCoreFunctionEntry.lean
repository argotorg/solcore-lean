import Solcore.Frontend.SourceCoreFunctionEntry

#check_failure Solcore.Frontend.SourceTypedRuntime.run
#check_failure Solcore.Frontend.SourceTypedRuntime.Value

set_option autoImplicit false

namespace Tests.SourceCoreFunctionEntry

open Solcore Solcore.Frontend Solcore.Frontend.SourceInference
open SourceCoreFunctionEntry

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

private def word (value : Nat) : Core.Word := Core.Word.ofNatModulo value
private def scalar (value : Nat) : Core.Value := .word (word value)
private def present (value : Core.Value) : Core.Value := .inRight .unit value

private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := []
  mainSources := [{ path := "main.solc", content := String.intercalate "\n" [
    "function inc(value: Word) returns (Word) { return value + 1; }",
    "function consume(f: function(Word) returns (Word), value: Word) returns (Word) { return f(value); }",
    "function named(value: Word) returns (Word) { let f: function(Word) returns (Word) = inc; return consume(f, value); }",
    "function makeAdder(value: Word) returns (function(Word) returns (Word)) {",
    " return lam(delta: Word) -> Word { value = value + delta; return value; }; }",
    "function useReturned(value: Word) returns (Word, Word) {",
    " let f: function(Word) returns (Word) = makeAdder(value); return (f(2), f(3)); }",
    "function shared(value: Word) returns (Word, Word) {",
    " let f: function(Word) returns (Word) = lam(delta: Word) -> Word { value = value + delta; return value; };",
    " let g: function(Word) returns (Word) = lam(delta: Word) -> Word { value = value + delta; return value; }; return (f(2), g(3)); }",
    "function selfCell(value: Word) returns (Word) {",
    " let loop: function(Word) returns (Word);",
    " loop = lam(n: Word) -> Word { return n == 0 ? value : loop(n - 1); }; return loop(3); }",
    "function nestedCapture(value: Word) returns (Word) {",
    " let outer: function(Word) returns (function() returns (Word)) = lam(delta: Word) -> function() returns (Word) {",
    "   return lam() -> Word { return inc(value + delta); }; };",
    " let inner: function() returns (Word) = outer(3); value = 9; return inner(); }",
    "function bounce(count: Word, f: function(Word) returns (Word)) returns (Word) {",
    " return count == 0 ? f(count) : bounce(count - 1, f); }",
    "function useBounce(value: Word) returns (Word) {",
    " let f: function(Word) returns (Word) = lam(n: Word) -> Word { return value + n; }; return bounce(3, f); }",
    "function closureLoop(value: Word) returns (Word) {",
    " let f: function(Word) returns (Word) = lam(n: Word) -> Word {",
    "   while (n > 0) { value = inc(value); n = n - 1; } return value; }; return f(3); }",
    "function failBeforeArgument() returns (Word) {",
    " let f: function(Word) returns (Word); let marker: Word = 0;",
    " let argument: function() returns (Word) = lam() -> Word { marker = 9; return marker; }; return f(argument()); }",
    "function makeFailure() returns (function() returns (Word)) {",
    " let absent: Word; return lam() -> Word { return absent; }; }",
    "function useFailure() returns (Word) { let f: function() returns (Word) = makeFailure(); return f(); }",
    "function pairInput(pair: (Word, Bool)) returns (Word, Bool) { return pair; }",
    "function rejectProduct(pair: (Word, function(Word) returns (Word))) returns (Word) { return 0; }",
    "function staged(comptime value: Word) returns (Word) { return value; }"
  ] }]
}

private def request (program : CheckedProgram) (name : String) : IO SourceSpecializationWorklist.Request := do
  match program.signatures.functions.filter (·.name == name) with
  | [signature] => pure { declaration := signature.id, parameterSubstitution := [] }
  | _ => throw (IO.userError s!"function-entry fixture missing: {name}")

private def plan (program : CheckedProgram) (names : List String) : IO Plan := do
  let requests ← names.mapM (request program)
  match SourceSpecializationWorklist.run program requests 100 with
  | .ok (.complete plan) => pure plan
  | result => throw (IO.userError s!"function-entry worklist failed: {reprStr result}")

private def prepared (program : CheckedProgram) (names : List String) : IO PreparedProgram := do
  let input ← plan program names
  match prepare program input 100 Core.Word.zero with
  | .ok program => pure program
  | .error error => throw (IO.userError s!"function-entry preparation failed: {reprStr error}")

private def firstEntry (prepared : PreparedProgram) : IO Entry :=
  match prepared.entries with
  | entry :: _ => pure entry
  | [] => throw (IO.userError "function-entry seed missing")

private def execute (entry : Entry) (arguments : List Core.Value) (fuel : Nat := 30000) :
    IO (SourceCoreBasicEntry.Result entry.resultType) := do
  match entry.run arguments fuel with
  | .ok result => pure result
  | .error error => throw (IO.userError s!"function-entry invocation rejected: {reprStr error}")

private def success (entry : Entry) (arguments : List Core.Value) (expected : Core.Value) : IO Core.Store := do
  match (← execute entry arguments).observation with
  | .succeeded value store =>
      assertTrue (value == expected) "function-entry result mismatch"
      pure store
  | result => throw (IO.userError s!"function-entry did not succeed: {reprStr result}")

private def testCapturesAndCalls (program : CheckedProgram) : IO Unit := do
  let named ← firstEntry (← prepared program ["named"])
  discard <| success named [scalar 4] (scalar 5)
  discard <| success named [scalar 9] (scalar 10)
  let returnedProgram ← prepared program ["useReturned"]
  let returnedEntry ← firstEntry returnedProgram
  let store ← success returnedEntry [scalar 4] (.pair (scalar 6) (scalar 9))
  let firstSourceCell := returnedEntry.inputs.length + returnedProgram.plan.specializations.length
  assertTrue (store[firstSourceCell]? == some (present (scalar 4))) "returned closure mutated its caller's value copy"
  assertTrue (store[firstSourceCell + 1]? == some (present (scalar 9))) "returned closure did not share its own captured parameter"
  let sharedProgram ← prepared program ["shared"]
  let sharedEntry ← firstEntry sharedProgram
  let store ← success sharedEntry [scalar 4] (.pair (scalar 6) (scalar 9))
  assertTrue (store[sharedEntry.inputs.length + sharedProgram.plan.specializations.length]? == some (present (scalar 9)))
    "two closures copied a mutable capture instead of sharing its cell"
  let nested ← firstEntry (← prepared program ["nestedCapture"])
  discard <| success nested [scalar 4] (scalar 13)
  let loop ← firstEntry (← prepared program ["closureLoop"])
  discard <| success loop [scalar 8] (scalar 11)

private def testRecursionAndResume (program : CheckedProgram) : IO Unit := do
  let compiled ← prepared program ["selfCell", "useBounce", "selfCell"]
  assertTrue (compiled.entries.length == 3) "function-entry duplicate seed order changed"
  for entry in compiled.entries do
    discard <| success entry [scalar 7] (scalar 7)
  let entry ← firstEntry compiled
  let suspended ← execute entry [scalar 7] 15
  let checkpoint ← match suspended.checkpoint? with
    | some checkpoint => pure checkpoint
    | none => throw (IO.userError "closure recursion did not produce a typed checkpoint")
  let resumed := checkpoint.resume 30000
  let uninterrupted ← execute entry [scalar 7] 30015
  assertTrue (resumed.observation == uninterrupted.observation)
    "function-entry checkpoint resumption changed the exact result/store"

private def testFailures (program : CheckedProgram) : IO Unit := do
  let compiled ← prepared program ["failBeforeArgument"]
  let entry ← firstEntry compiled
  match (← execute entry []).observation with
  | .failed reason store =>
      let marker := entry.inputs.length + compiled.plan.specializations.length + 1
      assertTrue (store[marker]? == some (present (scalar 0))) "failed callee evaluated argument side effects"
      assertTrue (decide (entry.failureDiagnostic? reason ≠ none)) "failed function cell lost its diagnostic"
  | result => throw (IO.userError s!"uninitialized function cell did not fail: {reprStr result}")
  let compiled ← prepared program ["useFailure"]
  let entry ← firstEntry compiled
  let owner := (← request program "makeFailure").declaration
  let site ← match entry.faultSites.reads.find? (fun site => decide (site.binder.owner = owner)) with
    | some site => pure site
    | none => throw (IO.userError "returned lambda's captured read site missing")
  match (← execute entry []).observation with
  | .failed reason _ =>
      assertTrue (reason == site.reason) "returned lambda failure used the caller's source token"
      assertTrue (decide (entry.failureDiagnostic? reason = some {
        error := .uninitializedLocal site.binder
        site := .occurrence site.expression.occurrence
        span := some site.span
      })) "returned lambda failure lost its exact original binder/occurrence/span"
  | result => throw (IO.userError s!"returned failing closure did not fail: {reprStr result}")

private def testPublicBoundary (program : CheckedProgram) : IO Unit := do
  for name in ["consume", "rejectProduct"] do
    let input ← plan program [name]
    match prepare program input 100 Core.Word.zero with
    | .error (.entry (.lowering (.typeProjection { reason := .unsupportedType (.function _ _), .. }))) => pure ()
    | result => throw (IO.userError s!"function-valued public input did not receive the explicit projection rejection: {reprStr result}")
  for name in ["makeAdder", "makeFailure"] do
    let input ← plan program [name]
    match prepare program input 100 Core.Word.zero with
    | .error (.lowering (.typeProjection { reason := .unsupportedType (.function _ _), .. })) => pure ()
    | result => throw (IO.userError s!"function-valued public result did not receive the explicit projection rejection: {reprStr result}")
  let pair ← firstEntry (← prepared program ["pairInput"])
  discard <| success pair [.pair (scalar 8) (.bool true)] (.pair (scalar 8) (.bool true))
  match pair.run [.pair (scalar 8) (scalar 1)] 100 with
  | .error (.inputTypeMismatch _ _ _) => pure ()
  | _ => throw (IO.userError "public product input was not deeply validated")
  match pair.run [.pair (scalar 8) (.bool true)] 100 [scalar 2] with
  | .error (.initialStoreUnsupported 1) => pure ()
  | _ => throw (IO.userError "function-entry silently consumed an unsupported initial store")
  let staged ← firstEntry (← prepared program ["staged"])
  assertTrue (staged.inputs.map (·.comptime) == [true])
    "comptime scalar seed input marker was discarded"
  discard <| success staged [scalar 6] (scalar 6)
  let input ← plan program ["named"]
  match prepare program { input with referenceEdges := [] } 100 Core.Word.zero with
  | .error (.preparation _) => pure ()
  | _ => throw (IO.userError "forged named-reference plan escaped canonical preparation")
  match prepare program input 0 Core.Word.zero with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError "function-entry ignored compile traversal exhaustion")

def run : IO Unit := do
  let program ← match checkProgram workspace with
    | .ok program => pure program
    | .error errors => throw (IO.userError s!"function-entry source fixtures failed: {reprStr errors}")
  testCapturesAndCalls program
  testRecursionAndResume program
  testFailures program
  testPublicBoundary program

end Tests.SourceCoreFunctionEntry
