import Solcore.Frontend.SourceCoreFunctionEntry

/-! Real source plans exercise native Integer inputs/results through the
function-value profile, independently of the public compiler adapter. -/

#check_failure Solcore.Frontend.SourceTypedRuntime.run
#check_failure Solcore.Frontend.SourceTypedRuntime.Value

set_option autoImplicit false

namespace Tests.SourceCoreIntegerFunctionEntry

open Solcore Solcore.Frontend
open Solcore.Frontend.SourceCoreFunctionEntry

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

private def word (value : Nat) : Core.Word := Core.Word.ofNatModulo value
private def huge : Int := (2 : Int) ^ 1024 + 17
private def deep (first last : Int) : Core.Value :=
  .pair (.integer first) (.pair (.bool true) (.pair (.word (word 11)) (.integer last)))
private def deepType : Core.Ty :=
  .product .integer (.product .bool (.product .word .integer))
private def present (value : Core.Value) : Core.Value := .inRight .unit value

def workspace : Workspace.RawWorkspace := {
  entry := "main.solc"
  mainSources := [{ path := "main.solc", content := String.intercalate "\n" [
    "function echo(value: integer) returns (integer) { let copied: integer = value; return copied; }",
    "function tree(input: (integer, (Bool, (Word, integer)))) returns (integer, (Bool, (Word, integer))) { return input; }",
    "function replace(input: (integer, (Bool, (Word, integer))), replacement: (integer, (Bool, (Word, integer)))) returns (integer, (Bool, (Word, integer))) {",
    " let saved: (integer, (Bool, (Word, integer))) = input; saved = replacement; return saved; }",
    "function named(value: integer) returns (integer) { return echo(value); }",
    "function shared(value: integer) returns (integer) {",
    " let f: function(integer) returns (integer) = lam(n: integer) -> integer { value = integerAdd(value, n); return value; };",
    " let first: integer = f(2); return f(3); }",
    "function recurse(count: integer, value: integer) returns (integer) {",
    " return integerEq(count, 0) ? value : recurse(integerSub(count, 1), value); }",
    "function absent() returns (integer) { let missing: integer; return missing; }",
    "function calleeFailure() returns (integer) { return absent(); }",
    "function comptimeCompare(comptime value: integer) returns (Bool) { return integerLt(value, 0); }",
    "function stagedEcho(comptime value: integer) returns (integer) { return value; }",
    "function useStaged(value: integer) returns (integer) { return stagedEcho(value); }",
    "function publicFunction(f: function(integer) returns (integer)) returns (integer) { return f(0); }",
    "function make() returns (function(integer) returns (integer)) { return lam(n: integer) -> integer { return n; }; }"
  ] }]
  externalLibraries := []
}

private def request (program : CheckedProgram) (name : String) : IO SourceSpecializationWorklist.Request := do
  match program.signatures.functions.filter (·.name == name) with
  | [signature] => pure { declaration := signature.id, parameterSubstitution := [] }
  | _ => throw (IO.userError s!"Integer source fixture missing: {name}")

private def plan (program : CheckedProgram) (names : List String) : IO Plan := do
  let requests ← names.mapM (request program)
  match SourceSpecializationWorklist.run program requests 100 with
  | .ok (.complete plan) => pure plan
  | result => throw (IO.userError s!"Integer source worklist failed: {reprStr result}")

private def prepared (program : CheckedProgram) (names : List String) : IO PreparedProgram := do
  let input ← plan program names
  match prepare program input 100 Core.Word.zero with
  | .ok compiled => pure compiled
  | .error error => throw (IO.userError s!"Integer source entry preparation failed: {reprStr error}")

private def firstEntry (compiled : PreparedProgram) : IO Entry :=
  match compiled.entries with
  | entry :: _ => pure entry
  | [] => throw (IO.userError "Integer prepared seed missing")

private def execute (entry : Entry) (arguments : List Core.Value) (fuel : Nat := 30000) :
    IO (SourceCoreBasicEntry.Result entry.resultType) := do
  match entry.run arguments fuel with
  | .ok result => pure result
  | .error error => throw (IO.userError s!"Integer source invocation rejected: {reprStr error}")

private def success (entry : Entry) (arguments : List Core.Value) (expected : Core.Value) : IO Core.Store := do
  match (← execute entry arguments).observation with
  | .succeeded value store =>
      assertTrue (value == expected) "Integer source result mismatch"
      pure store
  | result => throw (IO.userError s!"Integer source entry did not succeed: {reprStr result}")

private def testSources (program : CheckedProgram) : IO Unit := do
  let echoCompiled ← prepared program ["echo"]
  let echo ← firstEntry echoCompiled
  assertTrue (echo.resultType == .integer && echo.inputs.map (·.type) == [.integer])
    "integer seed signature was projected through the legacy Word carrier"
  let store ← success echo [.integer (-huge)] (.integer (-huge))
  assertTrue (store[0]? == some (present (.integer (-huge)))) "Integer public input cell changed precision"
  discard <| success echo [.integer huge] (.integer huge)

  let tree ← firstEntry (← prepared program ["tree"])
  assertTrue (tree.resultType == deepType && tree.inputs.map (·.type) == [deepType])
    "deep integer source signature shape changed"
  discard <| success tree [deep (-huge) huge] (deep (-huge) huge)
  let replace ← firstEntry (← prepared program ["replace"])
  let store ← success replace [deep (-huge) huge, deep 9 (-12)] (deep 9 (-12))
  assertTrue (store[0]? == some (present (deep (-huge) huge)))
    "deep integer assignment mutated the input value instead of the local reference"
  discard <| success (← firstEntry (← prepared program ["named"])) [.integer huge] (.integer huge)
  let shared ← firstEntry (← prepared program ["shared"])
  discard <| success shared [.integer (-huge)]
    (.integer (-huge + 5))
  let recursive ← firstEntry (← prepared program ["recurse"])
  discard <| success recursive [.integer 3, .integer huge] (.integer huge)
  let paused ← execute recursive [.integer 3, .integer huge] 15
  let checkpoint ← match paused.checkpoint? with
    | some checkpoint => pure checkpoint
    | none => throw (IO.userError "Integer recursion did not produce a typed checkpoint")
  assertTrue ((checkpoint.resume 30000).observation ==
    (← execute recursive [.integer 3, .integer huge] 30015).observation)
    "integer source recursion checkpoint/resume changed its exact value or store"

private def testFailures (program : CheckedProgram) : IO Unit := do
  let compiled ← prepared program ["calleeFailure"]
  let entry ← firstEntry compiled
  let owner := (← request program "absent").declaration
  let site ← match entry.faultSites.reads.find? (fun site => decide (site.binder.owner = owner)) with
    | some site => pure site
    | none => throw (IO.userError "Integer callee's missing read diagnostic was lost")
  match (← execute entry []).observation with
  | .failed reason store =>
      assertTrue (reason == site.reason && store.any (· == .inLeft .integer .unit))
        "integer uninitialized failure changed its exact token or optional payload type"
      assertTrue (decide (entry.failureDiagnostic? reason = some {
        error := .uninitializedLocal site.binder
        site := .occurrence site.expression.occurrence
        span := some site.span
      })) "Integer callee diagnostic lost its owner, binder or source span"
  | result => throw (IO.userError s!"Integer uninitialized local did not fail: {reprStr result}")

private def testPublicBoundary (program : CheckedProgram) : IO Unit := do
  let staged ← firstEntry (← prepared program ["comptimeCompare"])
  assertTrue (staged.inputs.map (·.comptime) == [true])
    "comptime Integer public seed input marker was discarded"
  discard <| success staged [.integer (-huge)] (.bool true)
  discard <| success staged [.integer huge] (.bool false)
  let stagedCall ← plan program ["useStaged"]
  match prepare program stagedCall 100 Core.Word.zero with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError "internal comptime Integer call was silently moved to runtime")
  let tree ← firstEntry (← prepared program ["tree"])
  match tree.start [deep 1 2] [.integer 3] with
  | .error (.initialStoreUnsupported 1) => pure ()
  | _ => throw (IO.userError "Integer source entry accepted a supplied initial store")
  match tree.start [.pair (.integer 1) (.pair (.bool true) (.pair (.word (word 11)) (.bool false)))] with
  | .error (.inputTypeMismatch 0 _ _) => pure ()
  | _ => throw (IO.userError "Integer source entry accepted the wrong deep leaf type")
  for leaf in ([
      .cellRef .integer 999999,
      .closure .unit .integer (.integer 0) [.cellRef .integer 999999],
      .hostFunction .storageRead] : List Core.Value) do
    let invalid : Core.Value := .pair (.integer 1) (.pair (.bool true) (.pair (.word (word 11)) leaf))
    match tree.start [invalid] with
    | .error (.inputShape 0 _) => pure ()
    | _ => throw (IO.userError "Integer source entry accepted a deep external capability")
  let input ← plan program ["publicFunction"]
  match prepare program input 100 Core.Word.zero with
  | .error (.entry (.lowering (.typeProjection { reason := .unsupportedType (.function _ _), .. }))) => pure ()
  | result => throw (IO.userError s!"Integer public function input was accepted: {reprStr result}")
  let input ← plan program ["make"]
  match prepare program input 100 Core.Word.zero with
  | .error (.lowering (.typeProjection { reason := .unsupportedType (.function _ _), .. })) => pure ()
  | result => throw (IO.userError s!"Integer public function output was accepted: {reprStr result}")

def run : IO Unit := do
  let program ← match checkProgram workspace with
    | .ok program => pure program
    | .error errors => throw (IO.userError s!"Integer source fixtures failed checking: {reprStr errors}")
  testSources program
  testFailures program
  testPublicBoundary program

end Tests.SourceCoreIntegerFunctionEntry
