import Solcore.Frontend.SourceCoreBasicEntry

/-! Preparation consumes real canonical specialization plans. Invocation checks
Core values without importing the typed-source evaluator or recompiling code. -/

#check_failure Solcore.Frontend.SourceTypedRuntime.Value
#check_failure Solcore.Frontend.SourceTypedRuntime.run

set_option autoImplicit false

namespace Tests.SourceCoreBasicEntry

open Solcore Solcore.Frontend
open Solcore.Frontend.SourceCoreBasicEntry

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

private def word (value : Nat) : Core.Word := Core.Word.ofNatModulo value
private def scalar (value : Nat) : Core.Value := .word (word value)
private def present (value : Core.Value) : Core.Value := .inRight .unit value
private def reason : Core.Word := word 93

private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc"
  mainSources := [{ path := "main.solc", content := String.intercalate "\n" [
    "function mutate(flag: Bool, first: Word, second: Word) returns (Word, Bool) {",
    "  let value: Word; value = first; value = second; return (value, flag);",
    "}",
    "function keep<T>(input: T) returns (T) { let stored: T = input; return stored; }",
    "function absent(input: Word) returns (Word) { let value: Word; return value; }",
    "function staged(comptime input: (Word, Bool)) returns (Word, Bool) {",
    "  let stored: (Word, Bool) = input; return stored;",
    "}",
    "function nested(input: (Word, (Bool, Word))) returns (Word, (Bool, Word)) { return input; }",
    "function blocked(input: Word) returns (Word) { { return input; } }",
    "function scoped(flag: Bool, initial: Word, replacement: Word) returns (Word) {",
    "  let value: Word = initial; { let value: Word = replacement; value = initial; }",
    "  if (flag) { value = replacement; } return value;",
    "}",
    "function branchFailure(flag: Bool) returns (Word) {",
    "  let absent: Word; return flag ? absent : absent;",
    "}",
    "function chooseFailure(flag: Bool, value: Word) returns (Word) {",
    "  let absent: Word; return flag ? value : absent;",
    "}",
    "function loop(flag: Bool) { while (flag) { break; } }",
    "function stagedResult(comptime input: Word) returns (comptime<Word>) { return input; }",
    "function literalEvidence() returns (Word) { return 1; }"
  ] }]
  externalLibraries := []
}

private def request (program : CheckedProgram) (name : String)
    (types : List TypeSystem.Ty := []) : IO SourceSpecializationWorklist.Request := do
  let signature ← match program.signatures.functions.filter (·.name == name) with
    | [signature] => pure signature
    | _ => throw (IO.userError s!"entry fixture not found: {name}")
  assertTrue (signature.scheme.parameters.length == types.length) "specialization arity changed"
  pure { declaration := signature.id, parameterSubstitution := signature.scheme.parameters.zip types }

private def plan (program : CheckedProgram) (requests : List SourceSpecializationWorklist.Request) : IO Plan := do
  match SourceSpecializationWorklist.run program requests 100 with
  | .ok (.complete plan) => pure plan
  | result => throw (IO.userError s!"entry worklist failed: {reprStr result}")

private def preparePlan (program : CheckedProgram) (plan : Plan) : IO PreparedProgram := do
  match prepare program plan 100 reason with
  | .ok prepared => pure prepared
  | .error error => throw (IO.userError s!"entry preparation failed: {reprStr error}")

private def entryAt (prepared : PreparedProgram) (index : Nat) : IO Entry := do
  match prepared.entries[index]? with
  | some entry => pure entry
  | none => throw (IO.userError "prepared seed entry missing")

private def invoke (entry : Entry) (values : List Core.Value) (fuel : Nat := 1000) : IO (Result entry.resultType) := do
  match entry.run values fuel with
  | .ok result => pure result
  | .error error => throw (IO.userError s!"entry invocation rejected: {reprStr error}")

private def testPreparedRuns (program : CheckedProgram) : IO Unit := do
  let mutate ← request program "mutate"
  let keepWord ← request program "keep" [.word]
  let keepProduct ← request program "keep" [.product .word .bool]
  let absent ← request program "absent"
  let staged ← request program "staged"
  let nested ← request program "nested"
  let inputPlan ← plan program [mutate, keepWord, keepProduct, absent, staged, nested, mutate]
  let prepared ← preparePlan program inputPlan
  assertTrue (prepared.entries.map (·.key) == inputPlan.seedKeys)
    "preparation changed canonical seed order or removed duplicate roots"
  assertTrue (prepared.plan.seedKeys == inputPlan.seedKeys)
    "prepared plan changed the public seed catalog"
  let entry ← entryAt prepared 0
  assertTrue (entry.inputs.map (·.type) == [.bool, .word, .word])
    "entry inputs must retain original source parameter order"
  let arguments := [.bool true, scalar 11, scalar 29]
  let initial ← match entry.start arguments with
    | .ok checkpoint => pure checkpoint
    | .error error => throw (IO.userError s!"entry start failed: {reprStr error}")
  assertTrue (initial.state.store == arguments.map present)
    "input allocation must follow source order"
  assertTrue (initial.state.control == .eval entry.body [
      .cellRef (Core.OptionalCell.cellType .word) 2,
      .cellRef (Core.OptionalCell.cellType .word) 1,
      .cellRef (Core.OptionalCell.cellType .bool) 0])
    "prepared environment must use newest-first references without copying the input store"
  let result ← invoke entry arguments
  assertTrue (result.observation == .succeeded (.pair (scalar 29) (.bool true))
      [present (.bool true), present (scalar 11), present (scalar 29), present (scalar 29)])
    "prepared mutation result or shared local cell changed"
  let second ← invoke entry [.bool false, scalar 2, scalar 7]
  assertTrue (second.observation == .succeeded (.pair (scalar 7) (.bool false))
      [present (.bool false), present (scalar 2), present (scalar 7), present (scalar 7)])
    "reusing a cached entry must prepare a fresh input frame"
  let paused ← invoke entry arguments 10
  let checkpoint ← match paused.checkpoint? with
    | some checkpoint => pure checkpoint
    | none => throw (IO.userError "small execution fuel must return a typed checkpoint")
  assertTrue ((checkpoint.resume 990).observation == result.observation)
    "resuming a prepared entry must preserve its values and store"
  let kept ← invoke (← entryAt prepared 1) [scalar 8]
  assertTrue (kept.observation == .succeeded (scalar 8) [present (scalar 8), present (scalar 8)])
    "specialized generic Word input was not compiled through the plan"
  let pair : Core.Value := .pair (scalar 5) (.bool true)
  let keptPair ← invoke (← entryAt prepared 2) [pair]
  assertTrue (keptPair.observation == .succeeded pair [present pair, present pair])
    "specialized generic product input lost its complete structure"
  let absentEntry ← entryAt prepared 3
  let failed ← invoke absentEntry [scalar 3]
  let read ← match absentEntry.faultSites.reads with
    | [site] => pure site
    | _ => throw (IO.userError "uninitialized fixture lost its unique read site")
  assertTrue (read.reason != Core.Word.zero && failed.observation ==
      .failed read.reason [present (scalar 3), .inLeft .word .unit])
    "uninitialized entry local must return a typed language failure"
  assertTrue (decide (absentEntry.failureDiagnostic? read.reason = some {
      error := .uninitializedLocal read.binder, site := .occurrence read.expression.occurrence,
      span := some read.span })) "uninitialized diagnostic lost its source identity"
  let stagedEntry ← entryAt prepared 4
  assertTrue (stagedEntry.inputs.map (·.comptime) == [true]) "comptime input marker was discarded"
  let stagedResult ← invoke stagedEntry [pair]
  assertTrue (stagedResult.observation == .succeeded pair [present pair, present pair])
    "staged scalar/product input must retain its exact value"
  let nestedValue : Core.Value := .pair (scalar 6) (.pair (.bool false) (scalar 12))
  let nestedResult ← invoke (← entryAt prepared 5) [nestedValue]
  assertTrue (nestedResult.observation == .succeeded nestedValue [present nestedValue])
    "deep product input tree was flattened or reordered"
  match prepared.findEntry? entry.key with
  | some found => assertTrue (found.body == entry.body) "findEntry? returned a different prepared body"
  | none => throw (IO.userError "findEntry? lost a retained seed")

private def expectError {α : Type} (label : String) (result : Except Error α)
    (accept : Error → Bool) : IO Unit := do
  match result with
  | .ok _ => throw (IO.userError s!"{label}: invalid boundary input was accepted")
  | .error error => assertTrue (accept error) s!"{label}: wrong error {reprStr error}"

private def testInputRejections (program : CheckedProgram) : IO Unit := do
  let inputPlan ← plan program [← request program "nested"]
  let entry ← entryAt (← preparePlan program inputPlan) 0
  expectError "input count" (entry.start [])
    fun error => error matches .argumentCountMismatch 1 0
  expectError "input structural type" (entry.start [.pair (scalar 1) (.pair (scalar 2) (.bool true))])
    fun error => error matches .inputTypeMismatch 0 _ _
  expectError "nested external cell" (entry.start [.pair (scalar 1) (.pair (.bool true) (.cellRef .word 0))])
    fun error => error matches .inputShape 0 _
  expectError "nested external closure" (entry.start [
    .pair (scalar 1) (.pair (.bool true) (.closure .unit .word (.word (word 0)) []))])
    fun error => error matches .inputShape 0 _
  expectError "sum payload" (entry.start [.inRight .unit (.pair (scalar 1) (.pair (.bool true) (scalar 2)))])
    fun error => error matches .inputShape 0 _
  let valid := [.pair (scalar 1) (.pair (.bool true) (scalar 2))]
  expectError "unsupported initial store" (entry.start valid [.word (word 4)])
    fun error => error matches .initialStoreUnsupported 1

private def testPreparationRejections (program : CheckedProgram) : IO Unit := do
  let valid ← plan program [← request program "mutate"]
  expectError "noncanonical plan" (prepare program { valid with seedKeys := [] } 100 reason)
    fun error => error matches .preparation .nonCanonicalInputPlan
  expectError "compilation fuel" (prepare program valid 0 reason)
    fun error => error matches .lowering (.traversalExhausted _)
  for (name, accepts) in ([
      ("stagedResult", fun error => error matches .stagedResultUnsupported _)] :
      List (String × (Error → Bool))) do
    let input ← plan program [← request program name]
    expectError name (prepare program input 100 reason) accepts

private def prepareNamed (program : CheckedProgram) (name : String) : IO (Plan × Entry) := do
  let input ← plan program [← request program name]
  pure (input, ← entryAt (← preparePlan program input) 0)

private def testControlAndDiagnostics (program : CheckedProgram) : IO Unit := do
  let (_, literal) ← prepareNamed program "literalEvidence"
  assertTrue ((← invoke literal []).observation == .succeeded (scalar 1) [])
    "prepared entry did not compile its authenticated Word integer literal"
  let (_, blocked) ← prepareNamed program "blocked"
  assertTrue ((← invoke blocked [scalar 5]).observation ==
      .succeeded (scalar 5) [present (scalar 5)]) "nested block return was not compiled"
  let (_, scopedEntry) ← prepareNamed program "scoped"
  for flag in [false, true] do
    let actual ← invoke scopedEntry [.bool flag, scalar 11, scalar 29]
    let expected := if flag then scalar 29 else scalar 11
    assertTrue (actual.observation == .succeeded expected
        [present (.bool flag), present (scalar 11), present (scalar 29), present expected, present (scalar 11)])
      "block scope or conditional mutation changed the outer shared cell"
  let (input, branch) ← prepareNamed program "branchFailure"
  let source ← match input.specializations with
    | [specialized] => pure specialized.function.typedBody
    | _ => throw (IO.userError "branch fixture plan should have one specialization")
  let expectedReads := source.nodes.filterMap fun
    | .expression node => match node.form with
      | .reference "absent" (.local binder) => some (node, binder)
      | _ => none
    | _ => none
  let (left, right) ← match expectedReads with
    | [left, right] => pure (left, right)
    | _ => throw (IO.userError "branch fixture must retain two distinct reads")
  assertTrue (decide (left.2 = right.2 ∧ left.1.id ≠ right.1.id ∧ left.1.span ≠ right.1.span))
    "branch fixture no longer tests two occurrences of the same binder"
  let leftReason := branch.faultSites.reasonAt left.1.id
  let rightReason := branch.faultSites.reasonAt right.1.id
  assertTrue (leftReason != Core.Word.zero && rightReason != Core.Word.zero && leftReason != rightReason)
    "distinct read occurrences must receive distinct nonzero reasons"
  for (flag, node, binder, token) in [
      (true, left.1, left.2, leftReason), (false, right.1, right.2, rightReason)] do
    let actual ← invoke branch [.bool flag]
    assertTrue (actual.observation == .failed token [present (.bool flag), .inLeft .word .unit])
      "conditional execution reported the untaken read occurrence"
    assertTrue (decide (branch.failureDiagnostic? token = some {
        error := .uninitializedLocal binder, site := .occurrence node.id.occurrence,
        span := some node.span })) "failure token lost its original binder, occurrence or span"
  assertTrue (decide (branch.failureDiagnostic? Core.Word.zero = some {
      error := .functionFellThrough .word, site := .declaration branch.key.declaration, span := none }))
    "reserved zero token must classify non-Unit function fallthrough"
  assertTrue (decide (branch.failureDiagnostic? (word 999) = none)) "unknown reason produced a diagnostic"
  let (_, choose) ← prepareNamed program "chooseFailure"
  assertTrue ((← invoke choose [.bool true, scalar 6]).observation == .succeeded (scalar 6)
      [present (.bool true), present (scalar 6), .inLeft .word .unit])
    "untaken uninitialized branch was evaluated"

example (entry : Entry) :
    SourceCoreElaboration.lowerType (.declaration entry.key.declaration) entry.sourceResultType =
      .ok entry.resultType := entry.resultProjection

example (type : Core.Ty) (result : Result type) (value : Core.Value) (store : Core.Store)
    (succeeded : result.observation = .succeeded value store) :
    ∃ world, Core.RuntimeStoreHasTypes world store ∧ Core.RuntimeValueHasType world value type :=
  result.success_typed succeeded

example (type : Core.Ty) (result : Result type) (error : Core.MachineFault) (state : Core.State) :
    result.observation ≠ .internalFault error state := result.ne_internalFault error state

example (type : Core.Ty) (checkpoint next : Checkpoint type) (spent additional : Nat)
    (exhausted : Core.runStateful spent checkpoint.state = .outOfFuel next.state) :
    (next.resume additional).observation = (checkpoint.resume (spent + additional)).observation :=
  checkpoint.resume_after_exhaustion next spent additional exhausted

def run : IO Unit := do
  let program ← match checkProgram workspace with
    | .ok program => pure program
    | .error errors => throw (IO.userError s!"entry source fixtures failed checking: {reprStr errors}")
  testPreparedRuns program
  testInputRejections program
  testPreparationRejections program
  testControlAndDiagnostics program

end Tests.SourceCoreBasicEntry
