import Solcore.Frontend.SourceCompiler

/-! Public compilation selects the prepared Core path for mutable scalar and
product locals. These tests require its language-result carrier, so a silent
typed-source fallback cannot satisfy them. -/

set_option autoImplicit false

namespace Tests.SourceCompilerCoreCells

open Solcore Solcore.Frontend Solcore.Frontend.SourceCompiler

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

private def word (value : Nat) : Core.Word := Core.Word.ofNatModulo value
private def scalar (value : Nat) : Core.Value := .word (word value)
private def present (value : Core.Value) : Core.Value := .inRight .unit value

private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc"
  mainSources := [{ path := "main.solc", content := String.intercalate "\n" [
    "function mutate(flag: Bool, first: Word, second: Word) returns (Word, Bool) {",
    "  let value: Word; value = first; value = second; return (value, flag);",
    "}",
    "function replace<T>(first: T, second: T) returns (T) {",
    "  let value: T = first; value = second; return value;",
    "}",
    "function absent(input: Word) returns (Word) { let value: Word; return value; }",
    "function early(flag: Bool, initial: Word, replacement: Word) returns (Word) {",
    "  let value: Word = initial;",
    "  { let inner: Word = replacement; if (flag) { return value; } value = inner; }",
    "  value = replacement; return value;",
    "}",
    "function branchFailure(flag: Bool) returns (Word) {",
    "  let absent: Word; return flag ? absent : absent;",
    "}",
    "function chooseFailure(flag: Bool, value: Word) returns (Word) {",
    "  let absent: Word; return flag ? value : absent;",
    "}",
    "function arithmetic(initial: Word) returns (Word) {",
    "  let value: Word = initial + 2; value = value * 3; return value - 1;",
    "}",
    "function andFailure(flag: Bool) returns (Bool) {",
    "  let absent: Bool; return flag && absent;",
    "}",
    "function orFailure(flag: Bool) returns (Bool) {",
    "  let absent: Bool; return flag || absent;",
    "}",
    "function direct(input: Word) returns (Word) { return input; }",
    "function recurse(value: Word) returns (Word) {",
    "  return value == 0 ? 5 : recurse(value - 1);",
    "}"
  ] }]
  externalLibraries := []
}

private def options : CompileOptions := { specializationBudget := 64, stagingFuel := 128 }
private def execution : RunOptions := { executionFuel := 1000 }

private def compileNamed (program : CheckedProgram) (name : String)
    (types : List TypeSystem.Ty := []) (preference : BackendPreference := .automatic) :
    IO CompiledEntry := do
  let signature ← match program.signatures.functions.filter (·.name == name) with
    | [signature] => pure signature
    | _ => throw (IO.userError s!"public Core fixture missing: {name}")
  match compileChecked program (.declaration signature.id types)
      { options with backendPreference := preference } with
  | .ok compiled => pure compiled
  | .error error => throw (IO.userError s!"public Core compilation rejected {name}: {reprStr error}")

private def observation (result : Except RunError ExecutionResult) : IO Core.LanguageResult.Observation := do
  match result with
  | .ok (.coreLanguageResult observation) => pure observation
  | result => throw (IO.userError s!"prepared Core carrier was not selected: {reprStr result}")

private def localReads (program : CheckedProgram) (compiled : CompiledEntry) (name : String) :
    IO (List (SourceInference.ExpressionNode × Resolved.LocalId)) := do
  let function ← match program.functions.find? (·.declaration == compiled.key.declaration) with
    | some function => pure function
    | none => throw (IO.userError "public diagnostic fixture declaration disappeared")
  pure (function.typedBody.nodes.filterMap fun
    | .expression node => match node.form with
      | .reference actual (.local binder) => if actual == name then some (node, binder) else none
      | _ => none
    | _ => none)

private def testAutomaticAndExplicitCore (program : CheckedProgram) : IO Unit := do
  let arguments := [.bool true, scalar 11, scalar 29]
  let expected := Core.LanguageResult.Observation.succeeded (.pair (scalar 29) (.bool true))
    [present (.bool true), present (scalar 11), present (scalar 29), present (scalar 29)]
  for preference in [BackendPreference.automatic, .core] do
    let compiled ← compileNamed program "mutate" [] preference
    assertTrue (compiled.backend == .core) "mutable local compilation must report the Core backend"
    assertTrue (compiled.inputTypes == [.bool, .word, .word]) "public source input types changed"
    assertTrue (compiled.resultType == .product .word .bool) "public source result projection changed"
    let actual ← observation (compiled.runCore arguments execution)
    assertTrue (actual == expected) "public Core mutation changed value or allocation order"
    let reused ← observation (compiled.runCore [.bool false, scalar 2, scalar 7] execution)
    assertTrue (reused == .succeeded (.pair (scalar 7) (.bool false))
        [present (.bool false), present (scalar 2), present (scalar 7), present (scalar 7)])
      "public compiled entry reuse retained a previous input frame"
    let paused ← observation (compiled.runCore arguments { execution with executionFuel := 10 })
    match paused with
    | .outOfFuel state =>
        assertTrue (Core.LanguageResult.observeResult (Core.runStateful 990 state) == expected)
          "public Core exhaustion lost its resumable machine state"
    | result => throw (IO.userError s!"public Core did not suspend at small fuel: {reprStr result}")
    match compiled.runTyped [.bool true, .word (word 11), .word (word 29)] execution with
    | .error (.invocationKindMismatch .core .typedValues) => pure ()
    | result => throw (IO.userError s!"public Core accepted the typed-source input carrier: {reprStr result}")

private def testSpecializationAndFailure (program : CheckedProgram) : IO Unit := do
  let pairType := TypeSystem.Ty.product .word (.product .bool .word)
  let compiled ← compileNamed program "replace" [pairType]
  assertTrue (compiled.backend == .core) "generic mutable products must compile to Core"
  let first : Core.Value := .pair (scalar 1) (.pair (.bool false) (scalar 2))
  let second : Core.Value := .pair (scalar 8) (.pair (.bool true) (scalar 9))
  let actual ← observation (compiled.runCore [first, second] execution)
  assertTrue (actual == .succeeded second [present first, present second, present second])
    "generic product specialization did not share the assigned local cell"
  match compiled.runCore [first, .pair (scalar 8) (.pair (.bool true) (.cellRef .word 0))] execution with
  | .error (.coreRuntimeInput (.inputShape 1 _)) => pure ()
  | result => throw (IO.userError s!"deep external reference escaped public input checking: {reprStr result}")
  match compiled.runCore [first] execution with
  | .error (.coreRuntimeInput (.argumentCountMismatch 2 1)) => pure ()
  | result => throw (IO.userError s!"public prepared Core lost its arity rejection: {reprStr result}")
  match compiled.runCore [first, second] execution [scalar 3] with
  | .error (.coreRuntimeInput (.initialStoreUnsupported 1)) => pure ()
  | result => throw (IO.userError s!"nonempty initial store was silently dropped: {reprStr result}")
  let absent ← compileNamed program "absent"
  let failed ← observation (absent.runCore [scalar 4] execution)
  let (node, binder) ← match ← localReads program absent "value" with
    | [site] => pure site
    | _ => throw (IO.userError "public uninitialized fixture lost its read site")
  match failed with
  | .failed token store =>
      assertTrue (token != Core.Word.zero && store == [present (scalar 4), .inLeft .word .unit])
        "uninitialized local must retain a positive read reason and its final store"
      assertTrue (decide (absent.coreFailureDiagnostic? token = some {
          error := .uninitializedLocal binder, site := .occurrence node.id.occurrence,
          span := some node.span })) "public language failure lost its source diagnostic"
  | result => throw (IO.userError s!"public uninitialized read did not fail: {reprStr result}")

private def testControlAndDiagnostics (program : CheckedProgram) : IO Unit := do
  let early ← compileNamed program "early"
  assertTrue (early.backend == .core) "scoped conditional control did not select Core"
  for flag in [true, false] do
    let actual ← observation (early.runCore [.bool flag, scalar 11, scalar 29] execution)
    let expected := if flag then scalar 11 else scalar 29
    assertTrue (actual == .succeeded expected [present (.bool flag), present (scalar 11),
        present (scalar 29), present expected, present (scalar 29)])
      "nested early return or conditional fallthrough changed the value/store"
  let branch ← compileNamed program "branchFailure"
  let (left, right) ← match ← localReads program branch "absent" with
    | [left, right] => pure (left, right)
    | _ => throw (IO.userError "public branch fixture must retain two read occurrences")
  assertTrue (decide (left.2 = right.2 ∧ left.1.id ≠ right.1.id ∧ left.1.span ≠ right.1.span))
    "public branch fixture no longer tests different occurrences of one binder"
  let tokens ← [true, false].mapM fun flag => do
    let actual ← observation (branch.runCore [.bool flag] execution)
    let (node, binder) := if flag then left else right
    match actual with
    | .failed token store =>
        assertTrue (token != Core.Word.zero && store == [present (.bool flag), .inLeft .word .unit])
          "public branch failure changed the store or used fallthrough reason"
        assertTrue (decide (branch.coreFailureDiagnostic? token = some {
            error := .uninitializedLocal binder, site := .occurrence node.id.occurrence,
            span := some node.span })) "public branch reported the wrong read occurrence"
        pure token
    | result => throw (IO.userError s!"public branch failed to report uninitialized read: {reprStr result}")
  assertTrue (tokens.length == 2 && tokens[0]? != tokens[1]?)
    "public failure carrier merged different read occurrences"
  assertTrue (decide (branch.coreFailureDiagnostic? Core.Word.zero = some {
      error := .functionFellThrough .word, site := .declaration branch.key.declaration, span := none }))
    "public reserved fallthrough diagnostic changed"
  assertTrue (decide (branch.coreFailureDiagnostic? (word 999) = none)) "unknown public reason resolved"
  let choose ← compileNamed program "chooseFailure"
  assertTrue ((← observation (choose.runCore [.bool true, scalar 6] execution)) ==
      .succeeded (scalar 6) [present (.bool true), present (scalar 6), .inLeft .word .unit])
    "public conditional evaluated an untaken failure branch"

private def testRetainedBackends (program : CheckedProgram) : IO Unit := do
  let direct ← compileNamed program "direct"
  match direct.runCore [scalar 17] execution with
  | .ok (.core (.done value [])) =>
      assertTrue (value == scalar 17) "legacy direct Core value changed"
  | result => throw (IO.userError s!"legacy direct Core priority changed: {reprStr result}")
  let typed ← compileNamed program "mutate" [] .typedSource
  assertTrue (typed.backend == .typedSource) "explicit typed-source policy was ignored"
  match typed.runTyped [.bool true, .word (word 11), .word (word 29)] execution with
  | .ok (.typedSource (.done (.product (.word value) (.bool true)) _)) =>
      assertTrue (value == word 29) "explicit typed-source execution changed"
  | result => throw (IO.userError s!"explicit typed-source execution failed: {reprStr result}")
  let recursive ← compileNamed program "recurse"
  assertTrue (recursive.backend == .core) "named recursion did not select Core"
  match recursive.runCore [scalar 3] execution with
  | .ok (.coreLanguageResult (.succeeded (.word value) _)) =>
      assertTrue (value == word 5) "Core recursive value changed"
  | result => throw (IO.userError s!"Core recursive execution failed: {reprStr result}")

private def testPrimitiveIntegration (program : CheckedProgram) : IO Unit := do
  for preference in [BackendPreference.automatic, .core] do
    let arithmetic ← compileNamed program "arithmetic" [] preference
    assertTrue (arithmetic.backend == .core) "mutable literal/arithmetic code did not select Core"
    for (initial, stored, expected) in ([(4, 18, 17), (0, 6, 5)] : List (Nat × Nat × Nat)) do
      let actual ← observation (arithmetic.runCore [scalar initial] execution)
      assertTrue (actual == .succeeded (scalar expected) [present (scalar initial), present (scalar stored)])
        "public primitive policy lost literals, mutation, arithmetic order or cached entry reuse"
    for (name, shortValue, evaluatingValue) in [
        ("andFailure", false, true), ("orFailure", true, false)] do
      let compiled ← compileNamed program name [] preference
      assertTrue (compiled.backend == .core) "short-circuit local code did not select Core"
      let skipped ← observation (compiled.runCore [.bool shortValue] execution)
      assertTrue (skipped == .succeeded (.bool shortValue)
          [present (.bool shortValue), .inLeft .bool .unit])
        "public short circuit evaluated its uninitialized right operand"
      let (node, binder) ← match ← localReads program compiled "absent" with
        | [site] => pure site
        | _ => throw (IO.userError "short-circuit fixture lost its right read occurrence")
      match ← observation (compiled.runCore [.bool evaluatingValue] execution) with
      | .failed token store =>
          assertTrue (token != Core.Word.zero && store ==
              [present (.bool evaluatingValue), .inLeft .bool .unit])
            "public short-circuit failure lost its nonzero reason or preserved store"
          assertTrue (decide (compiled.coreFailureDiagnostic? token = some {
              error := .uninitializedLocal binder, site := .occurrence node.id.occurrence,
              span := some node.span })) "public short-circuit failure lost the right operand's source diagnostic"
      | result => throw (IO.userError s!"public short circuit skipped a required right operand: {reprStr result}")
  let typed ← compileNamed program "arithmetic" [] .typedSource
  match typed.runTyped [.word (word 4)] execution with
  | .ok (.typedSource (.done (.word value) _)) =>
      assertTrue (value == word 17) "explicit typed-source arithmetic disagrees with the Core result"
  | result => throw (IO.userError s!"explicit typed-source arithmetic failed: {reprStr result}")

private def testFallthroughChecking : IO Unit := do
  let incomplete : Workspace.RawWorkspace := {
    entry := "main.solc", externalLibraries := []
    mainSources := [{ path := "main.solc", content :=
      "function incomplete(flag: Bool, input: Word) returns (Word) { if (flag) { return input; } }" }]
  }
  match checkProgram incomplete with
  | .error [.inference failure] =>
      match failure.error with
      | .unification (.mismatch actual expected) =>
          assertTrue (actual == .unit && expected == .word)
            "incomplete non-Unit function changed its checking rejection"
      | error => throw (IO.userError s!"incomplete function produced a different error: {reprStr error}")
  | .error errors => throw (IO.userError s!"incomplete function changed checking phase: {reprStr errors}")
  | .ok _ => throw (IO.userError "incomplete non-Unit function passed source checking")

example (program : CheckedProgram) (seed : Seed) (compileOptions : CompileOptions)
    (compiled : CompiledEntry) (arguments : List Core.Value) (store : Core.Store)
    (runOptions : RunOptions) (result : Core.LanguageResult.Observation)
    (accepted : compileChecked program seed compileOptions = .ok compiled)
    (ran : compiled.run (.coreValues arguments store) runOptions = .ok (.coreLanguageResult result)) :
    compiled.CoreLanguageResultHasPublicType result :=
  compiled.run_coreLanguageResult_has_public_resultType arguments store runOptions result
    (compileChecked_hasPublicResultProjection program seed compileOptions compiled accepted) ran

def run : IO Unit := do
  let program ← match checkProgram workspace with
    | .ok program => pure program
    | .error errors => throw (IO.userError s!"public Core fixture checking failed: {reprStr errors}")
  testAutomaticAndExplicitCore program
  testSpecializationAndFailure program
  testControlAndDiagnostics program
  testRetainedBackends program
  testPrimitiveIntegration program
  testFallthroughChecking

end Tests.SourceCompilerCoreCells
