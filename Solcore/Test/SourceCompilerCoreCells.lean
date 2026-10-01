import Solcore.Test.SourceCompilerFeatureSupport

/-! One public compiler executes mutable locals. Allocation and failure effects
are also audited through the same cached Core artifact's source observer. -/
set_option autoImplicit false
namespace Tests.SourceCompilerCoreCells
open Solcore Solcore.Frontend Tests.SourceCompilerFeatureSupport

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


private def localReads (program : CheckedProgram) (compiled : Entry) (name : String) :
    IO (List (SourceInference.ExpressionNode × Resolved.LocalId)) := do
  let function ← match program.functions.find? (·.declaration == compiled.key.declaration) with
    | some function => pure function | none => throw (IO.userError "diagnostic owner missing")
  pure (function.typedBody.nodes.filterMap fun
    | .expression node => match node.form with
      | .reference actual (.local binder) => if actual == name then some (node, binder) else none
      | _ => none
    | _ => none)

private def failAt (entry : Entry) (arguments : List Value) (node : SourceInference.ExpressionNode)
    (binder : Resolved.LocalId) : IO Core.Word := do
  let invocation ← entry.invoke arguments
  match invocation.outcome with
  | .failed token _ =>
      require (token != Core.Word.zero && decide ((← invocation.diagnostic token) = some {
        error := .uninitializedLocal binder, site := .occurrence node.id.occurrence, span := some node.span }))
        "public failure lost its exact source error, occurrence or span"
      pure token
  | _ => throw (IO.userError "uninitialized read did not fail")

private def testMutableReuse (program : CheckedProgram) : IO Unit := do
  let compiled ← compileNamed program "mutate"
  require (compiled.inputTypes == [.bool, .word, .word] && compiled.resultType == .product .word .bool)
    "public source signature metadata changed"
  for (flag, first, second) in [(true, 11, 29), (false, 2, 7)] do
    let arguments : List Value := [.bool flag, scalar first, scalar second]
    let expected : Value := .product (scalar second) (.bool flag)
    require ((← compiled.run arguments) == expected) "cached mutation reused a previous input frame"
    compiled.checkCells arguments [(.bool, some (.bool flag)), (.word, some (scalar first)),
      (.word, some (scalar second)), (.word, some (scalar second))]
    compiled.checkResume arguments expected

private def testSpecializationAndFailure (program : CheckedProgram) : IO Unit := do
  let pairType := TypeSystem.Ty.product .word (.product .bool .word)
  let compiled ← compileNamed program "replace" [pairType]
  let first : Value := .product (scalar 1) (.product (.bool false) (scalar 2))
  let second : Value := .product (scalar 8) (.product (.bool true) (scalar 9))
  require ((← compiled.run [first, second]) == second) "generic product assignment changed"
  compiled.checkCells [first, second] [(pairType, some first), (pairType, some second), (pairType, some second)]
  let artifact ← compiled.execution.open
  let session ← boot artifact
  match session.start compiled.key [first, .product (scalar 8) (.product (.bool true) (.bool false))] with
  | .error {code := .compatible {code := .sourceTypeMismatch .word .bool, ..}, path, ..} =>
      require (!path.isEmpty) "deep public rejection lost its argument path"
  | _ => throw (IO.userError "nested public shape mismatch was accepted")
  match session.start compiled.key [first] with
  | .error {code := .argumentCountMismatch 2 1, ..} => pure ()
  | .error error => throw (IO.userError s!"public arity diagnostic changed: {reprStr error}")
  | .ok _ => throw (IO.userError "public arity mismatch was accepted")
  -- Raw capability rejection is checked on the actual cached native entry.
  let native ← compiled.native
  let rawFirst : Core.Value := .pair (.word (word 1)) (.pair (.bool false) (.word (word 2)))
  match native.start [rawFirst, .pair (.word (word 8)) (.pair (.bool true) (.cellRef .word 0))] with
  | .error (.input 1 _) => pure ()
  | _ => throw (IO.userError "cached native entry accepted a nested external reference")
  match native.start [] [.word (word 3)] with
  | .error (.initialStoreUnsupported 1) => pure ()
  | _ => throw (IO.userError "cached native entry silently dropped an initial store")
  let absent ← compileNamed program "absent"
  let (node, binder) ← match ← localReads program absent "value" with
    | [site] => pure site | _ => throw (IO.userError "absent read site missing")
  discard <| failAt absent [scalar 4] node binder
  absent.checkCells [scalar 4] [(.word, some (scalar 4)), (.word, none)]

private def testControlAndDiagnostics (program : CheckedProgram) : IO Unit := do
  let early ← compileNamed program "early"
  for flag in [true, false] do
    let expected := if flag then scalar 11 else scalar 29
    let arguments : List Value := [.bool flag, scalar 11, scalar 29]
    require ((← early.run arguments) == expected) "early return or conditional fallthrough changed"
    early.checkCells arguments [(.bool, some (.bool flag)), (.word, some (scalar 11)),
      (.word, some (scalar 29)), (.word, some expected), (.word, some (scalar 29))]
  let branch ← compileNamed program "branchFailure"
  let (left, right) ← match ← localReads program branch "absent" with
    | [left, right] => pure (left, right) | _ => throw (IO.userError "two branch reads missing")
  require (decide (left.2 = right.2 ∧ left.1.id ≠ right.1.id ∧ left.1.span ≠ right.1.span))
    "branch fixture lost distinct read occurrences"
  let tokens ← [true, false].mapM fun flag => do
    let (node, binder) := if flag then left else right
    let token ← failAt branch [.bool flag] node binder
    branch.checkCells [.bool flag] [(.bool, some (.bool flag)), (.word, none)]
    pure token
  require (tokens[0]? != tokens[1]?) "different source reads shared a failure token"
  let invocation ← branch.invoke [.bool true]
  require (decide ((← invocation.diagnostic Core.Word.zero) = some {
    error := .functionFellThrough .word, site := .declaration branch.key.declaration, span := none }))
    "reserved fallthrough diagnostic changed"
  require ((← invocation.diagnostic (word 999)).isNone) "unknown reason resolved to a source diagnostic"
  let choose ← compileNamed program "chooseFailure"
  require ((← choose.run [.bool true, scalar 6]) == scalar 6) "conditional evaluated its untaken branch"
  choose.checkCells [.bool true, scalar 6] [(.bool, some (.bool true)), (.word, some (scalar 6)), (.word, none)]

private def testPrimitivesAndCalls (program : CheckedProgram) : IO Unit := do
  require ((← (← compileNamed program "direct").run [scalar 17]) == scalar 17) "direct result changed"
  require ((← (← compileNamed program "recurse").run [scalar 3]) == scalar 5) "recursive result changed"
  let arithmetic ← compileNamed program "arithmetic"
  for (initial, stored, expected) in ([(4, 18, 17), (0, 6, 5)] : List (Nat × Nat × Nat)) do
    require ((← arithmetic.run [scalar initial]) == scalar expected) "mutable literal arithmetic changed"
    arithmetic.checkCells [scalar initial] [(.word, some (scalar initial)), (.word, some (scalar stored))]
  for (name, shortValue, evaluatingValue) in [("andFailure", false, true), ("orFailure", true, false)] do
    let compiled ← compileNamed program name
    require ((← compiled.run [.bool shortValue]) == .bool shortValue) "short circuit evaluated its right operand"
    compiled.checkCells [.bool shortValue] [(.bool, some (.bool shortValue)), (.bool, none)]
    let (node, binder) ← match ← localReads program compiled "absent" with
      | [site] => pure site | _ => throw (IO.userError "right operand site missing")
    discard <| failAt compiled [.bool evaluatingValue] node binder
    compiled.checkCells [.bool evaluatingValue] [(.bool, some (.bool evaluatingValue)), (.bool, none)]

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
          require (actual == .unit && expected == .word)
            "incomplete non-Unit function changed its checking rejection"
      | error => throw (IO.userError s!"incomplete function produced a different error: {reprStr error}")
  | .error errors => throw (IO.userError s!"incomplete function changed checking phase: {reprStr errors}")
  | .ok _ => throw (IO.userError "incomplete non-Unit function passed source checking")

example {definitions : Core.DataEnvironment} {type : Core.Ty}
    (result : SourceCoreGeneralEntry.Result definitions type) : result.observation.HasType type definitions := result.typed
example {artifact : SourceCoreExecution.Artifact} (done : SourceCoreExecution.Completion artifact) :
    done.session.Authenticates done.boundaryFuel done.sourceType done.value := done.typed

def run : IO Unit := do
  let program ← get "mutable locals checking" (checkProgram workspace)
  testMutableReuse program
  testSpecializationAndFailure program
  testControlAndDiagnostics program
  testPrimitivesAndCalls program
  testFallthroughChecking
end Tests.SourceCompilerCoreCells
