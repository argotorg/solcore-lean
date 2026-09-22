import Solcore.Frontend.SourceInference

/-!
Focused source-inference regressions for the phase-7 language forms.

These tests deliberately exercise the raw-workspace entry point.  They
therefore cover parsing, whole-program signature construction, name/type
resolution, and body inference together instead of manufacturing typed IR.
-/

set_option autoImplicit false

namespace Tests.SourcePhase7Inference

open Solcore Solcore.Frontend Solcore.Frontend.SourceInference

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do
    throw (IO.userError message)

private def workspace (content : String) : Workspace.RawWorkspace := {
  entry := "main.solc"
  mainSources := [{ path := "main.solc", content }]
  externalLibraries := []
}

private def check (label content : String) :
    IO (List CheckedFunction) := do
  match loadAndCheckProgram (workspace content) with
  | .ok functions => pure functions
  | .error errors => throw (IO.userError
      s!"{label} failed source inference: {reprStr errors}")

private def expectInferenceError (label content : String)
    (accept : Error → Bool) : IO Unit := do
  match loadAndCheckProgram (workspace content) with
  | .error errors =>
      assertTrue (errors.any fun error => match error with
        | .body failure => accept failure.error
        | _ => false) s!"{label} reported the wrong error: {reprStr errors}"
  | .ok _ => throw (IO.userError s!"{label} was unexpectedly accepted")

private def checkedNamed (functions : List CheckedFunction)
    (environment : ProgramEnvironment) (name : String) : IO CheckedFunction :=
  match functions.find? fun function =>
      (environment.declaration? function.declaration).any fun declaration =>
        declaration.name == some name with
  | some function => pure function
  | none => throw (IO.userError s!"checked function `{name}` was not found")

private def checkedProgram (label content : String) :
    IO (ProgramEnvironment × List CheckedFunction) := do
  let loaded ← match loadProgram (workspace content) with
    | .ok loaded => pure loaded
    | .error errors => throw (IO.userError
        s!"{label} failed loading: {reprStr errors}")
  let functions ← match checkLoadedProgram loaded with
    | .ok functions => pure functions
    | .error errors => throw (IO.userError
        s!"{label} failed source inference: {reprStr errors}")
  pure (loaded.environment, functions)

private def hasConstructorExpression (function : CheckedFunction) : Bool :=
  function.typedBody.nodes.any fun
    | .expression { form := .constructor .., .. } => true
    | _ => false

private def hasConstructorPattern (function : CheckedFunction) : Bool :=
  function.typedBody.nodes.any fun
    | .statement { form := .matchWith resolution, .. } =>
        resolution.cases.any fun arm => match arm.pattern.resolution with
          | .constructor .. => true
          | _ => false
    | _ => false

private def testConstructors : IO Unit := do
  let source := String.intercalate "\n" [
    "enum Box<T> { Empty, Wrap(T) }",
    "function qualified(value: Word) returns (Box<Word>) {",
    "  return Box.Wrap(value);",
    "}",
    "function contextual(value: Word) returns (Box<Word>) {",
    "  return .Wrap(value);",
    "}"
  ]
  let (environment, functions) ← checkedProgram "constructor forms" source
  let qualified ← checkedNamed functions environment "qualified"
  let contextual ← checkedNamed functions environment "contextual"
  assertTrue (hasConstructorExpression qualified)
    "qualified generic constructor did not produce a constructor node"
  assertTrue (hasConstructorExpression contextual)
    "contextual constructor did not produce a constructor node"

  expectInferenceError "constructor arity"
    (String.intercalate "\n" [
      "enum Box<T> { Wrap(T) }",
      "function bad() returns (Box<Word>) { return Box.Wrap(); }"
    ]) fun error => error matches .constructorArityMismatch _ 1 0
  expectInferenceError "unknown contextual constructor"
    (String.intercalate "\n" [
      "enum Box<T> { Wrap(T) }",
      "function bad(value: Word) returns (Box<Word>) {",
      "  return .Missing(value);",
      "}"
    ]) fun error => error == .unknownConstructor [] "Missing"
  expectInferenceError "unknown qualified constructor"
    (String.intercalate "\n" [
      "enum Box<T> { Wrap(T) }",
      "function bad(value: Word) returns (Box<Word>) {",
      "  return Box.Missing(value);",
      "}"
    ]) fun error => error == .unknownConstructor ["Box"] "Missing"
  expectInferenceError "contextual constructor without an expected type"
    (String.intercalate "\n" [
      "enum Box<T> { Wrap(T) }",
      "function bad() { .Wrap(1); return; }"
    ]) fun error => error == .constructorNeedsExpectedType "Wrap"

private def testConstructorPatterns : IO Unit := do
  let source := String.intercalate "\n" [
    "enum Tree<T> { Leaf(T), Pair(Tree<T>, Tree<T>) }",
    "function nested(tree: Tree<Word>) returns (Word) {",
    "  match (tree) {",
    "    case .Pair(.Leaf(left), .Leaf(right)) { return left; }",
    "    default { return 0; }",
    "  }",
    "}"
  ]
  let (environment, functions) ← checkedProgram "nested patterns" source
  let nested ← checkedNamed functions environment "nested"
  assertTrue (hasConstructorPattern nested)
    "nested constructor/binder pattern did not produce constructor metadata"

  expectInferenceError "duplicate pattern binder"
    (String.intercalate "\n" [
      "enum Tree<T> { Leaf(T), Pair(Tree<T>, Tree<T>) }",
      "function bad(tree: Tree<Word>) returns (Word) {",
      "  match (tree) {",
      "    case .Pair(.Leaf(value), .Leaf(value)) { return value; }",
      "    default { return 0; }",
      "  }",
      "}"
    ]) fun error => error == .duplicatePatternBinder "value"

private def testMultipleScrutinees : IO Unit := do
  let functions ← check "multiple scrutinees" (String.intercalate "\n" [
    "function select(left: Word, right: Bool) returns (Word) {",
    "  match (left, right) {",
    "    case (value, flag) { return flag ? value : 0; }",
    "    default { return 1; }",
    "  }",
    "}"
  ])
  assertTrue (functions.length == 1)
    "multiple-scrutinee tuple pattern lost its checked function"

private def testAssignments : IO Unit := do
  let functions ← check "assignments" (String.intercalate "\n" [
    "function update() returns (Word) {",
    "  let local: Word = 0;",
    "  local = 1;",
    "  let table: mapping(Word => Word);",
    "  table[local] = 2;",
    "  return table[local];",
    "}"
  ])
  let function ← match functions with
    | [function] => pure function
    | _ => throw (IO.userError "assignment fixture lost its checked function")
  let assignments := function.typedBody.nodes.filter fun
    | .statement { form := .assignValue .., .. } => true
    | _ => false
  let indexes := function.typedBody.nodes.filter fun
    | .expression { form := .index .., .. } => true
    | _ => false
  assertTrue (decide (assignments.length = 2) && !indexes.isEmpty)
    "local or mapping-index assignment did not survive in typed source"

private def testLoopsAndControl : IO Unit := do
  let functions ← check "loops and control" (String.intercalate "\n" [
    "function loops(flag: Bool) returns (Word) {",
    "  let total: Word = 0;",
    "  while (flag) { total += 1; break; }",
    "  for (let i: Word = 0; i < 2; i += 1) {",
    "    if (i == 0) { continue; } else { break; }",
    "  }",
    "  return total;",
    "}"
  ])
  let function ← match functions with
    | [function] => pure function
    | _ => throw (IO.userError "loop fixture lost its checked function")
  let hasWhile := function.typedBody.nodes.any fun
    | .statement { form := .whileLoop .., .. } => true
    | _ => false
  let hasFor := function.typedBody.nodes.any fun
    | .statement { form := .forLoop .., .. } => true
    | _ => false
  let hasBreak := function.typedBody.nodes.any fun
    | .statement { form := .breakStmt, .. } => true
    | _ => false
  let hasContinue := function.typedBody.nodes.any fun
    | .statement { form := .continueStmt, .. } => true
    | _ => false
  assertTrue (hasWhile && hasFor && hasBreak && hasContinue)
    "for/while or nested break/continue did not survive in typed source"

  for (kind, statement) in [("break", "break;"), ("continue", "continue;")] do
    expectInferenceError s!"loop-external {kind}"
      ("function bad() { " ++ statement ++ " return; }") fun error =>
        error == .controlOutsideLoop kind

  expectInferenceError "lambda cannot break its enclosing loop"
    (String.intercalate "\n" [
      "function bad(flag: Bool) {",
      "  while (flag) {",
      "    let escape = lam() { break; };",
      "    break;",
      "  }",
      "}"
    ]) fun error => error == .controlOutsideLoop "break"

private def testNonterminalMatch : IO Unit := do
  let functions ← check "nonterminal match" (String.intercalate "\n" [
    "function route(tag: Word) returns (Word) {",
    "  let result: Word = 0;",
    "  match (tag) {",
    "    case 0 { result = 1; }",
    "    default { result = 2; }",
    "  }",
    "  return result;",
    "}"
  ])
  assertTrue (functions.length == 1)
    "a nonterminal exhaustive match did not check"

/-- Exercise every phase-7 source-inference form before runtime lowering. -/
def testSourcePhase7Inference : IO Unit := do
  testConstructors
  testConstructorPatterns
  testMultipleScrutinees
  testAssignments
  testLoopsAndControl
  testNonterminalMatch
  IO.println "phase-7 source inference GREEN"

end Tests.SourcePhase7Inference
