import Solcore.Frontend.SourceInference

/-! Focused parsed-source regressions for the source inference slice. -/

set_option autoImplicit false

namespace Tests.SourceInference

open Solcore Solcore.Frontend

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do
    throw (IO.userError message)

private def workspace (content : String) : Workspace.RawWorkspace := {
  entry := "main.solc"
  mainSources := [{ path := "main.solc", content }]
  externalLibraries := []
}

private def check (content : String) :
    IO (List SourceInference.CheckedFunction) := do
  match SourceInference.loadAndCheckProgram (workspace content) with
  | .ok checked => pure checked
  | .error errors =>
      throw (IO.userError s!"source inference failed: {reprStr errors}")

private def testLambdaLetTupleConditional : IO Unit := do
  let checked ← check (String.intercalate "\n" [
    "function polymorphic(flag: Bool) returns (Word, Bool) {",
    "  let id = lam(value) { return value; };",
    "  return (id(((1))), id(flag ? flag : !flag));",
    "}",
    "function expected(flag: Bool) returns (function(Word) returns (Word)) {",
    "  return lam(value) { return flag ? value + 1 : value; };",
    "}",
    "function empty() { return (); }"
  ])
  assertTrue (decide (checked.length = 3))
    "lambda/let/tuple fixture lost a checked function"
  match checked with
  | first :: second :: third :: [] =>
      assertTrue (decide (first.inferredBodyType =
          TypeSystem.Ty.product .word .bool))
        "let-polymorphic tuple did not infer Word × Bool"
      assertTrue (decide (second.inferredBodyType =
          TypeSystem.Ty.function .word .word))
        "expected function type did not guide an inferred lambda"
      assertTrue (decide (third.inferredBodyType = .unit))
        "empty tuple did not check as Unit"
  | _ => throw (IO.userError "checked function order changed")

private def testAmbiguousOverload : IO Unit := do
  let source := String.intercalate "\n" [
    "function choose(value: Word) returns (Word) { return value; }",
    "function choose(other: Word) returns (Word) { return other + 1; }",
    "function run() returns (Word) { return choose(1); }"
  ]
  match SourceInference.loadAndCheckProgram (workspace source) with
  | .error errors =>
      assertTrue (errors.any fun error => match error with
        | .body { error := .ambiguousOverload "choose" candidates, .. } =>
            candidates.length == 2
        | _ => false) "ambiguous overload was not reported explicitly"
  | .ok _ => throw (IO.userError "ambiguous overload was selected")

private def testNumericExpectedType : IO Unit := do
  let source := "function bad() returns (Bool) { return 1; }"
  match SourceInference.loadAndCheckProgram (workspace source) with
  | .error errors =>
      assertTrue (errors.any fun error => match error with
        | .body { error := .nonNumericLiteral .bool, .. } => true
        | _ => false) "a numeric literal silently checked as Bool"
  | .ok _ => throw (IO.userError "a numeric literal checked as Bool")

private def testTraitBackedLiteral : IO Unit := do
  let source := String.intercalate "\n" [
    "trait FromLiteral<T> {}",
    "enum Box { Only }",
    "impl FromLiteral<Box> {}",
    "function literal() returns (Box) { return 1; }"
  ]
  let checked ← check source
  match checked with
  | [function] =>
      assertTrue (decide (function.predicates.length = 1) &&
          function.evidence.any fun evidence => match evidence with
            | .implementation _ => true
            | .assumption _ => false)
        "trait-backed non-Word literal lost its predicate or evidence"
  | _ => throw (IO.userError "literal fixture lost its checked function")

private def testUnsupportedStatement : IO Unit := do
  let source :=
    "function loop(flag: Bool) { while (flag) { return; } }"
  match SourceInference.loadAndCheckProgram (workspace source) with
  | .error errors =>
      assertTrue (errors.any fun error => match error with
        | .body { error := .unsupportedStatement "while loop", .. } => true
        | _ => false) "deferred while inference was not explicit"
  | .ok _ => throw (IO.userError "deferred while inference was accepted")

private def testTraitBackedCoercion : IO Unit := do
  let source := String.intercalate "\n" [
    "trait Coerce<From, To> {}",
    "enum Box { Only }",
    "impl Coerce<Word, Box> {}",
    "function accept(value: Box) returns (Box) { return value; }",
    "function convert(value: Word) returns (Box) { return accept(value); }"
  ]
  let checked ← check source
  match checked.find? fun function =>
      function.evidence.any fun evidence => match evidence with
        | .implementation _ => true
        | .assumption _ => false with
  | some function =>
      assertTrue (decide (function.predicates.length = 1))
        "coercion evidence lost its Coerce predicate"
  | none => throw (IO.userError "trait-backed coercion produced no evidence")

private def testMissingCoercion : IO Unit := do
  let source := String.intercalate "\n" [
    "trait Coerce<From, To> {}",
    "enum Box { Only }",
    "function accept(value: Box) returns (Box) { return value; }",
    "function reject(value: Word) returns (Box) { return accept(value); }"
  ]
  match SourceInference.loadAndCheckProgram (workspace source) with
  | .error errors =>
      assertTrue (errors.any fun error => match error with
        | .body { error := .noTraitImplementation predicate, .. } =>
            predicate.arguments.length == 1
        | _ => false) "missing coercion implementation was accepted"
  | .ok _ => throw (IO.userError "missing coercion implementation was accepted")

private def testInconclusiveCoercion : IO Unit := do
  let source := String.intercalate "\n" [
    "trait Coerce<From, To> {}",
    "enum Box { Only }",
    "impl Coerce<Word, Box> {}",
    "impl Coerce<Word, Box> {}",
    "function accept(value: Box) returns (Box) { return value; }",
    "function reject(value: Word) returns (Box) { return accept(value); }"
  ]
  match SourceInference.loadAndCheckProgram (workspace source) with
  | .error errors =>
      assertTrue (errors.any fun error => match error with
        | .body { error := .inconclusiveTrait (.ambiguous _ _ _), .. } => true
        | _ => false) "overlapping coercion implementations lost ambiguity"
  | .ok _ => throw (IO.userError "ambiguous coercion implementation was selected")

private def testConstrainedLetDoesNotGeneralizeAwayEvidence : IO Unit := do
  let source := String.intercalate "\n" [
    "trait Eq<T> {}",
    "impl Eq<Word> {}",
    "function keep<T>(value: T) returns (T) where T: Eq { return value; }",
    "function reject() returns (Bool) {",
    "  let f = lam(value) { return keep(value); };",
    "  return f(true);",
    "}"
  ]
  match SourceInference.loadAndCheckProgram (workspace source) with
  | .error errors =>
      assertTrue (errors.any fun error => match error with
        | .body { error := .noTraitImplementation predicate, .. } =>
            predicate.subject == TypeSystem.Ty.bool
        | _ => false)
        "a constrained let detached its predicate from the instantiated type"
  | .ok _ => throw (IO.userError "Eq<Word> evidence was reused for Bool")

private def testAmbiguousCoercionTrait : IO Unit := do
  let raw : Workspace.RawWorkspace := {
    entry := "main.solc"
    mainSources := [
      { path := "left.solc", content := "trait Coerce<From, To> {}" },
      { path := "right.solc", content := "trait Coerce<From, To> {}" },
      {
        path := "main.solc"
        content := String.intercalate "\n" [
          "function accept(value: Bool) returns (Bool) { return value; }",
          "function reject(value: Word) returns (Bool) { return accept(value); }"
        ]
      }
    ]
    externalLibraries := []
  }
  match SourceInference.loadAndCheckProgram raw with
  | .error errors =>
      assertTrue (errors.any fun error => match error with
        | .body { error := .ambiguousOperatorTrait "Coerce" candidates, .. } =>
            candidates.length == 2
        | _ => false) "ambiguous Coerce declarations lost their diagnostic"
  | .ok _ => throw (IO.userError "ambiguous Coerce declaration was selected")

/-- Exercise parsed lambdas, local schemes, tuples, grouping, conditionals,
operators, numeric expected/default behavior, and explicit deferrals. -/
def testSourceInference : IO Unit := do
  testLambdaLetTupleConditional
  testAmbiguousOverload
  testNumericExpectedType
  testTraitBackedLiteral
  testUnsupportedStatement
  testTraitBackedCoercion
  testMissingCoercion
  testInconclusiveCoercion
  testConstrainedLetDoesNotGeneralizeAwayEvidence
  testAmbiguousCoercionTrait

end Tests.SourceInference
