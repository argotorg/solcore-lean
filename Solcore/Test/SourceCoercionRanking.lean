import Solcore.Frontend.SourceInference

/-! Per-argument coercion and exact-over-coercible overload regressions. -/

set_option autoImplicit false

namespace Tests.SourceCoercionRanking

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

private def finalFunction
    (checked : List SourceInference.CheckedFunction) :
    IO SourceInference.CheckedFunction :=
  match checked.getLast? with
  | some function => pure function
  | none => throw (IO.userError "source inference returned no checked function")

private def testTwoArgumentsBothCoerced : IO Unit := do
  let checked ← check (String.intercalate "\n" [
    "trait Coerce<From, To> {}",
    "enum Box { Only }",
    "impl Coerce<Word, Box> {}",
    "function accept(left: Box, right: Box) returns (Box) { return left; }",
    "function convert(left: Word, right: Word) returns (Box) {",
    "  return accept(left, right);",
    "}"
  ])
  let function ← finalFunction checked
  assertTrue (function.predicates.length == 2 && function.evidence.length == 2)
    "two source arguments did not retain two independent coercions"

private def testOneExactOneCoerced : IO Unit := do
  let checked ← check (String.intercalate "\n" [
    "trait Coerce<From, To> {}",
    "enum Box { Only }",
    "impl Coerce<Word, Box> {}",
    "function accept(left: Word, right: Box) returns (Box) { return right; }",
    "function convert(left: Word, right: Word) returns (Box) {",
    "  return accept(left, right);",
    "}"
  ])
  let function ← finalFunction checked
  assertTrue (function.predicates.length == 1 && function.evidence.length == 1)
    "an exact argument introduced coercion evidence"

private def testTupleArgumentStaysWhole : IO Unit := do
  let source := String.intercalate "\n" [
    "trait Coerce<From, To> {}",
    "enum Box { Only }",
    "impl Coerce<Word, Box> {}",
    "function accept(value: (Box, Box)) returns ((Box, Box)) { return value; }",
    "function reject(left: Word, right: Word) returns ((Box, Box)) {",
    "  return accept((left, right));",
    "}"
  ]
  match SourceInference.loadAndCheckProgram (workspace source) with
  | .error errors =>
      assertTrue (errors.any fun error => match error with
        | .body { error := .noTraitImplementation predicate, .. } =>
            predicate.subject == TypeSystem.Ty.product .word .word
        | _ => false)
        "one tuple argument was recursively treated as two coercible arguments"
  | .ok _ =>
      throw (IO.userError "element coercions were incorrectly applied inside a tuple")

private def testExactOverloadWins : IO Unit := do
  let checked ← check (String.intercalate "\n" [
    "trait Coerce<From, To> {}",
    "enum Box { Only }",
    "impl Coerce<Word, Box> {}",
    "function choose(value: Box) returns (Bool) { return true; }",
    "function choose(value: Word) returns (Word) { return value; }",
    "function select(value: Word) returns (Word) { return choose(value); }"
  ])
  let function ← finalFunction checked
  assertTrue (function.inferredBodyType == TypeSystem.Ty.word &&
      function.predicates.isEmpty && function.evidence.isEmpty)
    "a coercible overload competed with an exact overload"

private def testMissingPerArgumentCoercion : IO Unit := do
  let source := String.intercalate "\n" [
    "trait Coerce<From, To> {}",
    "enum Box { Only }",
    "enum Flag { Only }",
    "impl Coerce<Word, Box> {}",
    "function accept(left: Box, right: Flag) returns (Box) { return left; }",
    "function reject(left: Word, right: Word) returns (Box) {",
    "  return accept(left, right);",
    "}"
  ]
  match SourceInference.loadAndCheckProgram (workspace source) with
  | .error errors =>
      assertTrue (errors.any fun error => match error with
        | .body { error := .noTraitImplementation predicate, .. } =>
            predicate.subject == TypeSystem.Ty.word &&
              predicate.arguments.length == 1
        | _ => false)
        "a missing coercion for one argument did not reject the call"
  | .ok _ => throw (IO.userError "a missing per-argument coercion was accepted")

/-- Exercise direct coercion per source argument without flattening tuple values. -/
def testSourceCoercionRanking : IO Unit := do
  testTwoArgumentsBothCoerced
  testOneExactOneCoerced
  testTupleArgumentStaysWhole
  testExactOverloadWins
  testMissingPerArgumentCoercion

end Tests.SourceCoercionRanking
