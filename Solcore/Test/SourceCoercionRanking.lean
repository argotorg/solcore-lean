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

private def testMethodProofCountDoesNotDistortEdgeCost : IO Unit := do
  let source := String.intercalate "\n" [
    "trait Ready<T> {}",
    "trait Stable<T> {}",
    "trait Coerce<From, To> {",
    "  function coerce(value: From) returns (To)",
    "      where From: Ready, From: Stable;",
    "}",
    "enum A { Only }",
    "enum B { Only }",
    "enum Mid { Only }",
    "enum C { Only }",
    "impl Ready<A> {}",
    "impl Stable<A> {}",
    "impl Ready<Mid> {}",
    "impl Stable<Mid> {}",
    "impl Coerce<A, B> {",
    "  function coerce(value: A) returns (B)",
    "      where A: Ready, A: Stable { return value; }",
    "}",
    "impl Coerce<A, Mid> {",
    "  function coerce(value: A) returns (Mid)",
    "      where A: Ready, A: Stable { return value; }",
    "}",
    "impl Coerce<Mid, C> {",
    "  function coerce(value: Mid) returns (C)",
    "      where Mid: Ready, Mid: Stable { return value; }",
    "}",
    "function choose(value: B) returns (Word) { return 1; }",
    "function choose(value: C) returns (Word) { return 2; }",
    "function run(value: A) returns (Word) { return choose(value); }"
  ]
  let loaded ← match loadProgram (workspace source) with
    | .ok loaded => pure loaded
    | .error errors => throw (IO.userError
        s!"coercion-cost fixture failed to load: {reprStr errors}")
  let signatures ← match buildProgramSignatures loaded.environment with
    | .ok signatures => pure signatures
    | .error errors => throw (IO.userError
        s!"coercion-cost signatures failed: {reprStr errors}")
  let checked ← match SourceInference.checkFunctionBodies
      loaded.environment signatures with
    | .ok checked => pure checked
    | .error errors => throw (IO.userError
        s!"coercion-cost inference failed: {reprStr errors}")
  let run ← finalFunction checked
  let declaration ← match loaded.environment.valuesNamed "run" with
    | [declaration] => pure declaration
    | declarations => throw (IO.userError
        s!"expected one run declaration, found {declarations.length}")
  let namedType (name : String) : IO TypeSystem.Ty :=
    match loaded.environment.typesNamed name with
    | [declaration] => pure (.nominal declaration.id)
    | declarations => throw (IO.userError
        s!"expected one type `{name}`, found {declarations.length}")
  let namedTrait (name : String) : IO Resolved.DeclarationId :=
    match loaded.environment.traitsNamed name with
    | [declaration] => pure declaration.id
    | declarations => throw (IO.userError
        s!"expected one trait `{name}`, found {declarations.length}")
  let a ← namedType "A"
  let b ← namedType "B"
  let c ← namedType "C"
  let coerce ← namedTrait "Coerce"
  let ready ← namedTrait "Ready"
  let stable ← namedTrait "Stable"
  let context : SourceInference.Context := {
    environment := loaded.environment
    signatures
    scope := .ofDeclaration declaration
  }
  let state := SourceInference.State.initial declaration.id
  let argument : SourceInference.InferredExpression := {
    id := { occurrence := { owner := declaration.id, index := 0 } }
    type := a
  }
  let directFit ← match SourceInference.Detail.fitArguments context state
      [argument] [b] with
    | .ok (some fitted) => pure fitted
    | .ok none => throw (IO.userError "one-edge coercion did not fit")
    | .error error => throw (IO.userError
        s!"one-edge coercion failed: {reprStr error}")
  let longFit ← match SourceInference.Detail.fitArguments context state
      [argument] [c] with
    | .ok (some fitted) => pure fitted
    | .ok none => throw (IO.userError "two-edge coercion did not fit")
    | .error error => throw (IO.userError
        s!"two-edge coercion failed: {reprStr error}")
  assertTrue (decide (directFit.cost = 1 ∧ longFit.cost = 2 ∧
      directFit.state.requirements.length = 3 ∧
      longFit.state.requirements.length = 6))
    "coercion ranking counted proof obligations instead of path edges"
  let expected : List ProgramPredicate := [
    { trait := coerce, subject := a, arguments := [b] },
    { trait := ready, subject := a, arguments := [] },
    { trait := stable, subject := a, arguments := [] }
  ]
  assertTrue (decide (run.predicates = expected))
    "a two-edge overload outranked the one-edge overload with method evidence"

/-- Exercise direct coercion per source argument without flattening tuple values. -/
def testSourceCoercionRanking : IO Unit := do
  testTwoArgumentsBothCoerced
  testOneExactOneCoerced
  testTupleArgumentStaysWhole
  testExactOverloadWins
  testMissingPerArgumentCoercion
  testMethodProofCountDoesNotDistortEdgeCost

end Tests.SourceCoercionRanking
