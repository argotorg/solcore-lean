import Solcore.Frontend.SourceInference

/-! Stable function-local identities for solved source obligations. -/

set_option autoImplicit false

namespace Tests.SourceRequirementIdentity

open Solcore Solcore.Frontend

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do
    throw (IO.userError message)

private def workspace (content : String) : Workspace.RawWorkspace := {
  entry := "main.solc"
  mainSources := [{ path := "main.solc", content }]
  externalLibraries := []
}

private structure Fixture where
  environment : ProgramEnvironment
  checked : List SourceInference.CheckedFunction

private def check (content : String) : IO Fixture := do
  match loadProgram (workspace content) with
  | .error errors =>
      throw (IO.userError s!"requirement identity loading failed: {reprStr errors}")
  | .ok loaded =>
      match SourceInference.checkLoadedProgram loaded with
      | .error errors =>
          throw (IO.userError
            s!"requirement identity checking failed: {reprStr errors}")
      | .ok checked => pure { environment := loaded.environment, checked }

private def checkedNamed (fixture : Fixture) (name : String) :
    IO SourceInference.CheckedFunction :=
  match fixture.checked.find? fun function =>
      match fixture.environment.declaration? function.declaration with
      | some declaration => declaration.name == some name
      | none => false with
  | some function => pure function
  | none => throw (IO.userError s!"checked function `{name}` was not found")

private def namedType (environment : ProgramEnvironment) (name : String) :
    IO TypeSystem.Ty :=
  match environment.typesNamed name with
  | [declaration] => pure (.nominal declaration.id)
  | declarations =>
      throw (IO.userError
        s!"expected one type `{name}`, found {declarations.length}")

private def namedTrait (environment : ProgramEnvironment) (name : String) :
    IO Resolved.DeclarationId :=
  match environment.traitsNamed name with
  | [declaration] => pure declaration.id
  | declarations =>
      throw (IO.userError
        s!"expected one trait `{name}`, found {declarations.length}")

private def predicate (trait : Resolved.DeclarationId) (subject : TypeSystem.Ty)
    (arguments : List TypeSystem.Ty := []) : ProgramPredicate := {
  trait
  subject
  arguments
}

private def evidenceHasGoal (expected : ProgramPredicate) :
    SourceInference.PredicateEvidence → Bool
  | .assumption actual => decide (actual = expected)
  | .implementation (.byImpl goal _ _) => decide (goal = expected)

private def aligned (function : SourceInference.CheckedFunction)
    (expected : List ProgramPredicate) : Bool :=
  let solved := function.solvedRequirements
  decide (solved.map (·.id.index) = List.range solved.length) &&
    decide (solved.map (·.predicate) = expected) &&
    decide (function.predicates = expected) &&
    function.evidence == solved.map (·.evidence) &&
    solved.all fun requirement =>
      evidenceHasGoal requirement.predicate requirement.evidence &&
        decide (requirement.evidence.goal = requirement.predicate)

private def testAssumptionAndImplementationKeepPathIds : IO Unit := do
  let fixture ← check (String.intercalate "\n" [
    "trait Coerce<From, To> {}",
    "enum A { Only }",
    "enum B { Only }",
    "enum C { Only }",
    "impl Coerce<B, C> {}",
    "function accept(value: C) returns (C) { return value; }",
    "function convert(value: A) returns (C) where A: Coerce<B> {",
    "  return accept(value);",
    "}"
  ])
  let convert ← checkedNamed fixture "convert"
  let a ← namedType fixture.environment "A"
  let b ← namedType fixture.environment "B"
  let c ← namedType fixture.environment "C"
  let coerce ← namedTrait fixture.environment "Coerce"
  let first := predicate coerce a [b]
  let second := predicate coerce b [c]
  assertTrue (aligned convert [first, second])
    "multi-step coercion requirements lost contiguous path identities"
  match convert.solvedRequirements with
  | [{ evidence := .assumption _ , .. },
      { evidence := .implementation _, .. }] => pure ()
  | _ => throw (IO.userError
      "assumption and implementation evidence changed requirement order")

private def testCandidateForkCommitsOnlySelectedIds : IO Unit := do
  let fixture ← check (String.intercalate "\n" [
    "trait Ready<T> {}",
    "trait Coerce<From, To> {}",
    "trait Eq<T> {}",
    "enum Box { Only }",
    "enum Flag { Only }",
    "enum Token { Only }",
    "impl Ready<Word> {}",
    "impl Coerce<Word, Box> {}",
    "impl Eq<Token> {}",
    "function choose(value: Box) returns (Bool) { return true; }",
    "function choose(value: Flag) returns (Bool) { return true; }",
    "function choose<T>(value: T) returns (Bool) where T: Ready {",
    "  return true;",
    "}",
    "function run(value: Word, token: Token) returns (Bool) {",
    "  choose(value);",
    "  return token == token;",
    "}"
  ])
  let run ← checkedNamed fixture "run"
  let token ← namedType fixture.environment "Token"
  let ready ← namedTrait fixture.environment "Ready"
  let equality ← namedTrait fixture.environment "Eq"
  assertTrue (aligned run [predicate ready .word, predicate equality token])
    "failed or higher-cost candidates consumed committed requirement identities"

private def testFinalizeContinuesInferenceIds : IO Unit := do
  let fixture ← check (String.intercalate "\n" [
    "trait Add<T> {}",
    "trait Numeric<T> {}",
    "enum Box { Only }",
    "impl Add<Box> {}",
    "impl Numeric<Box> {}",
    "function compute(value: Box) returns (Box) { return value + 1; }"
  ])
  let compute ← checkedNamed fixture "compute"
  let box ← namedType fixture.environment "Box"
  let addition ← namedTrait fixture.environment "Add"
  let numeric ← namedTrait fixture.environment "Numeric"
  assertTrue (aligned compute [predicate addition box, predicate numeric box])
    "final numeric defaulting did not continue inference-time requirement IDs"

private def testRepeatedPredicatesKeepDistinctIds : IO Unit := do
  let fixture ← check (String.intercalate "\n" [
    "trait Eq<T> {}",
    "enum Token { Only }",
    "impl Eq<Token> {}",
    "function compareTwice(token: Token) returns (Bool) {",
    "  token == token;",
    "  return token == token;",
    "}"
  ])
  let compareTwice ← checkedNamed fixture "compareTwice"
  let token ← namedType fixture.environment "Token"
  let equality ← namedTrait fixture.environment "Eq"
  let equalityOnToken := predicate equality token
  assertTrue (aligned compareTwice [equalityOnToken, equalityOnToken])
    "repeated identical predicates were merged or shared a requirement identity"

/-- Exercise identity order across coercion paths, transactional overload
selection, and final numeric defaulting. -/
def testSourceRequirementIdentity : IO Unit := do
  testAssumptionAndImplementationKeepPathIds
  testCandidateForkCommitsOnlySelectedIds
  testFinalizeContinuesInferenceIds
  testRepeatedPredicatesKeepDistinctIds

end Tests.SourceRequirementIdentity
