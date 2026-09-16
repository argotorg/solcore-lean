import Solcore.Frontend.SourceInference

/-!
Focused end-to-end regressions for overload ranking when an argument is an
otherwise unconstrained numeric literal.

`Word` is the zero-cost literal default.  A non-`Word` parameter is viable
only through the conventional unary `FromLiteral`/`Numeric` trait, and such a
conversion has a strictly greater cost.  Equal-cost converted candidates stay
ambiguous.
-/

set_option autoImplicit false

namespace Tests.SourceLiteralOverloadRanking

open Solcore Solcore.Frontend

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do
    throw (IO.userError message)

private def rawWorkspace (lines : List String) : Workspace.RawWorkspace := {
  entry := "main.solc"
  mainSources := [{
    path := "main.solc"
    content := String.intercalate "\n" lines
  }]
  externalLibraries := []
}

private def checkProgram (lines : List String) :
    IO (List SourceInference.CheckedFunction) := do
  match SourceInference.loadAndCheckProgram (rawWorkspace lines) with
  | .ok checked => pure checked
  | .error errors =>
      throw (IO.userError s!"literal overload fixture failed: {reprStr errors}")

private def hasImplementationEvidence
    (function : SourceInference.CheckedFunction) : Bool :=
  function.evidence.any fun evidence => match evidence with
    | .implementation _ => true
    | .assumption _ => false

private def expectLastChecked (lines : List String) :
    IO SourceInference.CheckedFunction := do
  match (← checkProgram lines).getLast? with
  | some function => pure function
  | none => throw (IO.userError "literal overload fixture checked no functions")

private def testWordBeatsTraitBackedLiteral : IO Unit := do
  let run ← expectLastChecked [
    "trait FromLiteral<T> {}",
    "enum Box { Only }",
    "impl FromLiteral<Box> {}",
    "function choose(value: Box) returns (Bool) { return true; }",
    "function choose(value: Word) returns (Bool) { return true; }",
    "function run() returns (Bool) { return choose(1); }"
  ]
  assertTrue (decide (run.inferredBodyType = TypeSystem.Ty.bool))
    "Word-preferred literal overload changed run's result type"
  assertTrue (run.predicates.isEmpty && run.evidence.isEmpty)
    "Word-preferred literal overload retained converted-candidate evidence"

private def testSoleNumericCandidateRetainsEvidence : IO Unit := do
  let run ← expectLastChecked [
    "trait Numeric<T> {}",
    "enum Box { Only }",
    "impl Numeric<Box> {}",
    "function choose(value: Box) returns (Bool) { return true; }",
    "function run() returns (Bool) { return choose(1); }"
  ]
  assertTrue (decide (run.predicates.length = 1))
    "sole trait-backed literal candidate lost its Numeric predicate"
  assertTrue (hasImplementationEvidence run)
    "sole trait-backed literal candidate lost implementation evidence"

private def testEqualCostConvertedCandidatesStayAmbiguous : IO Unit := do
  let lines := [
    "trait FromLiteral<T> {}",
    "enum Box { Only }",
    "enum Crate { Only }",
    "impl FromLiteral<Box> {}",
    "impl FromLiteral<Crate> {}",
    "function choose(value: Box) returns (Bool) { return true; }",
    "function choose(value: Crate) returns (Bool) { return true; }",
    "function run() returns (Bool) { return choose(1); }"
  ]
  match SourceInference.loadAndCheckProgram (rawWorkspace lines) with
  | .error errors =>
      assertTrue (errors.any fun error => match error with
        | .body { error := .ambiguousOverload "choose" candidates, .. } =>
            candidates.length == 2
        | _ => false)
        "equal-cost converted literal candidates lost overload ambiguity"
  | .ok _ =>
      throw (IO.userError "equal-cost converted literal candidates were ranked")

private def testInapplicableBoolDoesNotBlockWord : IO Unit := do
  let run ← expectLastChecked [
    "function choose(value: Bool) returns (Bool) { return value; }",
    "function choose(value: Word) returns (Bool) { return true; }",
    "function run() returns (Bool) { return choose(1); }"
  ]
  assertTrue (decide (run.inferredBodyType = TypeSystem.Ty.bool))
    "inapplicable Bool overload blocked the Word literal candidate"
  assertTrue (run.predicates.isEmpty && run.evidence.isEmpty)
    "inapplicable Bool overload introduced literal evidence"

/-- Exercise literal-default-aware overload viability, ranking, evidence, and
equal-cost ambiguity through the complete parsed-source checking path. -/
def testSourceLiteralOverloadRanking : IO Unit := do
  testWordBeatsTraitBackedLiteral
  testSoleNumericCandidateRetainsEvidence
  testEqualCostConvertedCandidatesStayAmbiguous
  testInapplicableBoolDoesNotBlockWord

end Tests.SourceLiteralOverloadRanking
