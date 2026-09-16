import Solcore.Frontend.ProgramChecking

/-! End-to-end executable whole-program checking regressions. -/

set_option autoImplicit false

namespace Tests.ProgramChecking

open Solcore Solcore.Frontend

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do
    throw (IO.userError message)

private def successfulWorkspace : Workspace.RawWorkspace := {
  entry := "main.solc"
  mainSources := [
    {
      path := "traits.solc"
      content := String.intercalate "\n" [
        "trait Eq<T> {}",
        "impl Eq<Word> {}"
      ]
    },
    {
      path := "functions.solc"
      content := String.intercalate "\n" [
        "function keep<T>(value: T) returns (T) where T: Eq { return value; }",
        "function choose(value: Bool) returns (Bool) { return value; }",
        "function choose(value: Word) returns (Word) { return value + 1; }"
      ]
    },
    {
      path := "main.solc"
      content := "function run() returns (Word) { return choose(keep(41)); }"
    }
  ]
  externalLibraries := []
}

private def hasImplementationEvidence
    (function : SourceInference.CheckedFunction) : Bool :=
  function.evidence.any fun evidence => match evidence with
    | .implementation _ => true
    | .assumption _ => false

private def testSuccessfulProgram : IO Unit := do
  let checked ← match checkProgram successfulWorkspace with
    | .ok checked => pure checked
    | .error errors => throw (IO.userError
        s!"whole-program success fixture failed: {reprStr errors}")
  assertTrue (decide (checked.environment.modules.length = 3 ∧
      checked.signatures.functions.length = 4 ∧
      checked.signatures.implRules.length = 1 ∧
      checked.functions.length = 4))
    "whole-program summary omitted modules, overloads, impls, or bodies"
  assertTrue (decide (checked.functions.map (·.declaration) =
      checked.signatures.functions.map (·.id)))
    "checked functions did not preserve declaration order"
  let paired := checked.signatures.functions.zip checked.functions
  match paired.find? fun pair => pair.1.name == "run" with
  | none => throw (IO.userError "checked run function was not retained")
  | some (_, function) =>
      assertTrue (decide (function.inferredBodyType = TypeSystem.Ty.word))
        "overload selection or numeric literal defaulting changed run's type"
      assertTrue (hasImplementationEvidence function)
        "generic where predicate did not retain implementation evidence"

private def unsolvedTraitWorkspace : Workspace.RawWorkspace := {
  entry := "broken.solc"
  mainSources := [{
    path := "broken.solc"
    content := String.intercalate "\n" [
      "trait Add<T> {}",
      "enum Box { Only }",
      "function broken(value: Box) returns (Box) { return value + value; }"
    ]
  }]
  externalLibraries := []
}

private def testNoSolution : IO Unit := do
  match checkProgram unsolvedTraitWorkspace with
  | .error [.noSolution _ predicate] =>
      assertTrue (predicate.arguments.isEmpty)
        "unary operator-trait goal unexpectedly acquired arguments"
  | .error errors => throw (IO.userError
      s!"missing implementation had the wrong failure class: {reprStr errors}")
  | .ok _ => throw (IO.userError "missing Add implementation was accepted")

private def inconclusiveTraitWorkspace : Workspace.RawWorkspace := {
  entry := "ambiguous.solc"
  mainSources := [{
    path := "ambiguous.solc"
    content := String.intercalate "\n" [
      "trait Add<T> {}",
      "enum Box { Only }",
      "impl Add<Box> {}",
      "impl Add<Box> {}",
      "function ambiguous(value: Box) returns (Box) { return value + value; }"
    ]
  }]
  externalLibraries := []
}

private def testInconclusive : IO Unit := do
  match checkProgram inconclusiveTraitWorkspace with
  | .error [.inconclusive _ (.ambiguous _ _ _)] => pure ()
  | .error errors => throw (IO.userError
      s!"overlapping impls had the wrong failure class: {reprStr errors}")
  | .ok _ => throw (IO.userError "overlapping Add implementations were selected")

private def singleSourceWorkspace (content : String) : Workspace.RawWorkspace := {
  entry := "main.solc"
  mainSources := [{ path := "main.solc", content }]
  externalLibraries := []
}

private def testStageClassification : IO Unit := do
  let missingEntry := {
    singleSourceWorkspace "function ok() { return; }" with
    entry := "missing.solc"
  }
  match checkProgram missingEntry with
  | .error errors =>
      assertTrue (errors.any fun error => match error with
        | .loading _ => true
        | _ => false) "workspace failure was not classified as loading"
  | .ok _ => throw (IO.userError "missing entry reached source inference")
  match checkProgram (singleSourceWorkspace
      "function bad(value: Missing) { return; }") with
  | .error errors =>
      assertTrue (errors.any fun error => match error with
        | .signature _ => true
        | _ => false) "type-name failure was not classified as signature"
  | .ok _ => throw (IO.userError "unknown signature type was accepted")
  match checkProgram (singleSourceWorkspace
      "function bad() returns (Word) { return missing; }") with
  | .error errors =>
      assertTrue (errors.any fun error => match error with
        | .inference _ => true
        | _ => false) "ordinary body failure was not classified as inference"
  | .ok _ => throw (IO.userError "unknown body variable was accepted")

/-- Exercise the complete raw-workspace pipeline, including generics,
overloads, calls, predicates, implementation evidence, and numeric literals. -/
def testProgramChecking : IO Unit := do
  testSuccessfulProgram
  testNoSolution
  testInconclusive
  testStageClassification

end Tests.ProgramChecking
