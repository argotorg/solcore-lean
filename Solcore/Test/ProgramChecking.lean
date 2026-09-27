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
        "export {Eq};",
        "trait Eq<T> {}",
        "impl Eq<Word> {}"
      ]
    },
    {
      path := "functions.solc"
      content := String.intercalate "\n" [
        "import {Eq} from traits;",
        "export {keep, choose};",
        "function keep<T>(value: T) returns (T) where T: Eq { return value; }",
        "function choose(value: Bool) returns (Bool) { return value; }",
        "function choose(value: Word) returns (Word) { return value + 1; }"
      ]
    },
    {
      path := "main.solc"
      content := String.intercalate "\n" [
        "import {keep, choose} from functions;",
        "function run() returns (Word) { return choose(keep(41)); }"
      ]
    }
  ]
  externalLibraries := []
}

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
      let equality ← match checked.environment.traitsNamed "Eq" with
        | [declaration] => pure declaration.id
        | declarations => throw (IO.userError
            s!"expected one Eq trait, found {declarations.length}")
      let equalityPredicate : ProgramPredicate := {
        trait := equality
        subject := .word
        arguments := []
      }
      let integerPredicate :=
        ProgramSignatures.builtinIntPredicate TypeSystem.Ty.word
      assertTrue (decide (function.inferredBodyType = TypeSystem.Ty.word))
        "overload selection or integer-literal resolution changed run's type"
      assertTrue (function.solvedRequirements.any fun solved =>
          solved.predicate == equalityPredicate &&
            match solved.evidence with
            | .implementation
                (.byImpl goal (.declaration _) premises) =>
                goal == equalityPredicate && premises.isEmpty
            | _ => false)
        "generic where predicate did not retain implementation evidence"
      assertTrue (function.solvedRequirements.any fun solved =>
          solved.predicate == integerPredicate &&
            match solved.evidence with
            | .implementation (.byImpl goal (.builtin .intWord) premises) =>
                goal == integerPredicate && premises.isEmpty
            | _ => false)
        "nested literal did not retain builtin Int<Word> evidence"

private def importedTypeWorkspace : Workspace.RawWorkspace := {
  entry := "main.solc"
  mainSources := [
    {
      path := "models.solc"
      content := "export {*}; enum Box { Only }"
    },
    {
      path := "main.solc"
      content := String.intercalate "\n" [
        "import * from models;",
        "function echo(value: Box) returns (Box) { return value; }"
      ]
    }
  ]
  externalLibraries := []
}

private def testImportedTypeProgram : IO Unit := do
  let checked ← match checkProgram importedTypeWorkspace with
    | .ok checked => pure checked
    | .error errors => throw (IO.userError
        s!"imported whole-program fixture failed: {reprStr errors}")
  match checked.signatures.functions with
  | [signature] =>
      assertTrue (decide (signature.parameterTypes = signature.returnTypes))
        "imported type resolved inconsistently across a function signature"
  | _ => throw (IO.userError "imported fixture lost its function signature")

private def unsolvedTraitWorkspace : Workspace.RawWorkspace := {
  entry := "broken.solc"
  mainSources := [{
    path := "broken.solc"
    content := String.intercalate "\n" [
      "trait Add<T> {",
      "  function add(left: T, right: T) returns (T);",
      "}",
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
      "trait Add<T> {",
      "  function add(left: T, right: T) returns (T);",
      "}",
      "enum Box { Only }",
      "impl Add<Box> {",
      "  function add(left: Box, right: Box) returns (Box) { return left; }",
      "}",
      "impl Add<Box> {",
      "  function add(left: Box, right: Box) returns (Box) { return right; }",
      "}",
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

private def defaultImplementationWorkspace : Workspace.RawWorkspace := {
  entry := "main.solc"
  mainSources := [{
    path := "main.solc"
    content := String.intercalate "\n" [
      "trait Ready<T> {}",
      "trait Select<T> {}",
      "default impl<T> Select<T> {}",
      "impl Select<Word> {}",
      "impl Select<Bool> where Bool: Ready {}",
      "function select<T>(value: T) returns (T) where T: Select { return value; }",
      "function selectWord(value: Word) returns (Word) { return select(value); }",
      "function selectBool(value: Bool) returns (Bool) { return select(value); }"
    ]
  }]
  externalLibraries := []
}

private def testDefaultImplementationPriority : IO Unit := do
  let checked ← match checkProgram defaultImplementationWorkspace with
    | .ok checked => pure checked
    | .error errors => throw (IO.userError
        s!"default implementation program failed: {reprStr errors}")
  let fallback ← match checked.signatures.implementations.find? fun implementation =>
      implementation.isDefault with
    | some implementation => pure implementation
    | none => throw (IO.userError "default implementation was not retained")
  let wordSpecific ← match checked.signatures.implementations.find? fun implementation =>
      !implementation.isDefault && implementation.head.subject == .word with
    | some implementation => pure implementation
    | none => throw (IO.userError "specific Word implementation was not retained")
  let failedBoolSpecific ← match checked.signatures.implementations.find?
      fun implementation =>
        !implementation.isDefault && implementation.head.subject == .bool with
    | some implementation => pure implementation
    | none => throw (IO.userError "conditional Bool implementation was not retained")
  let checkedNamed (name : String) := checked.functions.find? fun function =>
    match checked.environment.declaration? function.declaration with
    | some declaration => declaration.name == some name
    | none => false
  let wordFunction ← match checkedNamed "selectWord" with
    | some function => pure function
    | none => throw (IO.userError "selectWord was not checked")
  let boolFunction ← match checkedNamed "selectBool" with
    | some function => pure function
    | none => throw (IO.userError "selectBool was not checked")
  match wordFunction.solvedRequirements with
  | [{ evidence := .implementation
        (.byImpl _ (.declaration implementation) []), .. }] =>
      assertTrue (decide (implementation = wordSpecific.id))
        "a matching default implementation displaced the ordinary Word implementation"
  | requirements => throw (IO.userError
      s!"selectWord evidence changed: {reprStr requirements}")
  match boolFunction.solvedRequirements with
  | [{ evidence := .implementation
        (.byImpl _ (.declaration implementation) []), .. }] =>
      assertTrue (decide (implementation = fallback.id ∧
          implementation ≠ failedBoolSpecific.id))
        "default implementation was not selected after the ordinary candidate failed"
  | requirements => throw (IO.userError
      s!"selectBool evidence changed: {reprStr requirements}")

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

private def testPhantomImplementationParameterRejection : IO Unit := do
  match checkProgram (singleSourceWorkspace (String.intercalate "\n" [
      "trait Identity<T> {}",
      "impl<T, U> Identity<T> {}"
    ])) with
  | .error [.signature
        (.implementationParameterNotInHead implementation parameter)] =>
      assertTrue (decide (parameter.owner = implementation ∧ parameter.index = 1))
        "phantom-parameter rejection lost its stable implementation identity"
  | .error errors => throw (IO.userError
      s!"phantom implementation had the wrong pipeline error: {reprStr errors}")
  | .ok _ => throw (IO.userError
      "a phantom implementation parameter reached body checking")

/-- Exercise the complete raw-workspace pipeline, including generics,
overloads, calls, predicates, implementation evidence, and integer literals. -/
def testProgramChecking : IO Unit := do
  testSuccessfulProgram
  testImportedTypeProgram
  testNoSolution
  testInconclusive
  testDefaultImplementationPriority
  testStageClassification
  testPhantomImplementationParameterRejection

end Tests.ProgramChecking
