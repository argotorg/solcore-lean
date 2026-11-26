import Solcore.Frontend.SourceCompiler

/-!
# Selected operator alias tests

An operator's trait is the trait declared with the operator's name, whatever a scope calls it. A
trait imported as `Add` under another declared name is not `Add`, so `+` at its type is refused at
inference; the declared `Add` imported as `Plus` is `+`'s trait, and its implementation runs.
-/

set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreSelectedOperatorAlias
open Solcore Solcore.Frontend Solcore.Frontend.SourceInference

/-- A provider of `Box`, its `Weird` trait, declared with `add` but not named `Add`, and the
declared `Add`, both implemented at `Box` by their left operand. -/
private def provider : String := String.intercalate "\n" [
  "export {*};",
  "enum Box { Only }",
  "trait Weird<T> { function add(left: T, right: T) returns (T); }",
  "impl Weird<Box> { function add(left: Box, right: Box) returns (Box) { return left; }"
    ++ " }",
  "trait Add<T> { function add(left: T, right: T) returns (T); }",
  "impl Add<Box> { function add(left: Box, right: Box) returns (Box) { return left; } }"
]

private def workspace (consumer : List String) : Workspace.RawWorkspace := {
  entry := "consumer.solc"
  mainSources := [{path := "provider.solc", content := "pragma solcore;\n" ++ provider},
    {path := "consumer.solc", content := "pragma solcore;\n" ++ String.intercalate "\n" consumer}]
  externalLibraries := []
}

private def require (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def get {α ε : Type} [Repr ε] (label : String) : Except ε α → IO α
  | .ok value => pure value
  | .error error => throw (IO.userError s!"{label}: {reprStr error}")

private def options : SourceCompiler.Options :=
  {checkingFuel := 1000, compilationFuel := 1000, specializationBudget := 256}

/-- The function named `name` compiled alone and run at `Box.Only`, which it must return. -/
private def runsToOnly (program : CheckedProgram) (name : String) : IO Unit := do
  let function ← match program.signatures.functions.find? (·.name == name) with
    | some function => pure function
    | none => throw (IO.userError s!"{name} declaration missing")
  let compiled ← get s!"{name} compilation"
    (SourceCompiler.compileChecked program [.declaration function.id] options)
  let key ← match compiled.keys with
    | [key] => pure key
    | _ => throw (IO.userError s!"{name} root changed")
  let box ← match program.signatures.dataTypes.find? (·.name == "Box") with
    | some box => pure box
    | none => throw (IO.userError "Box declaration missing")
  let value : SourceCompiler.Value :=
    .constructed ⟨⟨box.id, 0⟩, [], [], .nominal box.id []⟩ []
  let artifact ← compiled.open
  let bootstrap ← artifact.bootstrap
  let session ← match bootstrap.resume 300000 with
    | .ready session => pure session
    | .error error => throw (IO.userError s!"{name} bootstrap: {reprStr error}")
    | .outOfFuel _ => throw (IO.userError s!"{name} bootstrap exhausted")
  let outcome ← get s!"{name} execution"
    (← session.run key [value]
      {inputValidationFuel := 1024, executionFuel := 300000, outputValidationFuel := 1024})
  match outcome with
  | .succeeded completion =>
      require (completion.value == value) s!"{name} changed the original constructor value"
  | _ => throw (IO.userError s!"{name} did not execute")

def run : IO Unit := do
  -- `Weird` imported as `Add` is not the declared `Add`, so `+` at `Box` has no trait.
  match Frontend.checkProgram (workspace ["import {Box, Weird as Add} from provider;",
      "function run(value: Box) returns (Box) { return value + value; }"]) 1000 with
  | .error errors =>
      require (errors.any fun error => match error with
        | .inference { error := .operatorNotSupported "Add" _, .. } => true
        | _ => false) s!"an aliased Weird was not refused as Add: {reprStr errors}"
  | .ok _ => throw (IO.userError "an aliased Weird was taken as Add")
  -- An unrelated function beside the alias still runs.
  let aliased ← get "alias beside an unrelated function" (Frontend.checkProgram (workspace
    ["import {Box, Weird as Add} from provider;",
      "function identity(value: Box) returns (Box) { return value; }"]) 1000)
  runsToOnly aliased "identity"
  -- The declared `Add` imported as `Plus` is `+`'s trait, and its implementation runs.
  let renamed ← get "Add imported as Plus" (Frontend.checkProgram (workspace
    ["import {Box, Add as Plus} from provider;",
      "function run(value: Box) returns (Box) { return value + value; }"]) 1000)
  let trait ← match renamed.signatures.traits.find? (·.name == "Add") with
    | some trait => pure trait
    | none => throw (IO.userError "the declared Add is missing")
  let caller ← match renamed.signatures.functions.find? (·.name == "run") with
    | some caller => pure caller
    | none => throw (IO.userError "operator caller missing")
  let checked ← match renamed.functions.find? (·.declaration == caller.id) with
    | some checked => pure checked
    | none => throw (IO.userError "checked operator caller missing")
  let primary ← match checked.typedBody.nodes.findSome? fun
      | .expression node => match node.form, node.requirements with
        | .binary _ .add _, primary :: _ => some primary
        | _, _ => none
      | _ => none with
    | some primary => pure primary
    | none => throw (IO.userError "the operator's primary requirement is missing")
  match checked.solvedRequirements.filter (·.id == primary) with
  | [solved] =>
      require (solved.predicate.trait == .declaration trait.id)
        "the operator's requirement is not the declared Add"
  | _ => throw (IO.userError "the operator's primary requirement is not uniquely solved")
  runsToOnly renamed "run"
  IO.println "SELECTED_OPERATOR_ALIAS_PASS Weird-as-Add refused, identity=Box.Only, Add-as-Plus runs"

end Tests.SourceCoreSelectedOperatorAlias
