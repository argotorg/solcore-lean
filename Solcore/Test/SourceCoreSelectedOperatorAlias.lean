import Solcore.Frontend.SourceCompiler

set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreSelectedOperatorAlias
open Solcore Solcore.Frontend Solcore.Frontend.SourceInference

private def provider : String := String.intercalate "\n" [
  "export {*};",
  "enum Box { Only }",
  "trait Weird<T> { function add(left: T, right: T) returns (T); }",
  "impl Weird<Box> { function add(left: Box, right: Box) returns (Box) { return left; }"
    ++ " }"
]

private def consumer : String := String.intercalate "\n" [
  "import {Box, Weird as Add} from provider;",
  "function run(value: Box) returns (Box) { return value + value; }",
  "function identity(value: Box) returns (Box) { return value; }"
]

private def workspace : Workspace.RawWorkspace := {
  entry := "consumer.solc"
  mainSources := [{path := "provider.solc", content := provider},
    {path := "consumer.solc", content := consumer}]
  externalLibraries := []
}

private def require (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def get {α ε : Type} [Repr ε] (label : String) : Except ε α → IO α
  | .ok value => pure value
  | .error error => throw (IO.userError s!"{label}: {reprStr error}")

/-- Imported operator names retain their original trait identity. The selected
compiler checks that identity's declared interface before executing the site. -/
def run : IO Unit := do
  let program ← get "alias checker" (Frontend.checkProgram workspace 1000)
  require (program.functions.length == 2 && program.methods.length == 1)
    "alias checker changed the complete program"
  let trait ← match program.signatures.traits.find? (·.name == "Weird") with
    | some trait => pure trait
    | none => throw (IO.userError "original Weird declaration missing")
  let caller ← match program.signatures.functions.find? (·.name == "run") with
    | some caller => pure caller
    | none => throw (IO.userError "operator caller missing")
  let checked ← match program.functions.find? (·.declaration == caller.id) with
    | some checked => pure checked
    | none => throw (IO.userError "checked operator caller missing")
  let primary ← match checked.typedBody.nodes.findSome? fun
      | .expression node => match node.form, node.requirements with
        | .binary _ .add _, primary :: _ => some primary
        | _, _ => none
      | _ => none with
    | some primary => pure primary
    | none => throw (IO.userError "original operator primary missing")
  match checked.solvedRequirements.filter (·.id == primary) with
  | [solved] =>
      require (solved.predicate.trait == .declaration trait.id)
        "checker replaced the original imported trait identity"
  | _ => throw (IO.userError "operator primary is not uniquely solved")
  let options : SourceCompiler.Options :=
    {checkingFuel := 1000, compilationFuel := 1000, specializationBudget := 256}
  match SourceCompiler.compileChecked program [.declaration caller.id] options with
  | .error (.compilation (.planEvidence (.runtimeBinaryTraitNameMismatch _ _ expected actual))) =>
      require (expected == "Add" && actual == "Weird")
        "selected operator rejection changed its exact interface names"
  | .error error => throw (IO.userError s!"unexpected operator rejection: {reprStr error}")
  | .ok _ => throw (IO.userError "mismatched selected operator compiled")
  let identity ← match program.signatures.functions.find? (·.name == "identity") with
    | some identity => pure identity
    | none => throw (IO.userError "identity declaration missing")
  let compiled ← get "unrelated identity compilation"
    (SourceCompiler.compileChecked program [.declaration identity.id] options)
  let key ← match compiled.keys with
    | [key] => pure key
    | _ => throw (IO.userError "identity root changed")
  let box ← match program.signatures.dataTypes.find? (·.name == "Box") with
    | some box => pure box
    | none => throw (IO.userError "Box declaration missing")
  let value : SourceCompiler.Value :=
    .constructed ⟨⟨box.id, 0⟩, [], [], .nominal box.id []⟩ []
  let artifact ← compiled.open
  let bootstrap ← artifact.bootstrap
  let session ← match bootstrap.resume 300000 with
    | .ready session => pure session
    | .error error => throw (IO.userError s!"identity bootstrap: {reprStr error}")
    | .outOfFuel _ => throw (IO.userError "identity bootstrap exhausted")
  let outcome ← get "identity execution"
    (← session.run key [value]
      {inputValidationFuel := 1024, executionFuel := 300000, outputValidationFuel := 1024})
  match outcome with
  | .succeeded completion =>
      require (completion.value == value) "identity changed the original constructor value"
  | _ => throw (IO.userError "unrelated identity did not execute")
  IO.println "SELECTED_OPERATOR_ALIAS_PASS checker=Weird rejected=Add/Weird identity=Box.Only"

end Tests.SourceCoreSelectedOperatorAlias
