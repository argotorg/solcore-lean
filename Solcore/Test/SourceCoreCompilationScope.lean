import Solcore.Frontend.SourceCompiler

/-! Selected compilation keeps unrelated inference-only declarations in the
checked source program. Public execution uses the selected dependency closure. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreCompilationScope
open Solcore Frontend SourceInference

def source : String := String.intercalate "\n" [
  "trait Coerce<From, To> {}",
  "enum Box { Only }",
  "impl Coerce<Word, Box> {}",
  "function convert(value: Word) returns (Box) { return value; }",
  "function identity(value: Word) returns (Word) { return value; }"
]

def workspace : Workspace.RawWorkspace := {
  entry := "main.solc"
  mainSources := [{ path := "main.solc", content := source }]
  externalLibraries := []
}

def options : SourceCompiler.Options := {
  checkingFuel := 1000, compilationFuel := 1000, specializationBudget := 256
}

def run : IO Unit := do
  let program ← match checkProgram workspace options.checkingFuel with
    | .ok program => pure program
    | .error errors => throw (IO.userError s!"scope fixture rejected by checker: {reprStr errors}")
  unless program.functions.length == 2 && program.methods.isEmpty do
    throw (IO.userError "scope fixture changed its declaration inventory")
  let some conversion := program.signatures.functions.find? (fun row => row.name == "convert")
    | throw (IO.userError "conversion signature missing")
  let some identity := program.signatures.functions.find? (fun row => row.name == "identity")
    | throw (IO.userError "identity signature missing")
  match SourceCompiler.compileChecked program [.declaration conversion.id] options with
  | .error (.compilation (.planEvidence (.executableCoercionMethod _ _ _
      (.missingTraitMethod _ "coerce")))) => pure ()
  | .error error => throw (IO.userError s!"unexpected conversion failure: {reprStr error}")
  | .ok _ => throw (IO.userError "conversion without an executable method was accepted")
  let compiled ← match SourceCompiler.compileChecked program [.declaration identity.id] options with
    | .ok compiled => pure compiled
    | .error error => throw (IO.userError s!"unrelated selected function rejected: {reprStr error}")
  unless compiled.program.functions.length == 2 do
    throw (IO.userError "compilation discarded the original source program")
  unless compiled.plan.specializations.map (·.declaration) == [identity.id] do
    throw (IO.userError "unselected conversion entered the specialization plan")
  let [key] := compiled.keys | throw (IO.userError "selected root inventory changed")
  let artifact ← compiled.open
  let bootstrap ← artifact.bootstrap
  let .ready session := bootstrap.resume 10000
    | throw (IO.userError "selected scope initialization did not complete")
  match ← session.run key [.word (Core.Word.ofNatModulo 37)]
      { executionFuel := 10000 } with
  | .ok (.succeeded completion) =>
      unless completion.value == .word (Core.Word.ofNatModulo 37) do
        throw (IO.userError "selected scope returned the wrong value")
  | _ => throw (IO.userError "selected scope public execution did not succeed")
  IO.println "COMPILATION_SCOPE_BOUNDARY_PASS"

end Tests.SourceCoreCompilationScope
