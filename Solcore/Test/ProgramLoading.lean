import Solcore.Frontend.ProgramLoading

/-! Executable raw-workspace to declaration-environment regressions. -/

set_option autoImplicit false

namespace Tests

open Solcore Solcore.Frontend

private def assertTrue (condition : Bool) (label : String) : IO Unit := do
  unless condition do
    throw (IO.userError label)

private def validWorkspace : Workspace.RawWorkspace := {
  entry := "main.solc"
  mainSources := [
    { path := "main.solc", content := "type Main = lib.Remote;" },
    { path := "lib.solc", content := "enum Remote { Only }" }
  ]
  externalLibraries := []
}

private def testSuccessfulLoad : IO Unit := do
  match loadProgram validWorkspace with
  | .error errors =>
      throw (IO.userError s!"valid workspace failed to load: {reprStr errors}")
  | .ok loaded =>
      assertTrue (decide (loaded.sources.length = 2))
        "validated files were not all parsed"
      assertTrue (decide (loaded.environment.modules.length = 2 ∧
          loaded.environment.declarations.length = 2))
        "parsed files did not reach the declaration environment"
      assertTrue (decide (loaded.workspace.entry =
          { library := Workspace.LibraryId.main
            path := ⟨⟨[⟨"main", by decide⟩], by decide⟩⟩ }))
        "validated entry identity changed while loading"

private def testWorkspaceFailure : IO Unit := do
  let invalid := { validWorkspace with entry := "missing.solc" }
  match loadProgram invalid with
  | .error errors =>
      assertTrue (errors.any fun error => match error with
        | .workspace (.missingEntry _) => true
        | _ => false) "missing entry was not retained"
  | .ok _ => throw (IO.userError "invalid workspace was loaded")

private def testSourceDiagnostics : IO Unit := do
  let malformed := {
    validWorkspace with
    mainSources := [{ path := "main.solc", content := "type = ;" }]
  }
  match loadProgram malformed with
  | .error errors =>
      assertTrue (errors.any fun error => match error with
        | .sourceDiagnostics _ _ parsing => !parsing.isEmpty
        | _ => false) "ordinary source diagnostics were not retained"
  | .ok _ => throw (IO.userError "diagnostic source was loaded")

/-- Exercise validation, parsing and declaration collection as one API. -/
def testProgramLoading : IO Unit := do
  testSuccessfulLoad
  testWorkspaceFailure
  testSourceDiagnostics

end Tests
