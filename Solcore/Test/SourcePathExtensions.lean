import Solcore.Frontend.ProgramLoading

/-! Canonical Rust source paths retain exact provenance and share module names with legacy paths. -/
set_option autoImplicit false
namespace Tests.SourcePathExtensions
open Solcore Solcore.Frontend

private def require (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def parse (text : String) : IO Workspace.CanonicalSourcePath :=
  match Workspace.CanonicalSourcePath.parse text with
  | some path => pure path
  | none => throw (IO.userError s!"source path rejected: {text}")

private def source : String := "function main() returns (word) { return 7; }"

private def raw (entry : String) (sources : List Workspace.RawSourceFile) : Workspace.RawWorkspace :=
  {entry, mainSources := sources, externalLibraries := []}

def run : IO Unit := do
  for stem in ["main", "nested/Module_1", "function"] do
    let canonical ← parse (stem ++ ".sol")
    let legacy ← parse (stem ++ ".solc")
    require (canonical.extension == .sol && legacy.extension == .solc)
      "source path parser lost its exact extension"
    require (canonical.render == stem ++ ".sol" && legacy.render == stem ++ ".solc")
      "source path renderer changed its original spelling"
    require (canonical.modulePath == legacy.modulePath && canonical != legacy)
      "source and module identity no longer distinguish suffix spelling"
    let canonicalId : Workspace.SourceId := {library := .main, path := canonical}
    let legacyId : Workspace.SourceId := {library := .main, path := legacy}
    require (canonicalId.toModuleId == legacyId.toModuleId)
      "source extensions created distinct module identities"
    require ((syntaxSourceIdOfWorkspaceSource canonicalId).path == stem ++ ".sol")
      "parser-boundary provenance rewrote a canonical source path"
  for suffix in ["sol", "solc"] do
    let path := "main." ++ suffix
    match loadProgram (raw path [{path, content := source}]) with
    | .error errors => throw (IO.userError s!"source loading failed: {reprStr errors}")
    | .ok loaded =>
      require (loaded.sources.map (·.source.path) == [path])
        "loaded program lost source suffix provenance"
      require (loaded.environment.modules.length == 1) "source loading lost its module"
  match loadProgram (raw "main.sol" [
      {path := "main.sol", content := source}, {path := "main.solc", content := source}]) with
  | .error [.environment (.duplicateModule _)] => pure ()
  | result => throw (IO.userError s!"mixed suffix module collision was not rejected: {reprStr result}")
  match loadProgram (raw "main.sol" [{path := "main.solc", content := source}]) with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError "entry matching silently substituted the legacy source path")
  for path in [".sol", "a/.sol", "a.SOL", "a.sol.sol", "a.solc.sol", "a.sol.solc", "../a.sol", "a//b.sol"] do
    require (Workspace.CanonicalSourcePath.parse path).isNone s!"malformed canonical path accepted: {path}"

end Tests.SourcePathExtensions
