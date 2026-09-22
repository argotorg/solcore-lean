import Solcore.Syntax.Parser
import Solcore.Frontend.ProgramModuleResolution

/-! Executable regressions for canonical relative and rooted module paths. -/

set_option autoImplicit false

namespace Tests

open Solcore Solcore.Frontend

namespace ProgramModuleResolution

private def assertTrue (condition : Bool) (label : String) : IO Unit := do
  unless condition do throw (IO.userError label)

private def parsed (origin : Syntax.SourceOrigin) (path content : String) :
    IO Syntax.ParsedFile := do
  let file : Syntax.SourceFile := { id := { origin, path }, content }
  match Syntax.Parser.parse file with
  | .error error => throw (IO.userError
      s!"{path}: parser invariant failed: {reprStr error}")
  | .ok output =>
      unless output.lexicalDiagnostics.isEmpty &&
          output.parseDiagnostics.isEmpty do
        throw (IO.userError
          s!"{path}: source diagnostics: {reprStr output.lexicalDiagnostics}; {reprStr output.parseDiagnostics}")
      pure output.parsed

private def moduleId (environment : ProgramEnvironment)
    (library : Workspace.LibraryId) (path : String) : IO Workspace.ModuleId := do
  match environment.modules.find? fun module =>
      decide (module.id.library = library) && module.id.path.render == path with
  | some module => pure module.id
  | none => throw (IO.userError s!"missing module {path}")

private def importPaths (module : ProgramModule) : List Syntax.ModulePath :=
  module.source.items.filterMap fun item =>
    match item.value with
    | .importDecl declaration =>
        some <| match declaration.value with
          | .plain path | .namespace path _ | .wildcard path _
          | .selected _ path _ => path
    | _ => none

private def exportPaths (module : ProgramModule) : List Syntax.QualifiedName :=
  module.source.items.filterMap fun item =>
    match item.value with
    | .exportDecl declaration =>
        match declaration.value with
        | .module path | .moduleAs path _ | .itemsFrom path _ => some path
        | .local _ => none
    | _ => none

private def testCanonicalPaths : IO Unit := do
  let owner ← parsed .main "pkg/nested/main.solc" (String.intercalate "\n" [
    "import util;",
    "import lib.shared.util;",
    "import std.math;",
    "import std.local;",
    "import @dep.tools;",
    "import @dep;",
    "import lib;",
    "import std;",
    "export util;",
    "export lib.shared.util;",
    "export std.math;"
  ])
  let relative ← parsed .main "pkg/nested/util.solc" "export {};"
  let rooted ← parsed .main "shared/util.solc" "export {};"
  let localStdFallback ← parsed .main "pkg/nested/std/local.solc" "export {};"
  let relativeLib ← parsed .main "pkg/nested/lib.solc" "export {};"
  let relativeStd ← parsed .main "pkg/nested/std.solc" "export {};"
  let standard ← parsed .standard "math.solc" "export {};"
  let standardRoot ← parsed .standard "std.solc" "export {};"
  let external ← parsed (.external "dep") "tools.solc" "export {};"
  let externalRoot ← parsed (.external "dep") "dep.solc" "export {};"
  let environment ← match buildProgramEnvironment
      [owner, relative, rooted, localStdFallback, relativeLib, relativeStd,
        standard, standardRoot, external, externalRoot] with
    | .ok environment => pure environment
    | .error errors => throw (IO.userError
        s!"environment failed: {reprStr errors}")
  let ownerId ← moduleId environment .main "pkg/nested/main"
  let ownerModule := environment.modules.find? fun module =>
    decide (module.id = ownerId)
  let some ownerModule := ownerModule
    | throw (IO.userError "owner module disappeared")
  let relativeId ← moduleId environment .main "pkg/nested/util"
  let rootedId ← moduleId environment .main "shared/util"
  let standardId ← moduleId environment .standard "math"
  let localStdId ← moduleId environment .main "pkg/nested/std/local"
  let relativeLibId ← moduleId environment .main "pkg/nested/lib"
  let standardRootId ← moduleId environment .standard "std"
  let some dependency := Workspace.ExternalLibraryName.parse "dep"
    | throw (IO.userError "dependency name did not parse")
  let externalId ← moduleId environment (.external dependency) "tools"
  let externalRootId ← moduleId environment (.external dependency) "dep"
  let expectedImports : List Workspace.ModuleId :=
    [relativeId, rootedId, standardId, localStdId, externalId, externalRootId,
      relativeLibId, standardRootId]
  let resolvedImports := (importPaths ownerModule).map fun path =>
    resolveProgramModulePath? environment ownerId path
  assertTrue (resolvedImports == expectedImports.map some)
    "relative, lib, std, std-fallback, or external import resolution changed"
  let expectedExports := expectedImports.take 3
  let resolvedExports := (exportPaths ownerModule).map fun path =>
    resolveProgramExportPath? environment ownerId path
  assertTrue (resolvedExports == expectedExports.map some)
    "import and export paths no longer share canonical resolution"

private def testBareStdDoesNotUseLocalFallback : IO Unit := do
  let owner ← parsed .main "pkg/nested/main.solc" "import std;"
  let localStd ← parsed .main "pkg/nested/std.solc" "export {};"
  let environment ← match buildProgramEnvironment [owner, localStd] with
    | .ok environment => pure environment
    | .error errors => throw (IO.userError
        s!"bare std environment failed: {reprStr errors}")
  let ownerId ← moduleId environment .main "pkg/nested/main"
  let ownerModule ← match environment.modules.find? fun module =>
      decide (module.id = ownerId) with
    | some module => pure module
    | none => throw (IO.userError "bare std owner disappeared")
  match importPaths ownerModule with
  | [path] =>
      assertTrue ((resolveProgramModulePath? environment ownerId path).isNone)
        "bare std incorrectly used the nested local fallback"
  | paths => throw (IO.userError
      s!"bare std fixture retained {paths.length} import paths")

end ProgramModuleResolution

/-- Run canonical module-path resolution regressions. -/
def testProgramModuleResolution : IO Unit := do
  ProgramModuleResolution.testCanonicalPaths
  ProgramModuleResolution.testBareStdDoesNotUseLocalFallback

end Tests
