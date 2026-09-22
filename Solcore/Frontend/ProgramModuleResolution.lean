import Solcore.Frontend.ProgramEnvironment

/-!
Canonical module-path resolution shared by imports and re-exports.

Unmarked paths are relative to the importing module's directory.  A leading
`lib` on a multi-component path starts at the current library root; bare `lib`
remains relative.  `std` selects the standard library, with the canonical
local-relative fallback only for a multi-component path whose standard module
does not exist.  An externally marked path selects the named external library.
Resolution is purely over the already validated whole-program module set.
-/

set_option autoImplicit false

namespace Solcore.Frontend

/-- Exact source spelling components of a parsed module path. -/
def programModulePathComponents (path : Syntax.ModulePath) : List String :=
  path.value.components.toList.map (·.value)

/-- Exact source spelling components of a parsed export module reference. -/
def programExportPathComponents (path : Syntax.QualifiedName) : List String :=
  path.value.components.toList.map (·.value)

private def modulePathComponents (moduleId : Workspace.ModuleId) : List String :=
  moduleId.path.segments.map (·.text)

private def moduleDirectory (moduleId : Workspace.ModuleId) : List String :=
  (modulePathComponents moduleId).dropLast

private def moduleWithIdentity?
    (environment : ProgramEnvironment) (library : Workspace.LibraryId)
    (components : List String) : Option Workspace.ModuleId :=
  (environment.modules.find? fun module =>
    decide (module.id.library = library) &&
      modulePathComponents module.id == components).map (·.id)

private def externalLibraryNamed?
    (environment : ProgramEnvironment) (name : String) :
    Option Workspace.LibraryId :=
  (environment.modules.findSome? fun module =>
    match module.id.library with
    | .external external =>
        if external.render == name then some module.id.library else none
    | _ => none)

/-- Resolve a source module path to one loaded canonical module identity.

`external = true` means the first component names an external library.  The
remaining cases follow the canonical relative / `lib` / `std` path policy.
-/
def resolveProgramModuleComponents?
    (environment : ProgramEnvironment) (owner : Workspace.ModuleId)
    (external : Bool) (components : List String) : Option Workspace.ModuleId :=
  if external then
    match components with
    | [] => none
    | libraryName :: rest => do
        let library ← externalLibraryNamed? environment libraryName
        let logicalPath := if rest.isEmpty then [libraryName] else rest
        moduleWithIdentity? environment library logicalPath
  else
    match components with
    | "std" :: rest =>
        let standardPath := if rest.isEmpty then ["std"] else rest
        match moduleWithIdentity? environment .standard standardPath with
        | some target => some target
        | none =>
            if rest.isEmpty then none
            else
              moduleWithIdentity? environment owner.library
                (moduleDirectory owner ++ components)
    | "lib" :: rest =>
        if rest.isEmpty then
          moduleWithIdentity? environment owner.library
            (moduleDirectory owner ++ components)
        else
          moduleWithIdentity? environment owner.library rest
    | _ =>
        moduleWithIdentity? environment owner.library
          (moduleDirectory owner ++ components)

/-- Resolve a canonical import declaration's module path. -/
def resolveProgramModulePath?
    (environment : ProgramEnvironment) (owner : Workspace.ModuleId)
    (path : Syntax.ModulePath) : Option Workspace.ModuleId :=
  resolveProgramModuleComponents? environment owner
    path.value.externalMarker.isSome (programModulePathComponents path)

/-- Resolve an export-side module reference in the owner's library policy. -/
def resolveProgramExportPath?
    (environment : ProgramEnvironment) (owner : Workspace.ModuleId)
    (path : Syntax.QualifiedName) : Option Workspace.ModuleId :=
  resolveProgramModuleComponents? environment owner false
    (programExportPathComponents path)

end Solcore.Frontend
