import Solcore.Frontend.ProgramEnvironment

/-!
Direct import visibility for the executable whole-program environment.

This layer intentionally stops before exports and re-exports.  It resolves
canonical import module paths and direct visibility in the type, trait, and
value namespaces.  Value imports preserve overload sets; operator selectors
use their spelling as a value-namespace name.
-/

set_option autoImplicit false

namespace Solcore.Frontend

/-- One imported namespace spelling and the module it denotes. -/
structure ProgramImportedNamespace where
  localName : String
  target : Workspace.ModuleId
  deriving Repr, DecidableEq

/-- One unqualified imported type spelling. -/
structure ProgramImportedType where
  localName : String
  declaration : ProgramDeclaration
  deriving Repr

/-- One unqualified imported trait spelling. -/
structure ProgramImportedTrait where
  localName : String
  declaration : ProgramDeclaration
  deriving Repr

/-- One unqualified imported value spelling.  Several rows may form an
overload set under the same local name. -/
structure ProgramImportedValue where
  localName : String
  declaration : ProgramDeclaration
  deriving Repr

/-- Direct visibility contributed by all imports in one source module. -/
structure ProgramImports where
  hasImports : Bool := false
  namespaces : List ProgramImportedNamespace := []
  types : List ProgramImportedType := []
  traits : List ProgramImportedTrait := []
  values : List ProgramImportedValue := []
  deriving Repr

/-- Import construction failures which cannot be interpreted as name absence. -/
inductive ProgramImportError where
  | unknownModule
      (importer : Workspace.ModuleId)
      (external : Bool)
      (components : List String)
  | ambiguousModule
      (importer : Workspace.ModuleId)
      (external : Bool)
      (components : List String)
      (candidates : List Workspace.ModuleId)
  | unknownSelectedType
      (importer target : Workspace.ModuleId)
      (name : String)
  | ambiguousSelectedType
      (importer target : Workspace.ModuleId)
      (name : String)
      (candidates : List Resolved.DeclarationId)
  | ambiguousSelectedTrait
      (importer target : Workspace.ModuleId)
      (name : String)
      (candidates : List Resolved.DeclarationId)
  deriving Repr, DecidableEq

/-- Spelling components of one parsed import module path. -/
def programImportModuleComponents (path : Syntax.ModulePath) : List String :=
  path.value.components.toList.map (·.value)

private def workspaceModulePathComponents
    (moduleId : Workspace.ModuleId) : List String :=
  moduleId.path.segments.map (·.text)

private def externalModuleMatches
    (components : List String) (moduleId : Workspace.ModuleId) : Bool :=
  match components, moduleId.library with
  | library :: path, .external name =>
      library == name.render && path == workspaceModulePathComponents moduleId
  | _, _ => false

private def sameLibraryModuleMatches
    (importer : Workspace.ModuleId) (components : List String)
    (moduleId : Workspace.ModuleId) : Bool :=
  decide (moduleId.library = importer.library) &&
    components == workspaceModulePathComponents moduleId

/-- Resolve a direct import path against canonical program modules. -/
def resolveProgramImportModule
    (environment : ProgramEnvironment) (importer : Workspace.ModuleId)
    (path : Syntax.ModulePath) : Except ProgramImportError Workspace.ModuleId :=
  let components := programImportModuleComponents path
  let external := path.value.externalMarker.isSome
  let candidates := environment.modules.filterMap fun module =>
    let isMatch :=
      if external then
        externalModuleMatches components module.id
      else
        sameLibraryModuleMatches importer components module.id
    if isMatch then some module.id else none
  match candidates with
  | [] => .error (.unknownModule importer external components)
  | [target] => .ok target
  | _ => .error (.ambiguousModule importer external components candidates)

private def selectorSpelling (selector : Syntax.SelectorName) : String :=
  match selector.value with
  | .identifier name => name.value
  | .operator spelling => spelling

private def hiddenSelectorNames
    (clause : Option Syntax.HidingClause) : List String :=
  match clause with
  | none => []
  | some clause => clause.value.names.toList.map selectorSpelling

private def isHidden (hidden : List String) (source localName : String) : Bool :=
  hidden.contains source || hidden.contains localName

private def targetTypes
    (environment : ProgramEnvironment) (target : Workspace.ModuleId) :
    List ProgramDeclaration :=
  environment.declarationsIn target |>.filter fun declaration =>
    declaration.nameSpace == some ProgramDeclarationNamespace.type

private def targetTraits
    (environment : ProgramEnvironment) (target : Workspace.ModuleId) :
    List ProgramDeclaration :=
  environment.declarationsIn target |>.filter fun declaration =>
    declaration.nameSpace == some ProgramDeclarationNamespace.trait

private def targetValues
    (environment : ProgramEnvironment) (target : Workspace.ModuleId) :
    List ProgramDeclaration :=
  environment.declarationsIn target |>.filter fun declaration =>
    declaration.nameSpace == some ProgramDeclarationNamespace.value

private def wildcardTypes
    (environment : ProgramEnvironment) (target : Workspace.ModuleId)
    (hidden : List String) : List ProgramImportedType :=
  (targetTypes environment target).filterMap fun declaration =>
    match declaration.name with
    | some name =>
        if hidden.contains name then none
        else some { localName := name, declaration }
    | none => none

private def wildcardTraits
    (environment : ProgramEnvironment) (target : Workspace.ModuleId)
    (hidden : List String) : List ProgramImportedTrait :=
  (targetTraits environment target).filterMap fun declaration =>
    match declaration.name with
    | some name =>
        if hidden.contains name then none
        else some { localName := name, declaration }
    | none => none

private def wildcardValues
    (environment : ProgramEnvironment) (target : Workspace.ModuleId)
    (hidden : List String) : List ProgramImportedValue :=
  (targetValues environment target).filterMap fun declaration =>
    match declaration.name with
    | some name =>
        if hidden.contains name then none
        else some { localName := name, declaration }
    | none => none

private structure SelectedDeclarations where
  errors : List ProgramImportError := []
  types : List ProgramImportedType := []
  traits : List ProgramImportedTrait := []
  values : List ProgramImportedValue := []

private def selectedTrait
    (importer target : Workspace.ModuleId) (sourceName localName : String) :
    List ProgramDeclaration →
      List ProgramImportError × List ProgramImportedTrait
  | [] => ([], [])
  | [declaration] => ([], [{ localName, declaration }])
  | declarations =>
      ([.ambiguousSelectedTrait importer target sourceName
        (declarations.map (·.id))], [])

private def selectedDeclarations
    (environment : ProgramEnvironment) (importer target : Workspace.ModuleId)
    (hidden : List String) (selection : Syntax.SelectedImport) :
    SelectedDeclarations :=
  let sourceName := selectorSpelling selection.value.source
  let localName := selection.value.alias.map (·.value) |>.getD sourceName
  if isHidden hidden sourceName localName then
    {}
  else
    let typeCandidates := environment.localTypesNamed target sourceName
    let traitCandidates := environment.localTraitsNamed target sourceName
    let valueCandidates := environment.localValuesNamed target sourceName
    let typeResult : List ProgramImportError × List ProgramImportedType :=
      match typeCandidates with
      | [] => ([], [])
      | [declaration] => ([], [{ localName, declaration }])
      | declarations =>
          ([.ambiguousSelectedType importer target sourceName
            (declarations.map (·.id))], [])
    let traitResult := selectedTrait importer target sourceName localName
      traitCandidates
    let values := valueCandidates.map fun declaration =>
      { localName, declaration : ProgramImportedValue }
    let absent := typeCandidates.isEmpty && traitCandidates.isEmpty &&
      valueCandidates.isEmpty
    {
      errors :=
        (if absent then [.unknownSelectedType importer target sourceName]
          else []) ++ typeResult.1 ++ traitResult.1
      types := typeResult.2
      traits := traitResult.2
      values
    }

private def selectedDeclarationsList
    (environment : ProgramEnvironment) (importer target : Workspace.ModuleId)
    (hidden : List String) (selections : List Syntax.SelectedImport) :
    SelectedDeclarations :=
  selections.foldl (fun result selection =>
    let next := selectedDeclarations environment importer target hidden selection
    {
      errors := result.errors ++ next.errors
      types := result.types ++ next.types
      traits := result.traits ++ next.traits
      values := result.values ++ next.values
    }) {}

private def defaultNamespaceName (path : Syntax.ModulePath) : String :=
  (programImportModuleComponents path).getLast!

private def addNamespace
    (visibility : ProgramImports) (localName : String)
    (target : Workspace.ModuleId) : ProgramImports := {
  visibility with
  namespaces := visibility.namespaces ++ [{ localName, target }]
}

private def addWildcardDeclarations
    (visibility : ProgramImports)
    (types : List ProgramImportedType)
    (traits : List ProgramImportedTrait)
    (values : List ProgramImportedValue) : ProgramImports := {
  visibility with
  types := visibility.types ++ types
  traits := visibility.traits ++ traits
  values := visibility.values ++ values
}

private def addSelectedDeclarations
    (visibility : ProgramImports) (selected : SelectedDeclarations) :
    ProgramImports :=
  addWildcardDeclarations visibility selected.types selected.traits
    selected.values

private def processImport
    (environment : ProgramEnvironment) (importer : Workspace.ModuleId)
    (visibility : ProgramImports) (declaration : Syntax.ImportDecl) :
    List ProgramImportError × ProgramImports :=
  match declaration.value with
  | .plain path =>
      match resolveProgramImportModule environment importer path with
      | .error error => ([error], visibility)
      | .ok target =>
          ([], addNamespace visibility (defaultNamespaceName path) target)
  | .namespace path alias =>
      match resolveProgramImportModule environment importer path with
      | .error error => ([error], visibility)
      | .ok target => ([], addNamespace visibility alias.value target)
  | .wildcard path hidingClause =>
      match resolveProgramImportModule environment importer path with
      | .error error => ([error], visibility)
      | .ok target =>
          let hidden := hiddenSelectorNames hidingClause
          ([], addWildcardDeclarations visibility
            (wildcardTypes environment target hidden)
            (wildcardTraits environment target hidden)
            (wildcardValues environment target hidden))
  | .selected selection path hidingClause =>
      match resolveProgramImportModule environment importer path with
      | .error error => ([error], visibility)
      | .ok target =>
          let selected := selectedDeclarationsList environment importer target
            (hiddenSelectorNames hidingClause) selection.elements.toList
          (selected.errors, addSelectedDeclarations visibility selected)

private def importsInModule (module : ProgramModule) : List Syntax.ImportDecl :=
  module.source.items.filterMap fun item =>
    match item.value with
    | .importDecl declaration => some declaration
    | _ => none

private def buildProgramImportsFrom
    (environment : ProgramEnvironment) (importer : Workspace.ModuleId)
    (declarations : List Syntax.ImportDecl) :
    List ProgramImportError × ProgramImports :=
  declarations.foldl (fun result declaration =>
    let next := processImport environment importer result.2 declaration
    (result.1 ++ next.1, next.2))
    ([], { hasImports := !declarations.isEmpty })

/-- Build direct type and namespace visibility for one program module.
Scopes not owned by the environment retain the old empty-import behavior. -/
def buildProgramImports
    (environment : ProgramEnvironment) (importer : Workspace.ModuleId) :
    Except (List ProgramImportError) ProgramImports :=
  match environment.modules.find? fun module => decide (module.id = importer) with
  | none => .ok {}
  | some module =>
      let result := buildProgramImportsFrom environment importer
        (importsInModule module)
      if result.1.isEmpty then .ok result.2 else .error result.1

namespace ProgramImports

private def deduplicateDeclarationsAux
    (seen : List Resolved.DeclarationId) :
    List ProgramDeclaration → List ProgramDeclaration
  | [] => []
  | declaration :: rest =>
      if seen.any fun id => decide (id = declaration.id) then
        deduplicateDeclarationsAux seen rest
      else
        declaration :: deduplicateDeclarationsAux (declaration.id :: seen) rest

/-- Unqualified imported type candidates in declaration/import order. -/
def typesNamed (visibility : ProgramImports) (name : String) :
    List ProgramDeclaration :=
  deduplicateDeclarationsAux [] <|
    visibility.types.filterMap fun imported =>
      if imported.localName == name then some imported.declaration else none

/-- Unqualified imported trait candidates in declaration/import order. -/
def traitsNamed (visibility : ProgramImports) (name : String) :
    List ProgramDeclaration :=
  deduplicateDeclarationsAux [] <|
    visibility.traits.filterMap fun imported =>
      if imported.localName == name then some imported.declaration else none

/-- Unqualified imported value candidates in declaration/import order.
All distinct declarations in an imported overload set are retained. -/
def valuesNamed (visibility : ProgramImports) (name : String) :
    List ProgramDeclaration :=
  deduplicateDeclarationsAux [] <|
    visibility.values.filterMap fun imported =>
      if imported.localName == name then some imported.declaration else none

/-- Modules denoted by an imported namespace spelling. -/
def modulesNamed (visibility : ProgramImports) (name : String) :
    List Workspace.ModuleId :=
  (visibility.namespaces.filterMap fun imported =>
    if imported.localName == name then some imported.target else none).eraseDups

end ProgramImports

end Solcore.Frontend
