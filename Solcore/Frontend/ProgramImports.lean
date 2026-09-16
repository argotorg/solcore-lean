import Solcore.Frontend.ProgramInterfaces

/-!
Import visibility over explicit whole-program public interfaces.

The target module is resolved canonically, while item imports read only its
fixed-point public interface.  Value imports preserve overload sets; operator
selectors use their spelling as a value-namespace name.
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
  publicInterfaces : ProgramInterfaces := { entries := [] }
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
  | publicInterface (errors : List ProgramInterfaceError)
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

private def targetEntities
    (interfaces : ProgramInterfaces) (target : Workspace.ModuleId)
    (nameSpace : ProgramDeclarationNamespace) : List ProgramPublicEntity :=
  match interfaces.interface? target with
  | none => []
  | some interface => interface.entities.filter fun entity =>
      entity.declaration.nameSpace == some nameSpace

private def wildcardTypes
    (interfaces : ProgramInterfaces) (target : Workspace.ModuleId)
    (hidden : List String) : List ProgramImportedType :=
  (targetEntities interfaces target .type).filterMap fun entity =>
    if hidden.contains entity.publicName then none
    else some {
      localName := entity.publicName
      declaration := entity.declaration
    }

private def wildcardTraits
    (interfaces : ProgramInterfaces) (target : Workspace.ModuleId)
    (hidden : List String) : List ProgramImportedTrait :=
  (targetEntities interfaces target .trait).filterMap fun entity =>
    if hidden.contains entity.publicName then none
    else some {
      localName := entity.publicName
      declaration := entity.declaration
    }

private def wildcardValues
    (interfaces : ProgramInterfaces) (target : Workspace.ModuleId)
    (hidden : List String) : List ProgramImportedValue :=
  (targetEntities interfaces target .value).filterMap fun entity =>
    if hidden.contains entity.publicName then none
    else some {
      localName := entity.publicName
      declaration := entity.declaration
    }

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
    (interfaces : ProgramInterfaces) (importer target : Workspace.ModuleId)
    (hidden : List String) (selection : Syntax.SelectedImport) :
    SelectedDeclarations :=
  let sourceName := selectorSpelling selection.value.source
  let localName := selection.value.alias.map (·.value) |>.getD sourceName
  if isHidden hidden sourceName localName then
    {}
  else
    let typeCandidates := interfaces.entitiesNamed target .type sourceName
    let traitCandidates := interfaces.entitiesNamed target .trait sourceName
    let valueCandidates := interfaces.entitiesNamed target .value sourceName
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
    (interfaces : ProgramInterfaces) (importer target : Workspace.ModuleId)
    (hidden : List String) (selections : List Syntax.SelectedImport) :
    SelectedDeclarations :=
  selections.foldl (fun result selection =>
    let next := selectedDeclarations interfaces importer target hidden selection
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
    (environment : ProgramEnvironment) (interfaces : ProgramInterfaces)
    (importer : Workspace.ModuleId)
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
            (wildcardTypes interfaces target hidden)
            (wildcardTraits interfaces target hidden)
            (wildcardValues interfaces target hidden))
  | .selected selection path hidingClause =>
      match resolveProgramImportModule environment importer path with
      | .error error => ([error], visibility)
      | .ok target =>
          let selected := selectedDeclarationsList interfaces importer target
            (hiddenSelectorNames hidingClause) selection.elements.toList
          (selected.errors, addSelectedDeclarations visibility selected)

private def importsInModule (module : ProgramModule) : List Syntax.ImportDecl :=
  module.source.items.filterMap fun item =>
    match item.value with
    | .importDecl declaration => some declaration
    | _ => none

private def buildProgramImportsFrom
    (environment : ProgramEnvironment) (interfaces : ProgramInterfaces)
    (importer : Workspace.ModuleId)
    (declarations : List Syntax.ImportDecl) :
    List ProgramImportError × ProgramImports :=
  declarations.foldl (fun result declaration =>
    let next := processImport environment interfaces importer result.2 declaration
    (result.1 ++ next.1, next.2))
    ([], {
      hasImports := !declarations.isEmpty
      publicInterfaces := interfaces
    })

/-- Build public-interface-backed visibility for one program module.
Scopes not owned by the environment retain the old empty-import behavior. -/
def buildProgramImports
    (environment : ProgramEnvironment) (importer : Workspace.ModuleId) :
    Except (List ProgramImportError) ProgramImports :=
  match environment.modules.find? fun module => decide (module.id = importer) with
  | none => .ok {}
  | some module =>
      match buildProgramInterfaces environment with
      | .error errors => .error [.publicInterface errors]
      | .ok interfaces =>
          let result := buildProgramImportsFrom environment interfaces importer
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

/-- Whether the first component denotes an imported module namespace. -/
def hasNamespaceRoot (visibility : ProgramImports) : List String → Bool
  | [] => false
  | root :: _ => !(visibility.modulesNamed root).isEmpty

/-- Follow an imported namespace and then any public module re-export bindings. -/
def namespacePathTargets (visibility : ProgramImports) :
    List String → List Workspace.ModuleId
  | [] => []
  | root :: rest =>
      rest.foldl (fun targets component =>
        (targets.flatMap fun target =>
          visibility.publicInterfaces.modulesNamed target component).eraseDups)
        (visibility.modulesNamed root)

/-- Public declarations reached through an imported/re-exported module path. -/
def declarationsInNamespacePathNamed
    (visibility : ProgramImports) (path : List String)
    (nameSpace : ProgramDeclarationNamespace) (name : String) :
    List ProgramDeclaration :=
  deduplicateDeclarationsAux [] <|
    (visibility.namespacePathTargets path).flatMap fun target =>
      visibility.publicInterfaces.entitiesNamed target nameSpace name

/-- Public types reached through an imported/re-exported module path. -/
def typesInNamespacePathNamed (visibility : ProgramImports)
    (path : List String) (name : String) : List ProgramDeclaration :=
  visibility.declarationsInNamespacePathNamed path .type name

/-- Public traits reached through an imported/re-exported module path. -/
def traitsInNamespacePathNamed (visibility : ProgramImports)
    (path : List String) (name : String) : List ProgramDeclaration :=
  visibility.declarationsInNamespacePathNamed path .trait name

/-- Public values reached through an imported/re-exported module path. -/
def valuesInNamespacePathNamed (visibility : ProgramImports)
    (path : List String) (name : String) : List ProgramDeclaration :=
  visibility.declarationsInNamespacePathNamed path .value name

end ProgramImports

end Solcore.Frontend
