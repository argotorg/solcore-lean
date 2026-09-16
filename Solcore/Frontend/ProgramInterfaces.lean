import Solcore.Frontend.ProgramEnvironment

/-!
Executable public module interfaces for the initial whole-program profile.

Interfaces are explicit: a module without an `export` declaration publishes
nothing.  Imports and re-exports are interpreted over a finite monotone
least-fixed-point computation, so positive export cycles are supported without
choosing a source-order winner.  Constructor and operator export selectors are
kept as explicit errors until those entity forms enter the program catalog.
-/

set_option autoImplicit false

namespace Solcore.Frontend

/-- One public entity name and the top-level declaration it denotes. -/
structure ProgramPublicEntity where
  publicName : String
  declaration : ProgramDeclaration
  deriving Repr

/-- One public module namespace binding. -/
structure ProgramPublicModule where
  publicName : String
  target : Workspace.ModuleId
  deriving Repr, DecidableEq

/-- The public surface of one program module. -/
structure ProgramInterface where
  entities : List ProgramPublicEntity := []
  modules : List ProgramPublicModule := []
  deriving Repr

/-- Public interfaces indexed by canonical module identity in program order. -/
structure ProgramInterfaces where
  entries : List (Workspace.ModuleId × ProgramInterface)
  deriving Repr

/-- Failures which remain after public-interface closure has converged. -/
inductive ProgramInterfaceError where
  | unknownModule
      (owner : Workspace.ModuleId)
      (components : List String)
  | unknownImportName
      (owner target : Workspace.ModuleId)
      (name : String)
  | unknownExportName
      (owner : Workspace.ModuleId)
      (name : String)
  | unsupportedConstructorExport
      (owner : Workspace.ModuleId)
      (name : String)
  | unsupportedOperatorExport
      (owner : Workspace.ModuleId)
      (spelling : String)
  | fixedPointExhausted
  deriving Repr, DecidableEq

namespace ProgramInterfaces

/-- Look up the complete public interface of one module. -/
def interface? (interfaces : ProgramInterfaces)
    (moduleId : Workspace.ModuleId) : Option ProgramInterface :=
  (interfaces.entries.find? fun entry => decide (entry.1 = moduleId)).map (·.2)

/-- Public entities in one namespace under an exact public spelling. -/
def entitiesNamed (interfaces : ProgramInterfaces)
    (moduleId : Workspace.ModuleId)
    (nameSpace : ProgramDeclarationNamespace) (name : String) :
    List ProgramDeclaration :=
  match interfaces.interface? moduleId with
  | none => []
  | some interface =>
      interface.entities.filterMap fun entity =>
        if entity.publicName == name &&
            entity.declaration.nameSpace == some nameSpace then
          some entity.declaration
        else
          none

/-- All public entity candidates under a spelling, across entity namespaces. -/
def declarationsNamed (interfaces : ProgramInterfaces)
    (moduleId : Workspace.ModuleId) (name : String) :
    List ProgramDeclaration :=
  match interfaces.interface? moduleId with
  | none => []
  | some interface =>
      interface.entities.filterMap fun entity =>
        if entity.publicName == name then some entity.declaration else none

/-- Public module targets installed under an exact namespace spelling. -/
def modulesNamed (interfaces : ProgramInterfaces)
    (moduleId : Workspace.ModuleId) (name : String) :
    List Workspace.ModuleId :=
  match interfaces.interface? moduleId with
  | none => []
  | some interface =>
      (interface.modules.filterMap fun binding =>
        if binding.publicName == name then some binding.target else none).eraseDups

end ProgramInterfaces

private def qualifiedComponents (path : Syntax.QualifiedName) : List String :=
  path.value.components.toList.map (·.value)

private def importComponents (path : Syntax.ModulePath) : List String :=
  path.value.components.toList.map (·.value)

private def moduleComponents (moduleId : Workspace.ModuleId) : List String :=
  moduleId.path.segments.map (·.text)

private def sameLibraryTarget?
    (environment : ProgramEnvironment) (owner : Workspace.ModuleId)
    (components : List String) : Option Workspace.ModuleId :=
  (environment.modules.find? fun module =>
    decide (module.id.library = owner.library) &&
      moduleComponents module.id == components).map (·.id)

private def importTarget?
    (environment : ProgramEnvironment) (owner : Workspace.ModuleId)
    (path : Syntax.ModulePath) : Option Workspace.ModuleId :=
  let components := importComponents path
  if path.value.externalMarker.isSome then
    match components with
    | library :: rest =>
        (environment.modules.find? fun module =>
          match module.id.library with
          | .external name =>
              name.render == library && moduleComponents module.id == rest
          | _ => false).map (·.id)
    | [] => none
  else
    sameLibraryTarget? environment owner components

private def exportTarget?
    (environment : ProgramEnvironment) (owner : Workspace.ModuleId)
    (path : Syntax.QualifiedName) : Option Workspace.ModuleId :=
  sameLibraryTarget? environment owner (qualifiedComponents path)

private def entityKeyEq
    (left right : ProgramPublicEntity) : Bool :=
  left.publicName == right.publicName &&
    decide (left.declaration.id = right.declaration.id)

private def moduleKeyEq
    (left right : ProgramPublicModule) : Bool :=
  left.publicName == right.publicName && decide (left.target = right.target)

private def appendEntity
    (entities : List ProgramPublicEntity) (entity : ProgramPublicEntity) :
    List ProgramPublicEntity :=
  if entities.any fun previous => entityKeyEq previous entity then entities
  else entities ++ [entity]

private def appendModule
    (modules : List ProgramPublicModule) (binding : ProgramPublicModule) :
    List ProgramPublicModule :=
  if modules.any fun previous => moduleKeyEq previous binding then modules
  else modules ++ [binding]

private def mergeEntities
    (left right : List ProgramPublicEntity) : List ProgramPublicEntity :=
  right.foldl appendEntity left

private def mergeModules
    (left right : List ProgramPublicModule) : List ProgramPublicModule :=
  right.foldl appendModule left

private def mergeInterface
    (left right : ProgramInterface) : ProgramInterface := {
  entities := mergeEntities left.entities right.entities
  modules := mergeModules left.modules right.modules
}

private def interfaceEq (left right : ProgramInterface) : Bool :=
  left.entities.length == right.entities.length &&
    left.modules.length == right.modules.length &&
    (left.entities.zip right.entities |>.all fun pair =>
      entityKeyEq pair.1 pair.2) &&
    (left.modules.zip right.modules |>.all fun pair =>
      moduleKeyEq pair.1 pair.2)

private def interfacesEq
    (left right : ProgramInterfaces) : Bool :=
  left.entries.length == right.entries.length &&
    (left.entries.zip right.entries |>.all fun pair =>
      decide (pair.1.1 = pair.2.1) && interfaceEq pair.1.2 pair.2.2)

private def emptyInterfaces (environment : ProgramEnvironment) : ProgramInterfaces := {
  entries := environment.modules.map fun module => (module.id, {})
}

private def interfaceOf
    (interfaces : ProgramInterfaces) (target : Workspace.ModuleId) :
    ProgramInterface :=
  (interfaces.interface? target).getD {}

private structure VisibleEntity where
  localName : String
  declaration : ProgramDeclaration
  deriving Repr

private def visibleKeyEq (left right : VisibleEntity) : Bool :=
  left.localName == right.localName &&
    decide (left.declaration.id = right.declaration.id)

private def appendVisible
    (entities : List VisibleEntity) (entity : VisibleEntity) :
    List VisibleEntity :=
  if entities.any fun previous => visibleKeyEq previous entity then entities
  else entities ++ [entity]

private def mergeVisible
    (left right : List VisibleEntity) : List VisibleEntity :=
  right.foldl appendVisible left

private def selectorSpelling (selector : Syntax.SelectorName) : String :=
  match selector.value with
  | .identifier name => name.value
  | .operator spelling => spelling

private def hiddenNames (clause : Option Syntax.HidingClause) : List String :=
  match clause with
  | none => []
  | some clause => clause.value.names.toList.map selectorSpelling

private def publicAsVisible
    (interface : ProgramInterface) (hidden : List String) :
    List VisibleEntity :=
  interface.entities.filterMap fun entity =>
    if hidden.contains entity.publicName then none
    else some { localName := entity.publicName, declaration := entity.declaration }

private structure VisibilityResult where
  entities : List VisibleEntity := []
  errors : List ProgramInterfaceError := []

private def selectImported
    (owner target : Workspace.ModuleId) (interface : ProgramInterface)
    (hidden : List String) (selection : Syntax.SelectedImport) :
    VisibilityResult :=
  let sourceName := selectorSpelling selection.value.source
  let localName := selection.value.alias.map (·.value) |>.getD sourceName
  let candidates := interface.entities.filter fun entity =>
    entity.publicName == sourceName
  let isHidden := hidden.contains sourceName || hidden.contains localName
  if candidates.isEmpty then
    { errors := [.unknownImportName owner target sourceName] }
  else if isHidden then
    {}
  else
    { entities := candidates.map fun entity =>
        { localName, declaration := entity.declaration } }

private def validateHidden
    (owner target : Workspace.ModuleId) (interface : ProgramInterface)
    (hidden : List String) : List ProgramInterfaceError :=
  hidden.filterMap fun name =>
    if interface.entities.any fun entity => entity.publicName == name then none
    else some (.unknownImportName owner target name)

private def processImport
    (environment : ProgramEnvironment) (interfaces : ProgramInterfaces)
    (owner : Workspace.ModuleId) (declaration : Syntax.ImportDecl) :
    VisibilityResult :=
  let path := match declaration.value with
    | .plain path | .namespace path _ | .wildcard path _ | .selected _ path _ => path
  match importTarget? environment owner path with
  | none => { errors := [.unknownModule owner (importComponents path)] }
  | some target =>
      let interface := interfaceOf interfaces target
      match declaration.value with
      | .plain _ | .namespace _ _ => {}
      | .wildcard _ hidingClause =>
          let hidden := hiddenNames hidingClause
          {
            entities := publicAsVisible interface hidden
            errors := validateHidden owner target interface hidden
          }
      | .selected selection _ hidingClause =>
          let hidden := hiddenNames hidingClause
          let selected := selection.elements.toList.foldl
              (fun (result : VisibilityResult) item =>
            let next := selectImported owner target interface hidden item
            {
              entities := mergeVisible result.entities next.entities
              errors := result.errors ++ next.errors
            }) ({} : VisibilityResult)
          { selected with
            errors := selected.errors ++ validateHidden owner target interface hidden }

private def importsIn (module : ProgramModule) : List Syntax.ImportDecl :=
  module.source.items.filterMap fun item =>
    match item.value with
    | .importDecl declaration => some declaration
    | _ => none

private def importedVisibility
    (environment : ProgramEnvironment) (interfaces : ProgramInterfaces)
    (module : ProgramModule) : VisibilityResult :=
  (importsIn module).foldl (fun result declaration =>
    let next := processImport environment interfaces module.id declaration
    {
      entities := mergeVisible result.entities next.entities
      errors := result.errors ++ next.errors
    }) {}

private def localEntities
    (environment : ProgramEnvironment) (moduleId : Workspace.ModuleId) :
    List VisibleEntity :=
  (environment.declarationsIn moduleId).filterMap fun declaration =>
    match declaration.nameSpace, declaration.name with
    | some _, some name => some { localName := name, declaration }
    | _, _ => none

private def visibleNamed
    (locals imported : List VisibleEntity) (name : String) : List VisibleEntity :=
  [.type, .trait, .value].flatMap fun nameSpace =>
    let localCandidates := locals.filter fun entity =>
      entity.localName == name && entity.declaration.nameSpace == some nameSpace
    if localCandidates.isEmpty then
      imported.filter fun entity =>
        entity.localName == name && entity.declaration.nameSpace == some nameSpace
    else
      localCandidates

private structure Contribution where
  interface : ProgramInterface := {}
  errors : List ProgramInterfaceError := []

private def addVisibleWithName
    (contribution : Contribution) (publicName : String)
    (entities : List VisibleEntity) : Contribution :=
  { contribution with
    interface := { contribution.interface with
      entities := mergeEntities contribution.interface.entities <|
        entities.map fun entity => { publicName, declaration := entity.declaration } } }

private def addPublicEntities
    (contribution : Contribution) (entities : List ProgramPublicEntity) :
    Contribution :=
  { contribution with
    interface := { contribution.interface with
      entities := mergeEntities contribution.interface.entities entities } }

private def addPublicModule
    (contribution : Contribution) (name : String)
    (target : Workspace.ModuleId) : Contribution :=
  { contribution with
    interface := { contribution.interface with
      modules := appendModule contribution.interface.modules
        { publicName := name, target } } }

private def addError
    (contribution : Contribution) (error : ProgramInterfaceError) : Contribution :=
  { contribution with errors := contribution.errors ++ [error] }

private def processExportName
    (owner : Workspace.ModuleId) (locals imported : List VisibleEntity)
    (contribution : Contribution) (name : Syntax.ExportName) : Contribution :=
  match name.value with
  | .wildcard _ =>
      locals.foldl (fun result entity =>
        addVisibleWithName result entity.localName [entity]) contribution
  | .identifier identifier none =>
      let spelling := identifier.value
      let candidates := visibleNamed locals imported spelling
      if candidates.isEmpty then
        addError contribution (.unknownExportName owner spelling)
      else
        addVisibleWithName contribution spelling candidates
  | .identifier identifier (some _) =>
      addError contribution
        (.unsupportedConstructorExport owner identifier.value)
  | .operator spelling =>
      addError contribution (.unsupportedOperatorExport owner spelling.value)

private def processRemoteName
    (owner : Workspace.ModuleId) (targetInterface : ProgramInterface)
    (contribution : Contribution) (name : Syntax.ExportName) : Contribution :=
  match name.value with
  | .wildcard _ => addPublicEntities contribution targetInterface.entities
  | .identifier identifier none =>
      let spelling := identifier.value
      let candidates := targetInterface.entities.filter fun entity =>
        entity.publicName == spelling
      if candidates.isEmpty then
        addError contribution (.unknownExportName owner spelling)
      else
        addPublicEntities contribution candidates
  | .identifier identifier (some _) =>
      addError contribution
        (.unsupportedConstructorExport owner identifier.value)
  | .operator spelling =>
      addError contribution (.unsupportedOperatorExport owner spelling.value)

private def processLocalExportItem
    (environment : ProgramEnvironment) (interfaces : ProgramInterfaces)
    (owner : Workspace.ModuleId) (locals imported : List VisibleEntity)
    (contribution : Contribution) (item : Syntax.LocalExportItem) : Contribution :=
  match item.value with
  | .name name => processExportName owner locals imported contribution name
  | .moduleWildcard path _ =>
      match exportTarget? environment owner path with
      | none => addError contribution
          (.unknownModule owner (qualifiedComponents path))
      | some target =>
          addPublicEntities contribution (interfaceOf interfaces target).entities

private def processExport
    (environment : ProgramEnvironment) (interfaces : ProgramInterfaces)
    (module : ProgramModule) (locals imported : List VisibleEntity)
    (contribution : Contribution) (declaration : Syntax.ExportDecl) : Contribution :=
  match declaration.value with
  | .local items =>
      items.elements.foldl
        (processLocalExportItem environment interfaces module.id locals imported)
        contribution
  | .module path =>
      match exportTarget? environment module.id path with
      | none => addError contribution
          (.unknownModule module.id (qualifiedComponents path))
      | some target =>
          addPublicModule contribution (qualifiedComponents path).getLast! target
  | .moduleAs path alias =>
      match exportTarget? environment module.id path with
      | none => addError contribution
          (.unknownModule module.id (qualifiedComponents path))
      | some target => addPublicModule contribution alias.value target
  | .itemsFrom path selection =>
      match exportTarget? environment module.id path with
      | none => addError contribution
          (.unknownModule module.id (qualifiedComponents path))
      | some target =>
          let targetInterface := interfaceOf interfaces target
          match selection.value with
          | .wildcard _ => addPublicEntities contribution targetInterface.entities
          | .selected items =>
              items.elements.foldl
                (processRemoteName module.id targetInterface) contribution

private def exportsIn (module : ProgramModule) : List Syntax.ExportDecl :=
  module.source.items.filterMap fun item =>
    match item.value with
    | .exportDecl declaration => some declaration
    | _ => none

private def moduleContribution
    (environment : ProgramEnvironment) (interfaces : ProgramInterfaces)
    (module : ProgramModule) : Contribution :=
  let locals := localEntities environment module.id
  let imported := importedVisibility environment interfaces module
  let exported := (exportsIn module).foldl
      (fun (contribution : Contribution) declaration =>
    processExport environment interfaces module locals imported.entities
      contribution declaration) ({} : Contribution)
  { exported with errors := imported.errors ++ exported.errors }

private def closureRound
    (environment : ProgramEnvironment) (interfaces : ProgramInterfaces) :
    ProgramInterfaces := {
  entries := environment.modules.map fun module =>
    let previous := interfaceOf interfaces module.id
    let next := (moduleContribution environment interfaces module).interface
    (module.id, mergeInterface previous next)
}

private def syntaxBudget (environment : ProgramEnvironment) : Nat :=
  environment.modules.foldl (fun total module =>
    total + module.source.items.foldl (fun itemTotal item =>
      itemTotal + match item.value with
        | .importDecl declaration =>
            match declaration.value with
            | .selected selection _ _ => selection.elements.toList.length + 1
            | _ => 1
        | .exportDecl declaration =>
            match declaration.value with
            | .local items => items.elements.length + 1
            | .itemsFrom _ selection =>
                match selection.value with
                | .selected items => items.elements.length + 1
                | _ => 1
            | _ => 1
        | _ => 1) 0) 1

private def closureFuel (environment : ProgramEnvironment) : Nat :=
  let modules := environment.modules.length + 1
  let declarations := environment.declarations.length + 1
  modules * modules * declarations * (syntaxBudget environment + 1) + 1

private def closeInterfaces
    (environment : ProgramEnvironment) :
    Nat → ProgramInterfaces → Except ProgramInterfaceError ProgramInterfaces
  | 0, _ => .error .fixedPointExhausted
  | fuel + 1, current =>
      let next := closureRound environment current
      if interfacesEq current next then .ok next
      else closeInterfaces environment fuel next

private def finalErrors
    (environment : ProgramEnvironment) (interfaces : ProgramInterfaces) :
    List ProgramInterfaceError :=
  environment.modules.flatMap fun module =>
    (moduleContribution environment interfaces module).errors

/-- Compute explicit public interfaces by finite monotone least fixed point. -/
def buildProgramInterfaces (environment : ProgramEnvironment) :
    Except (List ProgramInterfaceError) ProgramInterfaces :=
  match closeInterfaces environment (closureFuel environment)
      (emptyInterfaces environment) with
  | .error error => .error [error]
  | .ok interfaces =>
      let errors := finalErrors environment interfaces
      if errors.isEmpty then .ok interfaces else .error errors

end Solcore.Frontend
