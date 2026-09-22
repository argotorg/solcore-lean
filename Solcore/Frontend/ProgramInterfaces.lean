import Solcore.Frontend.ProgramModuleResolution

/-!
Executable public module interfaces for the initial whole-program profile.

Interfaces are explicit: a module without an `export` declaration publishes
nothing.  Imports and re-exports are interpreted over a finite monotone
least-fixed-point computation, so positive export cycles are supported without
choosing a source-order winner.  Data declarations separately record whether
their constructors are opaque or which constructor spellings are public.
-/

set_option autoImplicit false

namespace Solcore.Frontend

/-- Constructor access carried by a public or imported type binding. -/
inductive ProgramConstructorVisibility where
  | notData
  | opaqueData
  | visible (names : List String)
  deriving Repr, BEq, DecidableEq

namespace ProgramConstructorVisibility

/-- Normalize the empty visible set to opaque data, matching the upstream
nonempty-set invariant. -/
def ofVisible : List String → ProgramConstructorVisibility
  | [] => .opaqueData
  | names => .visible names

end ProgramConstructorVisibility

/-- One public entity name and the top-level declaration it denotes. -/
structure ProgramPublicEntity where
  publicName : String
  declaration : ProgramDeclaration
  constructors : ProgramConstructorVisibility := .notData
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
  | unknownExportConstructor
      (owner : Workspace.ModuleId)
      (typeName constructorName : String)
  | fixedPointExhausted
  deriving Repr, DecidableEq

namespace ProgramDeclaration

/-- Constructor spellings of a catalogued enum, in declaration order. -/
def constructorNames (declaration : ProgramDeclaration) : List String :=
  match declaration.source.value with
  | .enum source => source.value.constructors.map (·.value.name.value)
  | _ => []

/-- Full local constructor access for a catalogued declaration. -/
def localConstructorVisibility
    (declaration : ProgramDeclaration) : ProgramConstructorVisibility :=
  match declaration.kind with
  | .enum => .ofVisible declaration.constructorNames
  | _ => .notData

end ProgramDeclaration

namespace ProgramConstructorVisibility

/-- Whether the binding denotes a data declaration, even if it is opaque. -/
def isData : ProgramConstructorVisibility → Bool
  | .notData => false
  | .opaqueData | .visible _ => true

/-- Whether one constructor spelling is exposed by the binding. -/
def contains : ProgramConstructorVisibility → String → Bool
  | .visible names, name => names.contains name
  | _, _ => false

/-- Remove constructor access while retaining the fact that this is data. -/
def strip : ProgramConstructorVisibility → ProgramConstructorVisibility
  | .notData => .notData
  | .opaqueData | .visible _ => .opaqueData

/-- Monotone deterministic union for duplicate bindings of one declaration. -/
def merge (declaration : ProgramDeclaration) :
    ProgramConstructorVisibility → ProgramConstructorVisibility →
      ProgramConstructorVisibility
  | .notData, .notData => .notData
  | .opaqueData, .opaqueData => .opaqueData
  | .opaqueData, .visible names | .visible names, .opaqueData => .ofVisible names
  | .visible left, .visible right =>
      .ofVisible <| declaration.constructorNames.filter fun name =>
        left.contains name || right.contains name
  | .notData, _ | _, .notData => .notData

end ProgramConstructorVisibility

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

private def entityKeyEq
    (left right : ProgramPublicEntity) : Bool :=
  left.publicName == right.publicName &&
    decide (left.declaration.id = right.declaration.id)

private def entityEq
    (left right : ProgramPublicEntity) : Bool :=
  entityKeyEq left right && left.constructors == right.constructors

private def moduleKeyEq
    (left right : ProgramPublicModule) : Bool :=
  left.publicName == right.publicName && decide (left.target = right.target)

private def appendEntity :
    List ProgramPublicEntity → ProgramPublicEntity → List ProgramPublicEntity
  | [], entity => [entity]
  | previous :: rest, entity =>
      if entityKeyEq previous entity then
        { previous with
          constructors := previous.constructors.merge previous.declaration
            entity.constructors } :: rest
      else
        previous :: appendEntity rest entity

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
      entityEq pair.1 pair.2) &&
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
  constructors : ProgramConstructorVisibility := .notData
  deriving Repr

private def visibleKeyEq (left right : VisibleEntity) : Bool :=
  left.localName == right.localName &&
    decide (left.declaration.id = right.declaration.id)

private def appendVisible :
    List VisibleEntity → VisibleEntity → List VisibleEntity
  | [], entity => [entity]
  | previous :: rest, entity =>
      if visibleKeyEq previous entity then
        { previous with
          constructors := previous.constructors.merge previous.declaration
            entity.constructors } :: rest
      else
        previous :: appendVisible rest entity

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
    else some {
      localName := entity.publicName
      declaration := entity.declaration
      constructors := entity.constructors
    }

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
        {
          localName
          declaration := entity.declaration
          constructors := entity.constructors
        } }

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
  match resolveProgramModulePath? environment owner path with
  | none => { errors := [.unknownModule owner (programModulePathComponents path)] }
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
    | some _, some name => some {
        localName := name
        declaration
        constructors := declaration.localConstructorVisibility
      }
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
        entities.map fun entity => {
          publicName
          declaration := entity.declaration
          constructors := entity.constructors
        } } }

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

private def stripVisibleConstructors (entity : VisibleEntity) : VisibleEntity :=
  { entity with constructors := entity.constructors.strip }

private def stripPublicConstructors
    (entity : ProgramPublicEntity) : ProgramPublicEntity :=
  { entity with constructors := entity.constructors.strip }

private structure SelectedVisibleEntity where
  entity : VisibleEntity
  errors : List ProgramInterfaceError := []

private def selectVisibleConstructors
    (owner : Workspace.ModuleId) (typeName : String)
    (selection : Syntax.ConstructorSelection) (entity : VisibleEntity) :
    Option SelectedVisibleEntity :=
  if !entity.constructors.isData then
    none
  else
    let available := match entity.constructors with
      | .visible names => names
      | .notData | .opaqueData => []
    let requested : List String := match selection.value with
      | .all _ => available
      | .named constructors =>
          (constructors.toList.map fun (constructor : Syntax.Identifier) =>
            constructor.value).eraseDups
    let selected := available.filter requested.contains
    let missing := match selection.value with
      | .all _ => []
      | .named _ => requested.filter fun name => !available.contains name
    some {
      entity := { entity with constructors := .ofVisible selected }
      errors := missing.map fun constructorName =>
        .unknownExportConstructor owner typeName constructorName
    }

private def addSelectedConstructors
    (owner : Workspace.ModuleId) (typeName publicName : String)
    (selection : Syntax.ConstructorSelection) (candidates : List VisibleEntity)
    (contribution : Contribution) : Contribution :=
  let selected := candidates.filterMap fun entity =>
    selectVisibleConstructors owner typeName selection entity
  if selected.isEmpty then
    addError contribution (.unknownExportName owner typeName)
  else
    selected.foldl (fun result item =>
      let result := addVisibleWithName result publicName [item.entity]
      item.errors.foldl addError result) contribution

private def visibleOfPublic (entity : ProgramPublicEntity) : VisibleEntity := {
  localName := entity.publicName
  declaration := entity.declaration
  constructors := entity.constructors
}

private def processExportName
    (owner : Workspace.ModuleId) (locals imported : List VisibleEntity)
    (contribution : Contribution) (name : Syntax.ExportName) : Contribution :=
  match name.value with
  | .wildcard _ =>
      locals.foldl (fun result entity =>
        addVisibleWithName result entity.localName
          [stripVisibleConstructors entity]) contribution
  | .identifier identifier none =>
      let spelling := identifier.value
      let candidates := visibleNamed locals imported spelling
      if candidates.isEmpty then
        addError contribution (.unknownExportName owner spelling)
      else
        addVisibleWithName contribution spelling
          (candidates.map stripVisibleConstructors)
  | .identifier identifier (some selection) =>
      let spelling := identifier.value
      addSelectedConstructors owner spelling spelling selection
        (visibleNamed locals imported spelling) contribution
  | .operator spelling =>
      let candidates := visibleNamed locals imported spelling.value
      if candidates.isEmpty then
        addError contribution (.unknownExportName owner spelling.value)
      else
        addVisibleWithName contribution spelling.value
          (candidates.map stripVisibleConstructors)

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
        addPublicEntities contribution (candidates.map stripPublicConstructors)
  | .identifier identifier (some selection) =>
      let spelling := identifier.value
      let candidates := targetInterface.entities.filterMap fun entity =>
        if entity.publicName == spelling then some (visibleOfPublic entity)
        else none
      addSelectedConstructors owner spelling spelling selection candidates
        contribution
  | .operator spelling =>
      let candidates := targetInterface.entities.filter fun entity =>
        entity.publicName == spelling.value
      if candidates.isEmpty then
        addError contribution (.unknownExportName owner spelling.value)
      else
        addPublicEntities contribution (candidates.map stripPublicConstructors)

private def processLocalExportItem
    (environment : ProgramEnvironment) (interfaces : ProgramInterfaces)
    (owner : Workspace.ModuleId) (locals imported : List VisibleEntity)
    (contribution : Contribution) (item : Syntax.LocalExportItem) : Contribution :=
  match item.value with
  | .name name => processExportName owner locals imported contribution name
  | .moduleWildcard path _ =>
      match resolveProgramExportPath? environment owner path with
      | none => addError contribution
          (.unknownModule owner (programExportPathComponents path))
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
      match resolveProgramExportPath? environment module.id path with
      | none => addError contribution
          (.unknownModule module.id (programExportPathComponents path))
      | some target =>
          addPublicModule contribution
            (programExportPathComponents path).getLast! target
  | .moduleAs path alias =>
      match resolveProgramExportPath? environment module.id path with
      | none => addError contribution
          (.unknownModule module.id (programExportPathComponents path))
      | some target => addPublicModule contribution alias.value target
  | .itemsFrom path selection =>
      match resolveProgramExportPath? environment module.id path with
      | none => addError contribution
          (.unknownModule module.id (programExportPathComponents path))
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
