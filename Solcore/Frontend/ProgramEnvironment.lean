import Solcore.Resolved.Identity
import Solcore.Syntax.Declaration

/-!
An executable, deliberately small whole-program declaration catalog.

This is the first semantic layer after parsing.  It assigns declaration IDs
from canonical module identity plus top-level source order, and rejects the
name collisions that would make type and trait lookup non-deterministic.
Import/export visibility and nested contract declarations are intentionally
left to a later layer.
-/

set_option autoImplicit false

namespace Solcore.Frontend

/-- The declaration forms retained by the first whole-program catalog. -/
inductive ProgramDeclarationKind where
  | typeAlias
  | enum
  | trait
  | implementation
  | contract
  | function
  deriving Repr, BEq, DecidableEq

/-- Independent source namespaces needed before overload resolution exists. -/
inductive ProgramDeclarationNamespace where
  | type
  | trait
  | value
  deriving Repr, BEq, DecidableEq

/-- One parsed top-level declaration with its stable whole-program identity. -/
structure ProgramDeclaration where
  id : Resolved.DeclarationId
  kind : ProgramDeclarationKind
  nameSpace : Option ProgramDeclarationNamespace
  name : Option String
  genericParameters : List String
  source : Syntax.TopItem
  deriving Repr

/-- A parsed source after its syntax identity has been canonicalized. -/
structure ProgramModule where
  id : Workspace.ModuleId
  source : Syntax.ParsedFile
  deriving Repr

/-- The executable whole-program declaration/type environment. -/
structure ProgramEnvironment where
  modules : List ProgramModule
  declarations : List ProgramDeclaration
  deriving Repr

/-- Construction failures that make whole-program lookup non-deterministic. -/
inductive ProgramEnvironmentError where
  | invalidSourceId (source : Syntax.SourceId)
  | duplicateModule (moduleId : Workspace.ModuleId)
  | duplicateDeclaration
      (moduleId : Workspace.ModuleId)
      (nameSpace : ProgramDeclarationNamespace)
      (name : String)
      (first duplicate : Resolved.DeclarationId)
  deriving Repr, DecidableEq

/-- Translate the parser's permissive source owner into a canonical library. -/
def workspaceLibraryOfSyntaxOrigin? :
    Syntax.SourceOrigin → Option Workspace.LibraryId
  | .main => some .main
  | .standard => some .standard
  | .external name =>
      (Workspace.ExternalLibraryName.parse name).map Workspace.LibraryId.external

/-- Canonicalize a parser source identity for whole-program use. -/
def workspaceModuleOfSyntaxSource? (source : Syntax.SourceId) :
    Option Workspace.ModuleId := do
  let library ← workspaceLibraryOfSyntaxOrigin? source.origin
  let path ← Workspace.CanonicalSourcePath.parse source.path
  pure {
    library
    path := path.modulePath
  }

private def identifierTexts (parameters : List Syntax.Identifier) : List String :=
  parameters.map (·.value)

private def optionalGenericParameterTexts
    (parameters : Option Syntax.GenericParameters) : List String :=
  match parameters with
  | none => []
  | some parameters => identifierTexts parameters.elements.toList

private def optionalAliasParameterTexts
    (parameters : Option (Syntax.DelimitedList Syntax.Identifier)) : List String :=
  match parameters with
  | none => []
  | some parameters => identifierTexts parameters.elements

/-- Produce the catalog row for one semantic top-level item. -/
def programDeclarationOfTopItem?
    (moduleId : Workspace.ModuleId) (declarationIndex : Nat)
    (item : Syntax.TopItem) : Option ProgramDeclaration :=
  let id : Resolved.DeclarationId := { moduleId, declarationIndex }
  match item.value with
  | .typeAlias declaration => some {
      id
      kind := .typeAlias
      nameSpace := some .type
      name := some declaration.value.name.value
      genericParameters :=
        optionalAliasParameterTexts declaration.value.parameters
      source := item
    }
  | .enum declaration => some {
      id
      kind := .enum
      nameSpace := some .type
      name := some declaration.value.name.value
      genericParameters :=
        optionalGenericParameterTexts declaration.value.parameters
      source := item
    }
  | .trait declaration => some {
      id
      kind := .trait
      nameSpace := some .trait
      name := some declaration.value.name.value
      genericParameters :=
        identifierTexts declaration.value.genericParameters.elements.toList
      source := item
    }
  | .impl declaration => some {
      id
      kind := .implementation
      nameSpace := none
      name := none
      genericParameters :=
        optionalGenericParameterTexts declaration.value.genericParameters
      source := item
    }
  | .contract declaration => some {
      id
      kind := .contract
      nameSpace := some .type
      name := some declaration.value.name.value
      genericParameters :=
        optionalGenericParameterTexts declaration.value.genericParameters
      source := item
    }
  | .function declaration => some {
      id
      kind := .function
      nameSpace := some .value
      name := some declaration.value.signature.name.value
      genericParameters :=
        optionalGenericParameterTexts
          declaration.value.signature.genericParameters
      source := item
    }
  | .importDecl _
  | .exportDecl _
  | .pragmaDecl _
  | .error => none

/-- Cataloged semantic declarations of one module, retaining source indices. -/
def declarationsOfModule (module : ProgramModule) :
    List ProgramDeclaration :=
  module.source.items.zipIdx.filterMap fun (item, declarationIndex) =>
    programDeclarationOfTopItem? module.id declarationIndex item

/-- Canonicalize all valid parser source identities without dropping errors. -/
def canonicalizeModules : List Syntax.ParsedFile →
    List ProgramEnvironmentError × List ProgramModule
  | [] => ([], [])
  | source :: rest =>
      let (errors, modules) := canonicalizeModules rest
      match workspaceModuleOfSyntaxSource? source.source with
      | none => (.invalidSourceId source.source :: errors, modules)
      | some id => (errors, { id, source } :: modules)

def duplicateModuleErrorsAux
    (seen : List Workspace.ModuleId) :
    List ProgramModule → List ProgramEnvironmentError
  | [] => []
  | module :: rest =>
      if seen.any fun previous => decide (previous = module.id) then
        .duplicateModule module.id :: duplicateModuleErrorsAux seen rest
      else
        duplicateModuleErrorsAux (module.id :: seen) rest

def duplicateModuleErrors
    (modules : List ProgramModule) : List ProgramEnvironmentError :=
  duplicateModuleErrorsAux [] modules

private structure DeclarationCollisionKey where
  moduleId : Workspace.ModuleId
  nameSpace : ProgramDeclarationNamespace
  name : String
  deriving DecidableEq

private def ProgramDeclaration.collisionKey?
    (declaration : ProgramDeclaration) : Option DeclarationCollisionKey := do
  let nameSpace ← declaration.nameSpace
  let name ← declaration.name
  -- Values will acquire overload sets.  Type and trait heads must already be
  -- unique for deterministic resolution.
  if nameSpace == ProgramDeclarationNamespace.value then
    none
  else
    pure { moduleId := declaration.id.moduleId, nameSpace, name }

private def duplicateDeclarationErrorsAux
    (seen : List (DeclarationCollisionKey × Resolved.DeclarationId)) :
    List ProgramDeclaration → List ProgramEnvironmentError
  | [] => []
  | declaration :: rest =>
      match declaration.collisionKey? with
      | none => duplicateDeclarationErrorsAux seen rest
      | some key =>
          match seen.find? fun previous => decide (previous.1 = key) with
          | none =>
              duplicateDeclarationErrorsAux ((key, declaration.id) :: seen) rest
          | some previous =>
              .duplicateDeclaration key.moduleId key.nameSpace key.name
                  previous.2 declaration.id ::
                duplicateDeclarationErrorsAux seen rest

private def duplicateDeclarationErrors
    (declarations : List ProgramDeclaration) : List ProgramEnvironmentError :=
  duplicateDeclarationErrorsAux [] declarations

/-- Build one catalog from any number of parsed source files. -/
def buildProgramEnvironment (sources : List Syntax.ParsedFile) :
    Except (List ProgramEnvironmentError) ProgramEnvironment :=
  let canonicalized := canonicalizeModules sources
  let sourceErrors := canonicalized.1
  let modules := canonicalized.2
  let moduleErrors := duplicateModuleErrors modules
  let declarations := modules.flatMap declarationsOfModule
  let declarationErrors := duplicateDeclarationErrors declarations
  let errors := sourceErrors ++ moduleErrors ++ declarationErrors
  if errors.isEmpty then
    .ok { modules, declarations }
  else
    .error errors

namespace ProgramEnvironment

/-- Find one declaration by its stable identity. -/
def declaration? (environment : ProgramEnvironment)
    (id : Resolved.DeclarationId) : Option ProgramDeclaration :=
  environment.declarations.find? fun declaration => decide (declaration.id = id)

/-- All declarations in one canonical module, preserving source order. -/
def declarationsIn (environment : ProgramEnvironment)
    (moduleId : Workspace.ModuleId) : List ProgramDeclaration :=
  environment.declarations.filter fun declaration =>
    decide (declaration.id.moduleId = moduleId)

/-- Declarations in one namespace with an exact spelling in one module. -/
def localDeclarationsNamed (environment : ProgramEnvironment)
    (moduleId : Workspace.ModuleId) (nameSpace : ProgramDeclarationNamespace)
    (name : String) :
    List ProgramDeclaration :=
  environment.declarations.filter fun declaration =>
    decide (declaration.id.moduleId = moduleId) &&
      declaration.nameSpace == some nameSpace &&
      declaration.name == some name

/-- Declarations in one namespace with an exact spelling anywhere. -/
def declarationsNamed (environment : ProgramEnvironment)
    (nameSpace : ProgramDeclarationNamespace) (name : String) :
    List ProgramDeclaration :=
  environment.declarations.filter fun declaration =>
    declaration.nameSpace == some nameSpace &&
      declaration.name == some name

/-- Type declarations with an exact spelling in one module. -/
def localTypesNamed (environment : ProgramEnvironment)
    (moduleId : Workspace.ModuleId) (name : String) :
    List ProgramDeclaration :=
  environment.localDeclarationsNamed moduleId .type name

/-- Type declarations with an exact spelling anywhere in the program. -/
def typesNamed (environment : ProgramEnvironment) (name : String) :
    List ProgramDeclaration :=
  environment.declarationsNamed .type name

/-- Trait declarations with an exact spelling in one module. -/
def localTraitsNamed (environment : ProgramEnvironment)
    (moduleId : Workspace.ModuleId) (name : String) :
    List ProgramDeclaration :=
  environment.localDeclarationsNamed moduleId .trait name

/-- Trait declarations with an exact spelling anywhere in the program. -/
def traitsNamed (environment : ProgramEnvironment) (name : String) :
    List ProgramDeclaration :=
  environment.declarationsNamed .trait name

/-- Function declarations forming a local overload set. -/
def localValuesNamed (environment : ProgramEnvironment)
    (moduleId : Workspace.ModuleId) (name : String) :
    List ProgramDeclaration :=
  environment.localDeclarationsNamed moduleId .value name

/-- Function declarations with an exact spelling anywhere in the program. -/
def valuesNamed (environment : ProgramEnvironment) (name : String) :
    List ProgramDeclaration :=
  environment.declarationsNamed .value name

/-- Return a result exactly when the candidate set has one element. -/
def uniqueDeclaration? : List ProgramDeclaration → Option ProgramDeclaration
  | [declaration] => some declaration
  | _ => none

/-- Unique type lookup in one module. -/
def localType? (environment : ProgramEnvironment)
    (moduleId : Workspace.ModuleId) (name : String) :
    Option ProgramDeclaration :=
  uniqueDeclaration? (environment.localTypesNamed moduleId name)

/-- Unique trait lookup in one module. -/
def localTrait? (environment : ProgramEnvironment)
    (moduleId : Workspace.ModuleId) (name : String) :
    Option ProgramDeclaration :=
  uniqueDeclaration? (environment.localTraitsNamed moduleId name)

end ProgramEnvironment

end Solcore.Frontend
