import Solcore.Resolved.Identity
import Solcore.Syntax.Declaration
import Solcore.Workspace
import Solcore.Syntax.Unchecked

/-!
# Program identities, environment and interfaces

The first layers after parsing: identities, the declaration catalog, module resolution and public
interfaces. Main declarations: `ProgramTraitId`, `ProgramImplId`, `BuiltinFunctionId`,
`ProgramEnvironment`, `ProgramDeclaration`.
-/

section
-- leanmerge: from Solcore.Frontend.ProgramEnvironment
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
end

section
-- leanmerge: from Solcore.Frontend.ProgramEnvironmentProperties
/-!
Structural guarantees of the executable whole-program declaration catalog.

These results deliberately cover only identities allocated by
`buildProgramEnvironment`: successful construction rejects repeated canonical
module identities, and declaration identities inherit that module identity
together with their unique top-level source position.
-/

set_option autoImplicit false

namespace Solcore.Frontend

private theorem duplicateModuleErrorsAux_eq_nil
    (seen : List Workspace.ModuleId) (modules : List ProgramModule)
    (errors : duplicateModuleErrorsAux seen modules = []) :
    (modules.map (·.id)).Nodup ∧
      ∀ module, module ∈ modules → module.id ∉ seen := by
  induction modules generalizing seen with
  | nil => simp
  | cons module rest induction =>
      unfold duplicateModuleErrorsAux at errors
      split at errors <;> rename_i duplicate
      · simp at errors
      · have tail := induction (module.id :: seen) errors
        constructor
        · simp only [List.map_cons, List.nodup_cons]
          refine ⟨?_, tail.1⟩
          intro member
          obtain ⟨tailModule, tailMember, idEq⟩ := List.mem_map.mp member
          exact (tail.2 tailModule tailMember (by simp [idEq]))
        · intro candidate member
          simp only [List.mem_cons] at member
          rcases member with rfl | member
          · intro inSeen
            apply duplicate
            exact List.any_eq_true.mpr ⟨candidate.id, inSeen, by simp⟩
          · exact fun inSeen => tail.2 candidate member (by simp [inSeen])

theorem duplicateModuleErrors_eq_nil_ids_nodup
    {modules : List ProgramModule}
    (errors : duplicateModuleErrors modules = []) :
    (modules.map (·.id)).Nodup := by
  exact (duplicateModuleErrorsAux_eq_nil [] modules errors).1

private theorem programDeclarationOfTopItem?_id
    {moduleId : Workspace.ModuleId} {index : Nat} {item : Syntax.TopItem}
    {declaration : ProgramDeclaration}
    (produced : programDeclarationOfTopItem? moduleId index item =
      some declaration) :
    declaration.id = { moduleId, declarationIndex := index } := by
  cases value : item.value <;>
    simp [programDeclarationOfTopItem?, value] at produced
  all_goals subst declaration; rfl

private theorem declarationsOfModule_index_ge_from
    (moduleId : Workspace.ModuleId) (items : List Syntax.TopItem)
    (start : Nat) {declaration : ProgramDeclaration}
    (member : declaration ∈
      (items.zipIdx start).filterMap (fun item =>
        programDeclarationOfTopItem? moduleId item.2 item.1)) :
    start ≤ declaration.id.declarationIndex := by
  simp only [List.mem_filterMap] at member
  obtain ⟨item, itemMember, produced⟩ := member
  have bounds := List.mem_zipIdx itemMember
  have idEq := programDeclarationOfTopItem?_id produced
  rw [idEq]
  exact bounds.1

private theorem declarationsOfModule_ids_nodup_from
    (module : ProgramModule) (start : Nat) :
    ((module.source.items.zipIdx start).filterMap (fun item =>
      programDeclarationOfTopItem? module.id item.2 item.1) |>.map (·.id)).Nodup := by
  induction module.source.items generalizing start with
  | nil => simp
  | cons item rest induction =>
      simp only [List.zipIdx_cons, List.filterMap_cons]
      cases declaration : programDeclarationOfTopItem? module.id start item with
      | none =>
          exact induction (start + 1)
      | some value =>
          have valueId := programDeclarationOfTopItem?_id declaration
          simp only [List.map_cons, List.nodup_cons]
          refine ⟨?_, induction (start + 1)⟩
          intro member
          obtain ⟨tail, tailMember, idEq⟩ := List.mem_map.mp member
          have tailBounds := declarationsOfModule_index_ge_from module.id rest
            (start + 1) tailMember
          rw [idEq, valueId] at tailBounds
          change start + 1 ≤ start at tailBounds
          omega

theorem declarationsOfModule_ids_nodup (module : ProgramModule) :
    ((declarationsOfModule module).map (·.id)).Nodup := by
  exact declarationsOfModule_ids_nodup_from module 0

private theorem declarationsOfModule_id_module
    {module : ProgramModule} {declaration : ProgramDeclaration}
    (member : declaration ∈ declarationsOfModule module) :
    declaration.id.moduleId = module.id := by
  simp only [declarationsOfModule, List.mem_filterMap] at member
  obtain ⟨item, _, produced⟩ := member
  have idEq := programDeclarationOfTopItem?_id produced
  exact congrArg Resolved.DeclarationId.moduleId idEq

private theorem flatMap_declaration_ids_nodup
    (modules : List ProgramModule)
    (moduleIds : (modules.map (·.id)).Nodup) :
    ((modules.flatMap declarationsOfModule).map (·.id)).Nodup := by
  induction modules with
  | nil => simp
  | cons module rest induction =>
      simp only [List.map_cons, List.nodup_cons] at moduleIds
      simp only [List.flatMap_cons, List.map_append, List.nodup_append]
      refine ⟨declarationsOfModule_ids_nodup module,
        induction moduleIds.2, ?_⟩
      intro left leftMember right rightMember same
      obtain ⟨leftDeclaration, leftDeclarationMember, leftId⟩ :=
        List.mem_map.mp leftMember
      obtain ⟨rightDeclaration, rightDeclarationMember, rightId⟩ :=
        List.mem_map.mp rightMember
      obtain ⟨rightModule, rightModuleMember,
          rightDeclarationMember⟩ := List.mem_flatMap.mp rightDeclarationMember
      have leftOwner := declarationsOfModule_id_module leftDeclarationMember
      have rightOwner := declarationsOfModule_id_module rightDeclarationMember
      have moduleEq : module.id = rightModule.id := by
        rw [← leftOwner, ← rightOwner, leftId, rightId, same]
      exact moduleIds.1 (List.mem_map.mpr
        ⟨rightModule, rightModuleMember, moduleEq.symm⟩)

/-- Successful environment construction assigns every module a distinct
canonical identity. -/
theorem buildProgramEnvironment_success_modules_nodup
    {sources : List Syntax.ParsedFile} {environment : ProgramEnvironment}
    (success : buildProgramEnvironment sources = .ok environment) :
    (environment.modules.map (·.id)).Nodup := by
  simp only [buildProgramEnvironment] at success
  split at success <;> rename_i empty
  · have allErrors := List.isEmpty_iff.mp empty
    have moduleErrors :
        duplicateModuleErrors (canonicalizeModules sources).2 = [] := by
      have parts := List.append_eq_nil_iff.mp allErrors
      exact (List.append_eq_nil_iff.mp parts.1).2
    injection success with environmentEq
    subst environment
    exact duplicateModuleErrors_eq_nil_ids_nodup moduleErrors
  · simp at success

/-- Successful environment construction assigns every retained declaration a
distinct `(module, source-position)` identity. -/
theorem buildProgramEnvironment_success_declarations_nodup
    {sources : List Syntax.ParsedFile} {environment : ProgramEnvironment}
    (success : buildProgramEnvironment sources = .ok environment) :
    (environment.declarations.map (·.id)).Nodup := by
  have modules := buildProgramEnvironment_success_modules_nodup success
  simp only [buildProgramEnvironment] at success
  split at success
  · injection success with environmentEq
    subst environment
    exact flatMap_declaration_ids_nodup _ modules
  · simp at success

/-- A successful catalog retains exactly the declarations collected from its
canonical modules, in module and source order. -/
theorem buildProgramEnvironment_success_declarations_eq_flatMap
    {sources : List Syntax.ParsedFile} {environment : ProgramEnvironment}
    (success : buildProgramEnvironment sources = .ok environment) :
    environment.declarations =
      environment.modules.flatMap declarationsOfModule := by
  simp only [buildProgramEnvironment] at success
  split at success
  · injection success with environmentEq
    subst environment
    rfl
  · simp at success

/-- Every retained declaration is owned by one of the canonical modules in
the successfully constructed environment. -/
theorem buildProgramEnvironment_success_declaration_module_exists
    {sources : List Syntax.ParsedFile} {environment : ProgramEnvironment}
    {declaration : ProgramDeclaration}
    (success : buildProgramEnvironment sources = .ok environment)
    (member : declaration ∈ environment.declarations) :
    ∃ module, module ∈ environment.modules ∧
      module.id = declaration.id.moduleId := by
  rw [buildProgramEnvironment_success_declarations_eq_flatMap success] at member
  obtain ⟨module, moduleMember, declarationMember⟩ :=
    List.mem_flatMap.mp member
  exact ⟨module, moduleMember,
    (declarationsOfModule_id_module declarationMember).symm⟩

private theorem find?_eq_some_of_mem_of_nodup_map
    {alpha beta : Type} [DecidableEq beta] (key : alpha → beta)
    {items : List alpha} {item : alpha}
    (unique : (items.map key).Nodup) (member : item ∈ items) :
    items.find? (fun candidate => decide (key candidate = key item)) =
      some item := by
  induction items with
  | nil => simp at member
  | cons head tail induction =>
      simp only [List.map_cons, List.nodup_cons] at unique
      rcases unique with ⟨headAbsent, tailUnique⟩
      simp only [List.mem_cons] at member
      rcases member with rfl | tailMember
      · simp
      · have keysDiffer : key head ≠ key item := by
          intro keysEqual
          apply headAbsent
          rw [keysEqual]
          exact List.mem_map.mpr ⟨item, tailMember, rfl⟩
        simp [List.find?, keysDiffer,
          induction tailUnique tailMember]

/-- Stable-ID lookup returns only a retained declaration with the requested
identity.  This direction does not require a successful builder run. -/
theorem ProgramEnvironment.declaration?_sound
    {environment : ProgramEnvironment} {id : Resolved.DeclarationId}
    {declaration : ProgramDeclaration}
    (found : environment.declaration? id = some declaration) :
    declaration ∈ environment.declarations ∧ declaration.id = id := by
  constructor
  · exact List.mem_of_find?_eq_some found
  · have predicateMatches := List.find?_some found
    simpa [ProgramEnvironment.declaration?] using predicateMatches

/-- Unique stable identities make membership complete for declaration lookup. -/
theorem ProgramEnvironment.declaration?_eq_some_of_mem_of_ids_nodup
    {environment : ProgramEnvironment} {declaration : ProgramDeclaration}
    (unique : (environment.declarations.map (·.id)).Nodup)
    (member : declaration ∈ environment.declarations) :
    environment.declaration? declaration.id = some declaration := by
  exact find?_eq_some_of_mem_of_nodup_map ProgramDeclaration.id unique member

/-- Successful construction makes stable-ID lookup complete for every
retained declaration. -/
theorem buildProgramEnvironment_success_declaration?_eq_some
    {sources : List Syntax.ParsedFile} {environment : ProgramEnvironment}
    {declaration : ProgramDeclaration}
    (success : buildProgramEnvironment sources = .ok environment)
    (member : declaration ∈ environment.declarations) :
    environment.declaration? declaration.id = some declaration := by
  exact ProgramEnvironment.declaration?_eq_some_of_mem_of_ids_nodup
    (buildProgramEnvironment_success_declarations_nodup success) member

/-- In a successfully constructed catalog, stable-ID lookup is equivalent to
declarative membership together with identity agreement. -/
theorem buildProgramEnvironment_success_declaration?_eq_some_iff
    {sources : List Syntax.ParsedFile} {environment : ProgramEnvironment}
    {id : Resolved.DeclarationId} {declaration : ProgramDeclaration}
    (success : buildProgramEnvironment sources = .ok environment) :
    environment.declaration? id = some declaration ↔
      declaration ∈ environment.declarations ∧ declaration.id = id := by
  constructor
  · exact ProgramEnvironment.declaration?_sound
  · rintro ⟨member, rfl⟩
    exact buildProgramEnvironment_success_declaration?_eq_some success member

end Solcore.Frontend
end

section
-- leanmerge: from Solcore.Frontend.ProgramIdentity
/-!
Collision-free identities for compiler functions, traits, and implementations
in the whole-program frontend.

Source declarations and compiler-provided builtins inhabit disjoint variants.
The one-way declaration coercions keep source catalog construction concise,
while consumers that require source declarations must use `declaration?`
explicitly.
-/

set_option autoImplicit false

namespace Solcore.Frontend

/-- Compiler-provided functions that do not have source declaration identities. -/
inductive BuiltinFunctionId where
  | integerSub
  | wordFromInteger
  | integerAdd
  | integerEq
  | integerLt
  | integerMul
  | wordToInteger
  deriving Repr, BEq, DecidableEq

namespace BuiltinFunctionId

/-- Compiler functions implemented by the current frontend, in stable
append-only introduction order.  Name lookup derives from this list so
extending the identity type cannot silently leave a separate hand-written
lookup chain stale. -/
def all : List BuiltinFunctionId :=
  [.integerSub, .wordFromInteger, .integerAdd, .integerEq, .integerLt,
    .integerMul, .wordToInteger]

/-- Every compiler-function identity occurs in the lookup catalog. -/
theorem all_complete (function : BuiltinFunctionId) : function ∈ all := by
  cases function <;> simp [all]

/-- The append-only compiler-function catalog contains no repeated identity. -/
theorem all_nodup : all.Nodup := by
  simp [all]

end BuiltinFunctionId

/-- Compiler-provided traits that do not have source declaration identities. -/
inductive BuiltinTraitId where
  | int
  deriving Repr, BEq, DecidableEq

/-- A trait identity from either the compiler or a resolved source declaration. -/
inductive ProgramTraitId where
  | builtin (id : BuiltinTraitId)
  | declaration (id : Resolved.DeclarationId)
  deriving Repr, BEq, DecidableEq

instance : Coe Resolved.DeclarationId ProgramTraitId where
  coe := .declaration

namespace ProgramTraitId

/-- Recover the source declaration identity when this is a source trait. -/
def declaration? : ProgramTraitId → Option Resolved.DeclarationId
  | .builtin _ => none
  | .declaration id => some id

end ProgramTraitId

/-- Compiler-provided implementations that do not have source declarations. -/
inductive BuiltinImplId where
  | intInteger
  | intWord
  deriving Repr, BEq, DecidableEq

/-- An implementation identity from either the compiler or source catalog. -/
inductive ProgramImplId where
  | builtin (id : BuiltinImplId)
  | declaration (id : Resolved.DeclarationId)
  deriving Repr, BEq, DecidableEq

instance : Coe Resolved.DeclarationId ProgramImplId where
  coe := .declaration

namespace ProgramImplId

/-- Recover the source declaration identity when this is a source impl. -/
def declaration? : ProgramImplId → Option Resolved.DeclarationId
  | .builtin _ => none
  | .declaration id => some id

end ProgramImplId

end Solcore.Frontend
end

section
-- leanmerge: from Solcore.Frontend.ProgramModuleResolution
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
end

section
-- leanmerge: from Solcore.Frontend.ProgramInterfaces
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
end

section
-- leanmerge: from Solcore.Frontend.ProgramLoading
/-! Validation and parsing at the executable whole-program boundary. -/

set_option autoImplicit false

namespace Solcore.Frontend

/-- One validated workspace together with every diagnostic-free parsed source. -/
structure LoadedProgram where
  workspace : Workspace.ValidatedUserWorkspace
  sources : List Syntax.ParsedFile
  environment : ProgramEnvironment
  deriving Repr

/-- Failures before source type checking begins. -/
inductive ProgramLoadError where
  | workspace (error : Workspace.ValidationError)
  | syntaxInvariant
      (source : Workspace.SourceId)
      (error : Syntax.SyntaxInvariantError)
  | sourceDiagnostics
      (source : Workspace.SourceId)
      (lexical : List Syntax.LexicalDiagnostic)
      (parsing : List Syntax.ParseDiagnostic)
  | uncheckedBlock
      (source : Workspace.SourceId)
      (error : Syntax.Unchecked.Error)
  | environment (error : ProgramEnvironmentError)
  deriving Repr

/-- Convert a canonical workspace library into its parser-visible owner. -/
def syntaxOriginOfWorkspaceLibrary :
    Workspace.LibraryId → Syntax.SourceOrigin
  | .main => .main
  | .standard => .standard
  | .external name => .external name.render

/-- Preserve a validated identity at the parser boundary. -/
def syntaxSourceIdOfWorkspaceSource
    (source : Workspace.SourceId) : Syntax.SourceId := {
  origin := syntaxOriginOfWorkspaceLibrary source.library
  path := source.path.render
}

/-- Present a validated source to the canonical parser. -/
def syntaxSourceFileOfWorkspaceFile
    (file : Workspace.WorkspaceFile) : Syntax.SourceFile := {
  id := syntaxSourceIdOfWorkspaceSource file.id
  content := file.content
}

private def parseWorkspaceFile
    (file : Workspace.WorkspaceFile) :
    Except ProgramLoadError Syntax.ParsedFile :=
  let source := syntaxSourceFileOfWorkspaceFile file
  match Syntax.Unchecked.prepare source with
  | .error error => .error (.uncheckedBlock file.id error)
  | .ok (blanked, blocks) =>
  match Syntax.Parser.parse blanked with
  | .error error => .error (.syntaxInvariant file.id error)
  | .ok output =>
      if output.lexicalDiagnostics.isEmpty &&
          output.parseDiagnostics.isEmpty then
        (Syntax.Unchecked.mark (4 * source.content.utf8ByteSize + 4) blocks output.parsed).mapError
          (.uncheckedBlock file.id)
      else
        .error (.sourceDiagnostics file.id output.lexicalDiagnostics
          output.parseDiagnostics)

private def parseWorkspaceFiles :
    List Workspace.WorkspaceFile →
      List ProgramLoadError × List Syntax.ParsedFile
  | [] => ([], [])
  | file :: rest =>
      let (restErrors, restSources) := parseWorkspaceFiles rest
      match parseWorkspaceFile file with
      | .ok source => (restErrors, source :: restSources)
      | .error error => (error :: restErrors, restSources)

/-- Parse and catalog an already validated workspace. -/
def loadValidatedProgram
    (workspace : Workspace.ValidatedUserWorkspace) :
    Except (List ProgramLoadError) LoadedProgram :=
  let (parseErrors, sources) := parseWorkspaceFiles workspace.files
  if parseErrors.isEmpty then
    match buildProgramEnvironment sources with
    | .ok environment => .ok { workspace, sources, environment }
    | .error errors => .error (errors.map ProgramLoadError.environment)
  else
    .error parseErrors

/-- Validate, parse and catalog one complete caller workspace. -/
def loadProgram (raw : Workspace.RawWorkspace) :
    Except (List ProgramLoadError) LoadedProgram :=
  match Workspace.validate raw with
  | .error errors => .error (errors.map ProgramLoadError.workspace)
  | .ok workspace => loadValidatedProgram workspace

/-- A successful validated-workspace load retains the exact declaration
environment constructed from its parsed sources. -/
theorem loadValidatedProgram_success_environment
    {workspace : Workspace.ValidatedUserWorkspace}
    {loaded : LoadedProgram}
    (success : loadValidatedProgram workspace = .ok loaded) :
    buildProgramEnvironment loaded.sources = .ok loaded.environment := by
  cases parsed : parseWorkspaceFiles workspace.files with
  | mk parseErrors sources =>
      simp only [loadValidatedProgram, parsed] at success
      by_cases noParseErrors : parseErrors.isEmpty
      · simp only [noParseErrors, if_true] at success
        cases environmentResult : buildProgramEnvironment sources with
        | error errors => simp [environmentResult] at success
        | ok environment =>
            simp only [environmentResult, Except.ok.injEq] at success
            subst loaded
            exact environmentResult
      · simp [noParseErrors] at success

/-- A successful raw-workspace load likewise exposes the exact environment
builder success retained in the loaded carrier. -/
theorem loadProgram_success_environment
    {raw : Workspace.RawWorkspace}
    {loaded : LoadedProgram}
    (success : loadProgram raw = .ok loaded) :
    buildProgramEnvironment loaded.sources = .ok loaded.environment := by
  cases validationResult : Workspace.validate raw with
  | error errors => simp [loadProgram, validationResult] at success
  | ok workspace =>
      apply loadValidatedProgram_success_environment
      simpa [loadProgram, validationResult] using success

/-- Loaded declaration identities are unique because every successful raw
load is backed by a successful environment construction. -/
theorem loadProgram_success_declarations_nodup
    {raw : Workspace.RawWorkspace}
    {loaded : LoadedProgram}
    (success : loadProgram raw = .ok loaded) :
    (loaded.environment.declarations.map (·.id)).Nodup :=
  buildProgramEnvironment_success_declarations_nodup
    (loadProgram_success_environment success)

end Solcore.Frontend
end
