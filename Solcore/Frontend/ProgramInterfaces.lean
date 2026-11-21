import Solcore.Resolved.Identity
import Solcore.TypeSystem.Type
import Solcore.Syntax.Declaration
import Solcore.Workspace
import Solcore.Syntax.Unchecked
import Solcore.Frontend.StandardModules

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

/-- The namespace in which an import meets a declaration or an earlier import, as
upstream's: values apart, and types, enums, contracts and traits together. -/
def ProgramDeclarationNamespace.importGroup :
    ProgramDeclarationNamespace → ProgramDeclarationNamespace
  | .value => .value
  | .type | .trait => .type

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

/-- The 26 pure word functions of upstream's `std.opcodes`, each one EVM opcode
on words, in the opcodes' order. -/
inductive WordOpcode where
  | add | mul | sub | div | sdiv | mod | smod | addmod | mulmod | exp | signextend
  | lt | gt | slt | sgt | eq | iszero | and | or | xor | not | byte | shl | shr | sar | clz
  deriving Repr, BEq, DecidableEq

namespace WordOpcode

/-- The opcodes in their order. -/
def all : List WordOpcode :=
  [.add, .mul, .sub, .div, .sdiv, .mod, .smod, .addmod, .mulmod, .exp, .signextend,
    .lt, .gt, .slt, .sgt, .eq, .iszero, .and, .or, .xor, .not, .byte, .shl, .shr, .sar, .clz]

/-- The opcode's name, as `std.opcodes` exports it. -/
def name : WordOpcode → String
  | .add => "add" | .mul => "mul" | .sub => "sub" | .div => "div" | .sdiv => "sdiv"
  | .mod => "mod" | .smod => "smod" | .addmod => "addmod" | .mulmod => "mulmod"
  | .exp => "exp" | .signextend => "signextend" | .lt => "lt" | .gt => "gt"
  | .slt => "slt" | .sgt => "sgt" | .eq => "eq" | .iszero => "iszero" | .and => "and"
  | .or => "or" | .xor => "xor" | .not => "not" | .byte => "byte" | .shl => "shl"
  | .shr => "shr" | .sar => "sar" | .clz => "clz"

/-- The number of words the opcode takes. -/
def arity : WordOpcode → Nat
  | .iszero | .not | .clz => 1
  | .addmod | .mulmod => 3
  | _ => 2

theorem all_complete (op : WordOpcode) : op ∈ all := by
  cases op <;> simp [all]

theorem all_nodup : all.Nodup := by
  decide

/-- The opcode a `std.opcodes` name denotes, if it is one of the 26. -/
def ofName? (name : String) : Option WordOpcode :=
  all.find? (·.name == name)

end WordOpcode

/-- Compiler-provided functions that do not have source declaration identities. -/
inductive BuiltinFunctionId where
  | integerSub
  | wordFromInteger
  | integerAdd
  | integerEq
  | integerLt
  | integerMul
  | wordToInteger
  /-- `uint256(w)`, `uintN(w)` and `intN(w)`: a word as a value of one of the
  twelve fixed-width integer types. A word that is not canonical for the type
  reverts with `DirtyHigherBitsForInteger()`. A conversion is no closure: it is
  lowered where it is called, so it is not in `all`. -/
  | fixedFromWord (type : TypeSystem.FixedInteger)
  /-- `Typedef.rep(x)` at one of the twelve fixed-width integer types: the
  value's word. A conversion, so not in `all`. -/
  | fixedToWord (type : TypeSystem.FixedInteger)
  /-- `Typedef.abs(w)` and `Typedef.rep(w)` at `word`: the word itself, as
  upstream's `default impl<t> Typedef<t, t>` gives it. A conversion, so not in
  `all`. -/
  | wordIdentity
  /-- One of upstream's `std.opcodes` pure word functions: a closure over its
  Core primitive. It has no bare spelling; only `std.opcodes` would name it. -/
  | wordOpcode (op : WordOpcode)
  deriving Repr, BEq, DecidableEq

namespace BuiltinFunctionId

/-- Compiler functions implemented by the current frontend as closures, in
stable append-only introduction order, the opcodes last. Name lookup derives
from this list and from the twelve types' names, so extending the identity
type cannot silently leave a separate hand-written lookup chain stale. -/
def all : List BuiltinFunctionId :=
  [.integerSub, .wordFromInteger, .integerAdd, .integerEq, .integerLt,
    .integerMul, .wordToInteger] ++ WordOpcode.all.map .wordOpcode

/-- The opcode a closure applies, if it is one. -/
def opcode? : BuiltinFunctionId → Option WordOpcode
  | .wordOpcode op => some op
  | _ => none

/-- The type a conversion gives, or none for a closure. A conversion is
lowered where it is called: the word checked against the type at a fixed-width
type, and the word itself at `word`. -/
def conversion? : BuiltinFunctionId → Option TypeSystem.Ty
  | .fixedFromWord type => some (.fixed type)
  | .fixedToWord _ | .wordIdentity => some .word
  | _ => none

/-- Every compiler-function identity is a closure of the lookup catalog or a
conversion. -/
theorem all_complete (function : BuiltinFunctionId) :
    function ∈ all ∨ ∃ type, function.conversion? = some type := by
  cases function <;> simp [all, conversion?, WordOpcode.all_complete]

/-- The catalog's closures are no conversions. -/
theorem conversion?_of_mem {function : BuiltinFunctionId} (member : function ∈ all) :
    function.conversion? = none := by
  cases function <;> first | rfl | simp_all [all]

/-- A function found in the catalog's numbering is no conversion. -/
theorem conversion?_of_inventory {function : BuiltinFunctionId} {index : Nat}
    (inventory : all.zipIdx.find? (fun item => decide (item.1 = function)) = some (function, index)) :
    function.conversion? = none :=
  conversion?_of_mem (List.mem_of_find?_eq_some inventory |> List.fst_mem_of_mem_zipIdx)

/-- The append-only compiler-function catalog contains no repeated identity. -/
theorem all_nodup : all.Nodup := by
  decide

/-- The catalog's numbering finds each of its closures at its own index. -/
theorem find?_zipIdx_of_mem {function : BuiltinFunctionId} {index : Nat}
    (member : (function, index) ∈ all.zipIdx) :
    all.zipIdx.find? (fun item => decide (item.1 = function)) = some (function, index) := by
  cases found : all.zipIdx.find? (fun item => decide (item.1 = function)) with
  | none =>
    rw [List.find?_eq_none] at found
    exact absurd (by simp) (found _ member)
  | some item =>
    obtain ⟨actual, other⟩ := item
    have same : actual = function := by simpa using List.find?_some found
    subst same
    have first := List.mk_mem_zipIdx_iff_getElem?.mp (List.mem_of_find?_eq_some found)
    have second := List.mk_mem_zipIdx_iff_getElem?.mp member
    have equal := (List.getElem?_inj (List.getElem?_eq_some_iff.mp first).1 all_nodup).mp
      (first.trans second.symm)
    rw [equal]

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
  /-- `Int<uintN>` or `Int<intN>`, for one of the twelve fixed-width types. -/
  | intFixed (type : TypeSystem.FixedInteger)
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
  /-- A selected or wildcard import that brings a name a declaration of the importing module
  has in the same import group (`ProgramDeclarationNamespace.importGroup`), as upstream's
  `SC0108` refuses it. -/
  | importedNameConflict
      (owner : Workspace.ModuleId)
      (nameSpace : ProgramDeclarationNamespace)
      (name : String)
  /-- A selective import that lists one source name twice or binds one local name twice, or a
  hiding clause that hides one name twice, as upstream's `SC0117` refuses it. -/
  | duplicateImportName
      (owner : Workspace.ModuleId)
      (name : String)
  /-- A local name that selected or wildcard imports bring from two or more modules, in any
  import group and used or not, as upstream's `SC0120` refuses it. -/
  | ambiguousImport
      (owner : Workspace.ModuleId)
      (name : String)
      (targets : List Workspace.ModuleId)
  /-- A plain or namespace import's qualifier beside a value of the module of the same name,
  declared or imported, as upstream's `SC0121` refuses it. -/
  | importQualifierConflict
      (owner : Workspace.ModuleId)
      (name : String)
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

/-- The identity that stands for upstream's `std.opcodes`, a standard module Lean has no source
for: an import of it binds its functions (`standardOpcodeNames`), the 26 pure ones to builtins. -/
def standardOpcodesModule : Workspace.ModuleId :=
  ⟨.standard, ⟨[⟨"opcodes", by decide⟩], by simp⟩⟩

/-- Whether an import's path names upstream's `std.opcodes`. It stands for that module where no
module of the program resolves at the path. -/
def isStandardOpcodesPath (path : Syntax.ModulePath) : Bool :=
  path.value.externalMarker.isNone && programModulePathComponents path == ["std", "opcodes"]

/-- Whether an import's path names one of upstream's std modules (`upstreamStandardModulePaths`).
It stands for that module where no module of the program resolves at the path. -/
def isUpstreamStandardPath (path : Syntax.ModulePath) : Bool :=
  path.value.externalMarker.isNone &&
    upstreamStandardModulePaths.contains (programModulePathComponents path)

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
  | none =>
      -- An import of one of upstream's std modules binds no declarations: the load checks it
      -- (`standardOpcodeImportErrors`, `standardModuleImportErrors`), and the import tables bind
      -- `std.opcodes`' builtins and nothing for the others (`buildProgramImports`).
      if isUpstreamStandardPath path then {}
      else { errors := [.unknownModule owner (programModulePathComponents path)] }
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

private def importPath (declaration : Syntax.ImportDecl) : Syntax.ModulePath :=
  match declaration.value with
  | .plain path | .namespace path _ | .wildcard path _ | .selected _ path _ => path

/-- A local name an earlier import declaration bound, with its import group and the module
it came from. -/
private structure EarlierImport where
  localName : String
  group : ProgramDeclarationNamespace
  target : Workspace.ModuleId

private def VisibleEntity.importGroup? (entity : VisibleEntity) :
    Option ProgramDeclarationNamespace :=
  entity.declaration.nameSpace.map ProgramDeclarationNamespace.importGroup

/-- Whether an earlier import declaration bound this entity's local name in its group from the
same module. Upstream keeps that first binding and ignores the later one; the same name from
another module is upstream's `SC0120`, which stays an ambiguity here. -/
private def boundEarlier (earlier : List EarlierImport) (target : Workspace.ModuleId)
    (entity : VisibleEntity) : Bool :=
  match entity.importGroup? with
  | none => false
  | some group => earlier.any fun binding =>
      binding.localName == entity.localName && binding.group == group &&
        decide (binding.target = target)

private def earlierImports (target : Workspace.ModuleId)
    (entities : List VisibleEntity) : List EarlierImport :=
  entities.filterMap fun entity => entity.importGroup?.map fun group =>
    { localName := entity.localName, group, target }

/-- The module's imported visibility: each import declaration's entities, less those whose local
name an earlier declaration bound from the same module. One declaration's own candidates, an
overload set among them, all stay. -/
private def importedVisibility
    (environment : ProgramEnvironment) (interfaces : ProgramInterfaces)
    (module : ProgramModule) : VisibilityResult :=
  let result := (importsIn module).foldl
      (fun (state : VisibilityResult × List EarlierImport) declaration =>
    let next := processImport environment interfaces module.id declaration
    match resolveProgramModulePath? environment module.id (importPath declaration) with
    | none => ({ state.1 with errors := state.1.errors ++ next.errors }, state.2)
    | some target =>
        let kept := next.entities.filter fun entity => !boundEarlier state.2 target entity
        ({ entities := mergeVisible state.1.entities kept
           errors := state.1.errors ++ next.errors },
          state.2 ++ earlierImports target next.entities)) ({}, [])
  result.1

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

/-- Upstream's `SC0108` for imports: each name that a selected or wildcard import brings, and
that a declaration of the module has in the same import group, once per group and name, in
import order. Hidden names and constructors are not brought, so they meet nothing. -/
private def importConflicts
    (environment : ProgramEnvironment) (interfaces : ProgramInterfaces)
    (module : ProgramModule) (locals : List VisibleEntity) :
    List ProgramInterfaceError :=
  let imported := (importsIn module).flatMap fun declaration =>
    (processImport environment interfaces module.id declaration).entities
  let clashes := imported.filterMap fun entity => do
    let group ← entity.importGroup?
    if locals.any (fun declared => declared.localName == entity.localName &&
        declared.importGroup? == some group &&
        !decide (declared.declaration.id = entity.declaration.id)) then
      some (group, entity.localName)
    else none
  let unique := clashes.foldl (fun seen clash =>
    if seen.contains clash then seen else seen ++ [clash]) []
  unique.map fun (group, name) => .importedNameConflict module.id group name

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

/-- The converged public interfaces, beside every module's interface errors. -/
private def programInterfacesWithErrors (environment : ProgramEnvironment) :
    Except ProgramInterfaceError (ProgramInterfaces × List ProgramInterfaceError) := do
  let interfaces ← closeInterfaces environment (closureFuel environment)
    (emptyInterfaces environment)
  pure (interfaces, finalErrors environment interfaces)

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

/-- The pragma that marks a Solcore source file. -/
def solcorePragmaName : String := "solcore"

/-- One violation of the leading `pragma solcore;` that every source file declares, once and
with no arguments, before every other declaration, as upstream's `SC0002` requires. -/
inductive PragmaSolcoreProblem where
  /-- No `pragma solcore;`: an empty span at the first declaration, or at the file's start when
  it declares nothing. -/
  | missing (span : Syntax.SourceSpan)
  /-- The first declaration is `pragma solcore` with arguments, spanning them. -/
  | arguments (span : Syntax.SourceSpan)
  /-- `pragma solcore;` after another declaration, which is the file's first. -/
  | misplaced (span : Syntax.SourceSpan)
  /-- A `pragma solcore;` after the one that counts. -/
  | duplicate (span : Syntax.SourceSpan)
  deriving Repr, BEq, DecidableEq

/-- Whether a top item is `pragma solcore`, with arguments or not. -/
def isSolcorePragma (item : Syntax.TopItem) : Bool :=
  match item.value with
  | .pragmaDecl declaration => declaration.value.name.value == solcorePragmaName
  | _ => false

/-- The span of a pragma's arguments, from the first to the last, if it has any. -/
def pragmaArgumentsSpan? (item : Syntax.TopItem) : Option Syntax.SourceSpan :=
  match item.value with
  | .pragmaDecl declaration => do
      let first ← declaration.value.items.head?
      let last ← declaration.value.items.getLast?
      pure { first.span with endByte := last.span.endByte }
  | _ => none

/-- The violations of the leading `pragma solcore;` in a file that parsed with no diagnostic, as
upstream's `pragma_solcore_problems` finds them: the first declaration must be `pragma solcore`
with no arguments, and no other may follow it. With another declaration first, the first later
`pragma solcore;` is misplaced and the rest are duplicates. -/
def pragmaSolcoreProblems (file : Syntax.ParsedFile) : List PragmaSolcoreProblem :=
  let declarations := file.items.filter isSolcorePragma
  match file.items with
  | [] => [.missing { file.span with endByte := file.span.startByte }]
  | first :: _ =>
      if first.value matches .error then []
      else if isSolcorePragma first then
        (pragmaArgumentsSpan? first).toList.map PragmaSolcoreProblem.arguments ++
          (declarations.drop 1).map fun item => .duplicate item.span
      else
        match declarations with
        | [] => [.missing { first.span with endByte := first.span.startByte }]
        | misplaced :: rest =>
            .misplaced misplaced.span :: rest.map fun item => .duplicate item.span

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
  /-- A source that parsed with no diagnostic violates its leading `pragma solcore;`. -/
  | pragmaSolcore
      (source : Workspace.SourceId)
      (problems : List PragmaSolcoreProblem)
  | uncheckedBlock
      (source : Workspace.SourceId)
      (error : Syntax.Unchecked.Error)
  | environment (error : ProgramEnvironmentError)
  /-- Imports that upstream refuses where they are, in the modules reachable from the entry: an
  unknown module, an unknown selected or hidden item (`SC0110`), a name an import brings beside
  a declaration of the module (`SC0108`), a name listed twice in one import (`SC0117`), a name
  from two modules (`SC0120`), and a qualifier beside a value (`SC0121`)
  (`programImportErrors`). -/
  | imports (errors : List ProgramInterfaceError)
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
        match pragmaSolcoreProblems output.parsed with
        | [] =>
            (Syntax.Unchecked.mark (4 * source.content.utf8ByteSize + 4) blocks
              output.parsed).mapError (.uncheckedBlock file.id)
        | problems => .error (.pragmaSolcore file.id problems)
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

/-- Whether a load reports an interface error where the import is, as upstream reports it: an
unknown module other than one of upstream's std modules, an unknown selected or hidden item,
and the import rules (`importRuleErrors`). The other errors are reported where a name
resolves. -/
def ProgramInterfaceError.reportedAtLoad : ProgramInterfaceError → Bool
  | .unknownModule _ components => !upstreamStandardModulePaths.contains components
  | .unknownImportName _ _ _ | .importedNameConflict _ _ _ | .duplicateImportName _ _
  | .ambiguousImport _ _ _ | .importQualifierConflict _ _ => true
  | .unknownExportName _ _ | .unknownExportConstructor _ _ _ | .fixedPointExhausted => false

/-- The module an interface error is in. -/
def ProgramInterfaceError.owner? : ProgramInterfaceError → Option Workspace.ModuleId
  | .unknownModule owner _ | .unknownImportName owner _ _ | .unknownExportName owner _
  | .unknownExportConstructor owner _ _ | .importedNameConflict owner _ _
  | .duplicateImportName owner _ | .ambiguousImport owner _ _
  | .importQualifierConflict owner _ => some owner
  | .fixedPointExhausted => none

/-- The modules that a module's imports and re-exports name, where they resolve. -/
def programModuleReferences (environment : ProgramEnvironment) (module : ProgramModule) :
    List Workspace.ModuleId :=
  module.source.items.flatMap fun item =>
    match item.value with
    | .importDecl declaration =>
        (resolveProgramModulePath? environment module.id (importPath declaration)).toList
    | .exportDecl declaration =>
        let paths : List Syntax.QualifiedName := match declaration.value with
          | .local items => items.elements.filterMap fun item =>
              match item.value with
              | .moduleWildcard path _ => some path
              | .name _ => none
          | .module path => [path]
          | .moduleAs path _ => [path]
          | .itemsFrom path _ => [path]
        paths.filterMap (resolveProgramExportPath? environment module.id)
    | _ => []

private def reachableFrom (environment : ProgramEnvironment) :
    Nat → List Workspace.ModuleId → List Workspace.ModuleId
  | 0, seen => seen
  | fuel + 1, seen =>
      let edges (id : Workspace.ModuleId) : List Workspace.ModuleId :=
        match environment.modules.find? fun module => decide (module.id = id) with
        | some module => programModuleReferences environment module
        | none => []
      let added := ((seen.flatMap edges).filter fun id => !seen.contains id).eraseDups
      if added.isEmpty then seen else reachableFrom environment fuel (seen ++ added)

/-- The modules reachable from `entry` through the modules that imports and re-exports name, as
upstream's `reachable_modules` walks them. Upstream validates only these. -/
def reachableProgramModules (environment : ProgramEnvironment) (entry : Workspace.ModuleId) :
    List Workspace.ModuleId :=
  reachableFrom environment (environment.modules.length + 1) [entry]

/-- Whether an import names upstream's `std.opcodes` where no module of the program resolves. -/
def isStandardOpcodesImport (environment : ProgramEnvironment) (owner : Workspace.ModuleId)
    (declaration : Syntax.ImportDecl) : Bool :=
  isStandardOpcodesPath (importPath declaration) &&
    (resolveProgramModulePath? environment owner (importPath declaration)).isNone

/-- The names a selected or wildcard import of upstream's `std.opcodes` binds, each with the
function it denotes: its selected functions under their aliases, or all of them, less the hidden
ones. A name it does not export binds nothing (`standardOpcodeImportErrors`). -/
def standardOpcodeBindings (declaration : Syntax.ImportDecl) : List (String × String) :=
  match declaration.value with
  | .selected selection _ hidingClause =>
      let hidden := hiddenNames hidingClause
      selection.elements.toList.filterMap fun item =>
        let source := selectorSpelling item.value.source
        let localName := item.value.alias.map (·.value) |>.getD source
        if standardOpcodeNames.contains source &&
            !(hidden.contains source || hidden.contains localName) then
          some (localName, source)
        else none
  | .wildcard _ hidingClause =>
      let hidden := hiddenNames hidingClause
      standardOpcodeNames.filterMap fun name =>
        if hidden.contains name then none else some (name, name)
  | _ => []

/-- The names that one of upstream's std modules other than `std.opcodes` exports, with their
namespaces (`upstreamStandardModuleExports`), where an import names it and no module of the program
resolves at its path. Lean has none of its declarations. -/
def standardModuleImportExports? (environment : ProgramEnvironment) (owner : Workspace.ModuleId)
    (declaration : Syntax.ImportDecl) : Option (List (String × StandardExportNamespace)) :=
  let path := importPath declaration
  if path.value.externalMarker.isNone &&
      (resolveProgramModulePath? environment owner path).isNone then
    (upstreamStandardModuleExports.find? (·.1 == programModulePathComponents path)).map (·.2)
  else none

/-- The identity that stands for one of upstream's std modules: the standard library's module at
the path `std.X` and `std` resolve to (`X`, and `std`), as `standardOpcodesModule` stands for
`std.opcodes`. -/
def standardModuleId? (components : List String) : Option Workspace.ModuleId := do
  let logical := match components with
    | ["std"] => ["std"]
    | "std" :: rest => rest
    | other => other
  match ← logical.mapM Workspace.PathSegment.parse with
  | [] => none
  | first :: rest => some ⟨.standard, ⟨first :: rest, List.cons_ne_nil first rest⟩⟩

/-- The declaration namespace of a std export, whose import group `SC0108` compares. -/
def StandardExportNamespace.declarationNamespace :
    StandardExportNamespace → ProgramDeclarationNamespace
  | .function => .value
  | .type => .type
  | .trait => .trait

/-- The names a selected or wildcard import of one of upstream's std modules other than
`std.opcodes` binds, each with its namespace: its selected names under their aliases, or all of
them, less the hidden ones. A name it does not export, a constructor among them, binds nothing
(`standardModuleImportErrors`). The names take no part in name lookups: Lean has none of their
declarations, so a name is refused where it is used. -/
def standardModuleBindings (exports : List (String × StandardExportNamespace))
    (declaration : Syntax.ImportDecl) : List (String × StandardExportNamespace) :=
  match declaration.value with
  | .selected selection _ hidingClause =>
      let hidden := hiddenNames hidingClause
      selection.elements.toList.flatMap fun item =>
        let source := selectorSpelling item.value.source
        let localName := item.value.alias.map (·.value) |>.getD source
        if hidden.contains source || hidden.contains localName then []
        else (exports.filter (·.1 == source)).map fun entry => (localName, entry.2)
  | .wildcard _ hidingClause =>
      let hidden := hiddenNames hidingClause
      exports.filter fun entry => !hidden.contains entry.1
  | _ => []

/-- A module's imports of std's other modules, each with the module's exports and identity. -/
private def standardModuleImports (environment : ProgramEnvironment) (module : ProgramModule) :
    List (Syntax.ImportDecl × List (String × StandardExportNamespace) × Workspace.ModuleId) :=
  (importsIn module).filterMap fun declaration => do
    let exports ← standardModuleImportExports? environment module.id declaration
    let target ← standardModuleId? (programModulePathComponents (importPath declaration))
    pure (declaration, exports, target)

/-- The names a module's imports of upstream's `std.opcodes` bind. -/
private def standardOpcodeNamesBound (environment : ProgramEnvironment) (module : ProgramModule) :
    List String :=
  (importsIn module).flatMap fun declaration =>
    if isStandardOpcodesImport environment module.id declaration then
      (standardOpcodeBindings declaration).map (·.1)
    else []

/-- Upstream's `SC0110` and `SC0108` for an import of `std.opcodes`: a selected or hidden name
it does not export, and a name it binds beside a value the module declares. -/
private def standardOpcodeImportErrors (environment : ProgramEnvironment) (module : ProgramModule) :
    List ProgramInterfaceError :=
  let unknown (name : String) : Option ProgramInterfaceError :=
    if standardOpcodeNames.contains name then none
    else some (.unknownImportName module.id standardOpcodesModule name)
  let unknownNames := (importsIn module).flatMap fun declaration =>
    if isStandardOpcodesImport environment module.id declaration then
      match declaration.value with
      | .selected selection _ hidingClause =>
          (selection.elements.toList.filterMap fun item =>
            unknown (selectorSpelling item.value.source)) ++ (hiddenNames hidingClause).filterMap unknown
      | .wildcard _ hidingClause => (hiddenNames hidingClause).filterMap unknown
      | _ => []
    else []
  let declared := (environment.declarationsIn module.id).filterMap fun declaration =>
    if declaration.nameSpace == some .value then declaration.name else none
  unknownNames ++ ((standardOpcodeNamesBound environment module).eraseDups.filter
    declared.contains).map (.importedNameConflict module.id .value ·)

/-- Upstream's `SC0110` and `SC0108` for an import of one of upstream's std modules other than
`std.opcodes`: a selected or hidden name it does not export, a constructor among them, and a
name it binds beside a declaration of the module in the same import group, once per group and
name, as `importConflicts` compares a user module's. -/
private def standardModuleImportErrors (environment : ProgramEnvironment) (module : ProgramModule)
    (locals : List VisibleEntity) : List ProgramInterfaceError :=
  let rows := standardModuleImports environment module
  let unknownNames := rows.flatMap fun (declaration, exports, target) =>
    let unknown (name : String) : Option ProgramInterfaceError :=
      if exports.any (·.1 == name) then none else some (.unknownImportName module.id target name)
    match declaration.value with
    | .selected selection _ hidingClause =>
        (selection.elements.toList.filterMap fun item =>
          unknown (selectorSpelling item.value.source)) ++ (hiddenNames hidingClause).filterMap unknown
    | .wildcard _ hidingClause => (hiddenNames hidingClause).filterMap unknown
    | _ => []
  let clashes := rows.flatMap fun (declaration, exports, _) =>
    (standardModuleBindings exports declaration).filterMap fun (name, nameSpace) =>
      let group := nameSpace.declarationNamespace.importGroup
      if locals.any fun declared =>
          declared.localName == name && declared.importGroup? == some group then
        some (group, name)
      else none
  let unique := clashes.foldl (fun seen clash =>
    if seen.contains clash then seen else seen ++ [clash]) []
  unknownNames ++ unique.map fun (group, name) => .importedNameConflict module.id group name

/-- Upstream's `SC0117`: a selective import that lists one source name twice or binds one local
name twice, and a hiding clause that hides one name twice, once per name. It reads only the
import, so it holds for a module the load does not resolve too. -/
private def duplicateImportNames (module : ProgramModule) : List ProgramInterfaceError :=
  let repeated (names : List String) : List String :=
    (names.zipIdx.filter fun (name, index) => (names.take index).contains name).map (·.1)
  let names := (importsIn module).flatMap fun declaration =>
    match declaration.value with
    | .selected selection _ hidingClause =>
        let items := selection.elements.toList
        let sources := items.map fun item => selectorSpelling item.value.source
        let locals := items.map fun item =>
          item.value.alias.map (·.value) |>.getD (selectorSpelling item.value.source)
        repeated sources ++ repeated locals ++ repeated (hiddenNames hidingClause)
    | .wildcard _ hidingClause => repeated (hiddenNames hidingClause)
    | _ => []
  names.eraseDups.map (.duplicateImportName module.id ·)

/-- Upstream's `SC0120`: a local name that selected or wildcard imports bring from two or more
modules, in any import group and used or not. Two imports of one module are no ambiguity; a
module counts by the import that names it, so a re-export beside its origin counts as two. -/
private def ambiguousImports (environment : ProgramEnvironment) (interfaces : ProgramInterfaces)
    (module : ProgramModule) : List ProgramInterfaceError :=
  let brought := (importsIn module).flatMap fun declaration =>
    match declaration.value with
    | .wildcard _ _ | .selected _ _ _ =>
        match resolveProgramModulePath? environment module.id (importPath declaration) with
        | none =>
            if isStandardOpcodesPath (importPath declaration) then
              (standardOpcodeBindings declaration).map fun (name, _) => (name, standardOpcodesModule)
            else
              match standardModuleImportExports? environment module.id declaration,
                  standardModuleId? (programModulePathComponents (importPath declaration)) with
              | some exports, some target =>
                  (standardModuleBindings exports declaration).map fun (name, _) => (name, target)
              | _, _ => []
        | some target =>
            (processImport environment interfaces module.id declaration).entities.map
              fun entity => (entity.localName, target)
    | _ => []
  (brought.map (·.1)).eraseDups.filterMap fun name =>
    let targets := ((brought.filter (·.1 == name)).map (·.2)).eraseDups
    if targets.length ≥ 2 then some (.ambiguousImport module.id name targets) else none

/-- The qualifiers a plain or namespace import binds: a namespace import's alias, or a plain
import's last path component and the first component of the path it is seen by, a leading
`lib` and an external library's name dropped. -/
private def importQualifiers (declaration : Syntax.ImportDecl) : List String :=
  match declaration.value with
  | .plain path =>
      let components := programModulePathComponents path
      let seen :=
        if components.length > 1 &&
            (path.value.externalMarker.isSome || components.head? == some "lib") then
          components.drop 1
        else components
      (seen.getLast?.toList ++ seen.head?.toList).eraseDups
  | .namespace _ alias => [alias.value]
  | _ => []

/-- Upstream's `SC0121`: a plain or namespace import's qualifier beside a value of the module of
the same name, declared or brought by a selected or wildcard import. A module counts where the
load resolves it or where it is one of upstream's std modules, whose path alone gives the
qualifier. -/
private def importQualifierConflicts (environment : ProgramEnvironment)
    (interfaces : ProgramInterfaces) (module : ProgramModule) : List ProgramInterfaceError :=
  let qualifiers := (importsIn module).flatMap fun declaration =>
    let path := importPath declaration
    if (resolveProgramModulePath? environment module.id path).isSome ||
        upstreamStandardModulePaths.contains (programModulePathComponents path) then
      importQualifiers declaration
    else []
  let values := ((environment.declarationsIn module.id).filterMap fun declaration =>
      if declaration.nameSpace == some .value then declaration.name else none) ++
    ((importsIn module).flatMap fun declaration =>
      (processImport environment interfaces module.id declaration).entities.filterMap
        fun entity =>
          if entity.declaration.nameSpace == some .value then some entity.localName else none) ++
    standardOpcodeNamesBound environment module ++
    (standardModuleImports environment module).flatMap fun (declaration, exports, _) =>
      (standardModuleBindings exports declaration).filterMap fun (name, nameSpace) =>
        if nameSpace == .function then some name else none
  (qualifiers.eraseDups.filter values.contains).map (.importQualifierConflict module.id ·)

/-- The import rules a load checks in each module, as upstream's validation does: a name brought
beside a declaration (`SC0108`), a name listed twice (`SC0117`), a name from two modules
(`SC0120`) and a qualifier beside a value (`SC0121`). -/
private def importRuleErrors (environment : ProgramEnvironment) (interfaces : ProgramInterfaces)
    (module : ProgramModule) : List ProgramInterfaceError :=
  importConflicts environment interfaces module (localEntities environment module.id) ++
    standardOpcodeImportErrors environment module ++
    standardModuleImportErrors environment module (localEntities environment module.id) ++
    duplicateImportNames module ++
    ambiguousImports environment interfaces module ++
    importQualifierConflicts environment interfaces module

/-- The import errors of a program that its load reports, for the modules reachable from its
entry, as upstream validates only those: the interface errors reported where the import is, in
`buildProgramInterfaces`' order, then each module's import rules. -/
def programImportErrors (environment : ProgramEnvironment) (entry : Workspace.ModuleId) :
    List ProgramInterfaceError :=
  let reachable := reachableProgramModules environment entry
  match programInterfacesWithErrors environment with
  | .error _ => []
  | .ok (interfaces, errors) =>
      errors.filter (fun error =>
          error.reportedAtLoad && error.owner?.any reachable.contains) ++
        (environment.modules.filter fun module => reachable.contains module.id).flatMap
          (importRuleErrors environment interfaces)

/-- Parse and catalog an already validated workspace, and refuse the imports upstream refuses
where they are. -/
def loadValidatedProgram
    (workspace : Workspace.ValidatedUserWorkspace) :
    Except (List ProgramLoadError) LoadedProgram :=
  let (parseErrors, sources) := parseWorkspaceFiles workspace.files
  if parseErrors.isEmpty then
    match buildProgramEnvironment sources with
    | .ok environment =>
        match programImportErrors environment workspace.entry.toModuleId with
        | [] => .ok { workspace, sources, environment }
        | errors => .error [.imports errors]
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
            cases importErrors : programImportErrors environment workspace.entry.toModuleId with
            | nil =>
                simp only [environmentResult, importErrors, Except.ok.injEq] at success
                subst loaded
                exact environmentResult
            | cons error rest =>
                simp [environmentResult, importErrors] at success
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
