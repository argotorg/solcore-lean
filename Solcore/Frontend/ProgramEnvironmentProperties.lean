import Solcore.Frontend.ProgramEnvironment

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
