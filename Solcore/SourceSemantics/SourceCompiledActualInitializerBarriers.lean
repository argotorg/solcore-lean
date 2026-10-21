import Solcore.SourceSemantics.SourceBodyGeneralizationBarrierConnection
import Solcore.SourceSemantics.SourceCompiledReachableInitializerLifetime
import Solcore.SourceSemantics.SourceCompiledActualQuantifierSeparation
import Solcore.SourceSemantics.SourceCompiledCachedActualBody

/-! Actual checked call paths discharge the initializer barriers for every
cached ordinary or method body. Original body typing is then obtained from
the shared checker assembly without a separate generalization assumption. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledActualInitializerBarriers
open Frontend SourceInference TypeSystem SourceInferenceSoundness ProtectedVariables
open SourceCompiledLocalFinalization SourceCompiledGeneralizedSoundness
open SourceBodyGeneralizationBarrierConnection

private theorem item_binders (item : ForItemForm) :
    item.initializedLetBinders = (forItemInitializedLetBindings item).map (·.binder) := by
  cases item <;> try rfl
  rename_i binder initializer
  cases initializer <;> rfl

private theorem statement_binders (form : StatementForm) :
    form.initializedLetBinders = (statementInitializedLetBindings form).map (·.binder) := by
  cases form <;> try rfl
  · rename_i binder initializer
    cases initializer <;> rfl
  · simp only [StatementForm.initializedLetBinders, statementInitializedLetBindings,
      List.map_append, List.map_flatMap, ← item_binders]

private theorem source_binders (source : TypedSource) :
    source.initializedLetBinders = (initializedLetBindings source).map (·.binder) := by
  simp only [TypedSource.initializedLetBinders, initializedLetBindings, List.map_flatMap]
  apply congrArg (fun f : Node → List TypedBinder => source.nodes.flatMap f)
  funext node
  cases node with
  | expression node => rfl
  | statement node => exact statement_binders node.form

private theorem flatMap_sublist {α β : Type} (values : List α) (f g : α → List β)
    (each : ∀ value, List.Sublist (f value) (g value)) : List.Sublist (values.flatMap f) (values.flatMap g) := by
  induction values with
  | nil => exact .refl _
  | cons head rest ih => exact (each head).append ih

private theorem forItem_ids (item : ForItemForm) :
    List.Sublist ((forItemInitializedLetBindings item).map fun binding => binding.binder.id)
      (forItemDefinedLocalIds item) := by
  cases item <;> try exact .refl _
  rename_i binder initializer
  cases initializer <;> simp [forItemInitializedLetBindings, forItemDefinedLocalIds]

private theorem form_ids (form : StatementForm) :
    List.Sublist ((statementInitializedLetBindings form).map fun binding => binding.binder.id)
      (statementDefinedLocalIds form) := by
  cases form <;> try exact List.nil_sublist _
  case letDecl binder initializer =>
    cases initializer <;> simp [statementInitializedLetBindings, statementDefinedLocalIds]
  case forLoop initial condition post body =>
    simp only [statementInitializedLetBindings, statementDefinedLocalIds, List.map_append, List.map_flatMap]
    exact (flatMap_sublist initial _ _ forItem_ids).append (flatMap_sublist post _ _ forItem_ids)

private theorem initialized_ids (source : TypedSource) :
    List.Sublist ((initializedLetBindings source).map fun binding => binding.binder.id)
      (definedLocalIds source) := by
  unfold initializedLetBindings definedLocalIds
  rw [List.map_flatMap]
  apply List.sublist_append_of_sublist_right
  apply flatMap_sublist
  intro node
  cases node with
  | expression node => exact List.nil_sublist _
  | statement node => exact form_ids node.form

/-- The raw header binder and finalized containment identify the same complete
binding. Unique declaration identities also recover its original initializer. -/
theorem header_binding_retained
    {compiled : SourceCoreCompiler.Compiled} {row : SourceSpecialization.SpecializedFunction}
    {fuel : Nat} {selected : BodySelection compiled row fuel}
    {childFuel : Nat} {context : SourceInference.Context} {source : Syntax.ForItem}
    {expectedReturn : Ty} {initial final : State} {inferred : ForItemForm}
    {frames : List InitializedLetBinding} {target : SourceSemantics.Context}
    (boundary : ForItemBoundary selected (childFuel + 1) context source expectedReturn
      initial inferred final frames target)
    (receipt : LocalHeaderRequirementTiming.Receipt childFuel context source initial (inferred, final)) :
    ({binder := receipt.binding.1, initializer := .expression receipt.value.id} : InitializedLetBinding) ∈
      initializedLetBindings (evidenceSource selected) := by
  let binding : InitializedLetBinding := ⟨receipt.binding.1, .expression receipt.value.id⟩
  have member : binding ∈ forItemInitializedLetBindings inferred := by
    have form : inferred = .letDecl receipt.binding.1 (some receipt.value.id) := receipt.recorded
    rw [form]
    exact List.mem_singleton_self _
  have binderMember := (boundary.bindingsRetained binding member).1
  rw [source_binders] at binderMember
  obtain ⟨original, originalMember, binderEq⟩ := List.mem_map.mp binderMember
  have mapped : FlexibleSubstitution.applyInitializedLetBinding selected.body.finalized.substitution original ∈
      initializedLetBindings selected.body.finalized.typedSource := by
    rw [selected.body.resources.source_eq, FlexibleSubstitution.initializedLetBindings_applySubstitution]
    exact List.mem_map.mpr ⟨original, originalMember, rfl⟩
  have finalMember := (boundary.actualBindings binding member).1
  have same := eq_of_mem_of_nodup_map
    ((initialized_ids _).nodup selected.body.resources.local_identity_ownership.unique)
    mapped finalMember (show
      (FlexibleSubstitution.applyInitializedLetBinding selected.body.finalized.substitution original).binder.id =
      (FlexibleSubstitution.applyInitializedLetBinding selected.body.finalized.substitution binding).binder.id from by
        change original.binder.id = binding.binder.id
        exact congrArg TypedBinder.id binderEq)
  have initializerEq : original.initializer = binding.initializer := by
    have actual := congrArg InitializedLetBinding.initializer same
    change original.initializer = binding.initializer at actual
    exact actual
  have originalEq : original = binding := by
    cases original
    cases binderEq
    cases initializerEq
    rfl
  change binding ∈ initializedLetBindings (evidenceSource selected)
  rw [← originalEq]
  exact originalMember

/-- Both statement and header obligations are derived from the same actual
cached body and its successful checker execution. -/
theorem cached_actual_initializer_barriers
    {raw : Workspace.RawWorkspace} {fuel : Nat}
    {compiled : SourceCoreCompiler.Compiled} {cached : SourceCoreCompiler.Cached}
    (artifact : compiled.artifact? = some cached)
    (checked : checkProgram raw fuel = .ok compiled.program) :
    CachedActualBodyInitializerBarriers compiled cached fuel := by
  intro row selected position
  obtain ⟨index, named, position, rfl⟩ := position
  constructor
  · intro source expectedReturn frames target occurrence here boundary
    have retained : (⟨occurrence.receipt.binding.1,
        .expression occurrence.receipt.value.id⟩ : InitializedLetBinding) ∈
        initializedLetBindings (evidenceSource selected) :=
      List.mem_flatMap.mpr ⟨_, occurrence.recorded, List.mem_singleton_self _⟩
    exact statement_of_lifetime artifact checked position selected occurrence boundary
      (occurrence.actual_lifetime artifact checked position here)
      (selected.initialized_quantifiers_disjoint artifact checked position retained)
  · intro childFuel context source expectedReturn initial final inferred frames target here boundary receipt
    have retained := header_binding_retained boundary receipt
    have binderRetained := selected.headerReceipt_retained here receipt
    obtain ⟨ready, extension, lifetime⟩ :=
      selected.header_lifetime artifact checked position here receipt retained
    exact header_of_lifetime artifact checked position selected boundary receipt ready extension
      retained binderRetained lifetime
      (selected.initialized_quantifiers_disjoint artifact checked position retained)

/-- Public Core compilation supplies validity of every original cached body,
including late discovered ordinary functions and implementation methods. -/
theorem compile_cached_bodies
    {raw : Workspace.RawWorkspace} {seeds : List SourceCoreCompiler.Seed}
    {options : SourceCoreCompiler.Options} {compiled : SourceCoreCompiler.Compiled}
    {cached : SourceCoreCompiler.Cached}
    (accepted : SourceCoreCompiler.compile raw seeds options = .ok compiled)
    (artifact : compiled.artifact? = some cached) :
    CoreLowering.SelectedCompilationBodyTyping.Bodies cached :=
  compile_cached_bodies_of_actual_barriers accepted artifact
    (cached_actual_initializer_barriers artifact (SourceCoreCompiler.compile_checked_source accepted))

end Solcore.SourceSemantics.SourceCompiledActualInitializerBarriers
