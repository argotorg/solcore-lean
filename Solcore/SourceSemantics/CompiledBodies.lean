import Solcore.SourceSemantics.Internal.Compiled.BodyAssembly
import Solcore.SourceSemantics.CoreLowering.Internal.Selected.CatalogOrigins
import Solcore.SourceSemantics.Internal.Compiled.BodySelection
import Solcore.SourceSemantics.Internal.Compiled.Barriers

/-!
# Validity of compiled bodies

The top of the compiled route. `SourceCompiledActualInitializerBarriers.compile_cached_bodies` says
that a successful public compilation gives validity of every original cached body, including
ordinary functions discovered late and implementation methods. It combines
`SourceCompiledActualInitializerBarriers.cached_actual_initializer_barriers`, which discharges the
initializer barriers from actual checked call paths, with
`SourceCompiledGeneralizedSoundness.compile_cached_bodies_of_actual_barriers`.
-/

section
-- leanmerge: from Solcore.SourceSemantics.SourceCompiledCachedOrdinaryBody
/-! The actual public compiler cache supplies the original ordinary checker
receipt, including functions discovered during executable preparation. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledGeneralizedSoundness
open Frontend SourceInference TypeSystem SourceInferenceSoundness
open SourceCompiledLocalFinalization
open CoreLowering.SelectedCompilationBodyTyping

variable {raw : Workspace.RawWorkspace} {fuel : Nat}
  {compiled : SourceCoreCompiler.Compiled}
  {cached : SourceCoreUnifiedCompilation.Compiled}

/-- Each actual cached ordinary definition retains the original whole body
and receives executable interfaces from that same cache position. -/
theorem cached_ordinary_receipt
    (artifact : compiled.artifact? = some cached)
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    {original : CheckedFunction} (origin : OrdinarySource cached original) :
    ∃ (row : SourceSpecialization.SpecializedFunction)
      (selected : Selected compiled row fuel),
      selected.original = original ∧
      (∃ (index : Nat) (named : SourceCoreGeneralFunctions.Function),
        cached.indexed.base.functions[index]? = some named ∧ named.specialized = row) ∧
      ExecutableCoercionInterfaces.SourceInterfaces
        (checkingContext selected.toBodySelection).signatures selected.body.finalized.solvedRequirements
        selected.body.finalized.typedSource := by
  obtain ⟨index, named, signature, supplied, position, _signatureMember, member, specialized⟩ := origin
  have programEq := (compiled.artifact_fields artifact).1
  have originalMember : original ∈ compiled.program.functions := by
    simpa only [programEq] using member
  obtain ⟨bodySignature, signatureMember, accepted⟩ :=
    Frontend.checkProgram_success_function_body checked originalMember
  obtain ⟨body⟩ := BodyReceipt.of_check accepted
  let selected : Selected compiled named.specialized fuel := {
    original
    originalMember
    signature := bodySignature
    signatureMember
    body
    specialized := (CoreLowering.CallableCoercionBodyProvenance.specialization_fields specialized).1 }
  have interfaces := CoreLowering.SelectedCompilationCoercionInterfaces.cached cached position
  rw [(CoreLowering.CallableCoercionBodyProvenance.specialization_fields specialized).1] at interfaces
  have originalInterfaces := CoreLowering.SelectedCompilationCoercionInterfaces.of_applied interfaces
  refine ⟨named.specialized, selected, rfl, ⟨index, named, position, rfl⟩, ?_⟩
  change ExecutableCoercionInterfaces.SourceInterfaces compiled.program.signatures
    body.finalized.solvedRequirements body.finalized.typedSource
  rw [← body.source, ← body.solved]
  simpa only [programEq, ExecutableCoercionInterfaces.BodyInterfaces] using originalInterfaces

/-- The remaining generalization obligation ranges over the actual completed
cache. It does not require a row to belong to the initial worklist frontier. -/
def CachedOrdinaryInitializerBarriers
    (compiled : SourceCoreCompiler.Compiled)
    (cached : SourceCoreUnifiedCompilation.Compiled) (fuel : Nat) : Prop :=
  ∀ {row : SourceSpecialization.SpecializedFunction}
    (selected : Selected compiled row fuel),
    (∃ (index : Nat) (named : SourceCoreGeneralFunctions.Function),
      cached.indexed.base.functions[index]? = some named ∧ named.specialized = row) →
    SelectedInitializerBarriers selected

/-- Complete original ordinary-body validity for every retained cache row.
Actual initialization, executable interfaces and recursive typing are derived
inside the proof; only the exact initializer barriers remain to be supplied. -/
theorem cached_ordinary_valid_of_barriers
    (artifact : compiled.artifact? = some cached)
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    (barriers : CachedOrdinaryInitializerBarriers compiled cached fuel)
    {original : CheckedFunction} (origin : OrdinarySource cached original) :
    FunctionDefinition.Valid cached.sourceProgram.signatures
      (FunctionDefinition.ofChecked original) := by
  obtain ⟨row, selected, same, position, interfaces⟩ :=
    cached_ordinary_receipt artifact checked origin
  have valid := function_valid_of_barriers_of_interfaces selected checked interfaces
    (barriers selected position)
  simpa only [same, (compiled.artifact_fields artifact).1] using valid

/-- The public compiler's actual artifact supplies all ordinary selected-body
judgments, including later discovered helpers, under their exact barriers. -/
theorem compile_cached_ordinary_valid_of_barriers
    {seeds : List SourceCoreCompiler.Seed} {options : SourceCoreCompiler.Options}
    (accepted : SourceCoreCompiler.compile raw seeds options = .ok compiled)
    (artifact : compiled.artifact? = some cached)
    (barriers : CachedOrdinaryInitializerBarriers compiled cached options.checkingFuel) :
    ∀ original, OrdinarySource cached original →
      FunctionDefinition.Valid cached.sourceProgram.signatures
        (FunctionDefinition.ofChecked original) := by
  intro original origin
  exact cached_ordinary_valid_of_barriers artifact
    (SourceCoreCompiler.compile_checked_source accepted) barriers origin

end Solcore.SourceSemantics.SourceCompiledGeneralizedSoundness
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceCompiledCachedMethodValidity
/-! The same recursive body proof serves actual ordinary and implementation
method cache rows. Only their concrete initializer barriers remain inputs. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledMethodFinalization
open Frontend SourceInference TypeSystem SourceInferenceSoundness
open SourceCompiledLocalFinalization SourceCompiledGeneralizedSoundness

theorem MethodBodyReceipt.valid_of_body
    {raw : Workspace.RawWorkspace} {program : CheckedProgram}
    {retained : CheckedImplementationMethod} {fuel : Nat}
    (receipt : MethodBodyReceipt program retained fuel)
    (checked : Frontend.checkProgram raw fuel = .ok program)
    (typed : CheckedBodyHasType program.signatures receipt.signature retained.checked) :
    MethodDefinition.Valid program.signatures (MethodDefinition.ofChecked retained) := by
  let catalog := SignatureCatalogWellFormed.ofCheckProgram checked
  have implementation := catalog.implementations_semantic receipt.implementation receipt.implementationMember
  have method := implementation.methods receipt.method receipt.methodMember
  obtain ⟨trait, traitMethod, traitMember, head, traitMethodMember, traitMethodId,
    _, _, _, _, _, _⟩ := method.trait_method
  have actual := receipt.trait_origin checked
  have traitId : trait.id = receipt.trait.id := by
    have same := head.symm.trans actual.2
    injection same
  have same := Frontend.trait_signature_eq_of_mem_of_id_eq
    catalog.trait_ids traitMember actual.1 traitId
  subst trait
  have traitMethodFormed := (catalog.traits_semantic receipt.trait actual.1).methods
    traitMethod traitMethodMember
  have header := receipt.header checked
  obtain ⟨facts, bodyTyping, factsType⟩ := typed
  have bodyValid := bodyDefinitionHasType_ofCheckFunctionBody header
    (receipt.predicates_fixed checked retained.checked.substitution) receipt.body.accepted bodyTyping factsType
  refine .intro (facts := facts) receipt.implementationMember receipt.methodMember receipt.methodId
    method.owner actual.1 traitMethodMember ?_ ?_ ?_ ?_
  · exact traitMethodId.symm
  · exact traitMethodFormed.owner
  · simpa [MethodDefinition.ofChecked, BodyDefinition.ofChecked, MethodBodyReceipt.signature,
      ProgramImplementationSignature.functionSignatureOfMethodWithTrait,
      ProgramImplementationSignature.functionSignatureOfMethod] using header.declaration_eq
  · simpa [MethodDefinition.ofChecked, MethodBodyReceipt.signature,
      ProgramImplementationSignature.functionSignatureOfMethodWithTrait,
      ProgramImplementationSignature.functionSignatureOfMethod,
      ProgramFunctionSignature.parameterNames, ProgramFunctionSignature.parameterTypes,
      ProgramFunctionSignature.parameterComptime, ProgramImplMethodSignature.parameterNames,
      ProgramImplMethodSignature.parameterTypes, ProgramImplMethodSignature.parameterComptime,
      methodAssumptions] using bodyValid

end Solcore.SourceSemantics.SourceCompiledMethodFinalization

namespace Solcore.SourceSemantics.SourceCompiledGeneralizedSoundness
open Frontend SourceInference TypeSystem SourceInferenceSoundness
open SourceCompiledLocalFinalization SourceCompiledMethodFinalization
open CoreLowering.SelectedCompilationBodyTyping

def CachedBodyInitializerBarriers
    (compiled : SourceCoreCompiler.Compiled) (cached : SourceCoreCompiler.Cached) (fuel : Nat) : Prop :=
  ∀ {row : SourceSpecialization.SpecializedFunction}
    (selected : BodySelection compiled row fuel),
    (∃ (index : Nat) (named : SourceCoreGeneralFunctions.Function),
      cached.indexed.base.functions[index]? = some named ∧ named.specialized = row) →
    BodyInitializerBarriers selected

theorem cached_method_valid_of_barriers
    {raw : Workspace.RawWorkspace} {fuel : Nat}
    {compiled : SourceCoreCompiler.Compiled} {cached : SourceCoreCompiler.Cached}
    (artifact : compiled.artifact? = some cached)
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    (barriers : CachedBodyInitializerBarriers compiled cached fuel)
    {retained : CheckedImplementationMethod} (origin : MethodSource cached retained) :
    MethodDefinition.Valid cached.sourceProgram.signatures (MethodDefinition.ofChecked retained) := by
  obtain ⟨actual⟩ := cached_method_body checked artifact origin
  obtain ⟨row, selected, originalEq, signatureEq, _sameReceipt, position, interfaces⟩ := actual.bodySelection
  have typed := checked_body_of_barriers_of_interfaces selected checked interfaces (barriers selected position)
  have originalTyped : CheckedBodyHasType compiled.program.signatures actual.receipt.signature retained.checked := by
    simpa only [originalEq, signatureEq] using typed
  have valid := actual.receipt.valid_of_body checked originalTyped
  simpa only [(compiled.artifact_fields artifact).1] using valid

/-- Raw compiler success supplies both original ordinary and method judgments
for the actual complete cache, including rows added during preparation. -/
theorem compile_cached_bodies_of_barriers
    {raw : Workspace.RawWorkspace} {seeds : List SourceCoreCompiler.Seed}
    {options : SourceCoreCompiler.Options} {compiled : SourceCoreCompiler.Compiled}
    {cached : SourceCoreCompiler.Cached}
    (accepted : SourceCoreCompiler.compile raw seeds options = .ok compiled)
    (artifact : compiled.artifact? = some cached)
    (barriers : CachedBodyInitializerBarriers compiled cached options.checkingFuel) :
    CoreLowering.SelectedCompilationBodyTyping.Bodies cached := by
  have checked := SourceCoreCompiler.compile_checked_source accepted
  have actualChecked : Frontend.checkProgram raw options.checkingFuel = .ok cached.sourceProgram := by
    simpa only [(compiled.artifact_fields artifact).1] using checked
  let catalog := SignatureCatalogWellFormed.ofCheckProgram actualChecked
  obtain ⟨functionIds, methodIds⟩ := Frontend.checkProgram_success_ids actualChecked
  refine ⟨catalog, ?_, ?_, ?_, ?_⟩
  · simp only [Program.ofChecked, List.map_map, Function.comp_def,
      FunctionDefinition.ofChecked, BodyDefinition.ofChecked]
    rw [functionIds]
    exact catalog.function_ids
  · simp only [Program.ofChecked, List.map_map, Function.comp_def, MethodDefinition.ofChecked]
    rw [methodIds]
    exact catalog.implementation_method_ids
  · intro original origin
    exact cached_ordinary_valid_of_barriers artifact checked
      (fun selected position => barriers selected.toBodySelection position) origin
  · intro retained origin
    exact cached_method_valid_of_barriers artifact checked barriers origin

end Solcore.SourceSemantics.SourceCompiledGeneralizedSoundness
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceCompiledCachedActualBody
/-! Actual-call initializer barriers connect the shared checker assembly to
all cached ordinary and method bodies, including later discovered rows. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledGeneralizedSoundness
open Frontend SourceInference TypeSystem SourceInferenceSoundness
open SourceCompiledLocalFinalization SourceCompiledMethodFinalization
open CoreLowering.SelectedCompilationBodyTyping

def CachedActualBodyInitializerBarriers
    (compiled : SourceCoreCompiler.Compiled) (cached : SourceCoreCompiler.Cached) (fuel : Nat) : Prop :=
  ∀ {row : SourceSpecialization.SpecializedFunction}
    (selected : BodySelection compiled row fuel),
    (∃ (index : Nat) (named : SourceCoreGeneralFunctions.Function),
      cached.indexed.base.functions[index]? = some named ∧ named.specialized = row) →
    BodyInitializerBarriersFor selected.InferenceCall selected

theorem function_valid_of_actual_barriers_of_interfaces
    {raw : Workspace.RawWorkspace} {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel : Nat}
    (selected : Selected compiled row fuel)
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    (interfaces : ExecutableCoercionInterfaces.SourceInterfaces
      (checkingContext selected.toBodySelection).signatures selected.body.finalized.solvedRequirements
      selected.body.finalized.typedSource)
    (barriers : BodyInitializerBarriersFor selected.toBodySelection.InferenceCall selected.toBodySelection) :
    FunctionDefinition.Valid compiled.program.signatures
      (FunctionDefinition.ofChecked selected.original) := by
  apply functionDefinitionValid_ofCheckProgram checked selected.originalMember
  intro signature signatureMember bodySuccess
  have same : signature = selected.signature :=
    eq_of_mem_of_nodup_map (SignatureCatalogWellFormed.ofCheckProgram checked).function_ids
      signatureMember selected.signatureMember
      ((checkFunctionBody_success_declaration bodySuccess).symm.trans
        (checkFunctionBody_success_declaration selected.body.accepted))
  subst signature
  exact checked_body_of_actual_barriers_of_interfaces selected.toBodySelection checked interfaces barriers

theorem cached_ordinary_valid_of_actual_barriers
    {raw : Workspace.RawWorkspace} {fuel : Nat}
    {compiled : SourceCoreCompiler.Compiled} {cached : SourceCoreCompiler.Cached}
    (artifact : compiled.artifact? = some cached)
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    (barriers : CachedActualBodyInitializerBarriers compiled cached fuel)
    {original : CheckedFunction} (origin : OrdinarySource cached original) :
    FunctionDefinition.Valid cached.sourceProgram.signatures (FunctionDefinition.ofChecked original) := by
  obtain ⟨row, selected, same, position, interfaces⟩ := cached_ordinary_receipt artifact checked origin
  have valid := function_valid_of_actual_barriers_of_interfaces selected checked interfaces
    (barriers selected.toBodySelection position)
  simpa only [same, (compiled.artifact_fields artifact).1] using valid

theorem cached_method_valid_of_actual_barriers
    {raw : Workspace.RawWorkspace} {fuel : Nat}
    {compiled : SourceCoreCompiler.Compiled} {cached : SourceCoreCompiler.Cached}
    (artifact : compiled.artifact? = some cached)
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    (barriers : CachedActualBodyInitializerBarriers compiled cached fuel)
    {retained : CheckedImplementationMethod} (origin : MethodSource cached retained) :
    MethodDefinition.Valid cached.sourceProgram.signatures (MethodDefinition.ofChecked retained) := by
  obtain ⟨actual⟩ := cached_method_body checked artifact origin
  obtain ⟨row, selected, originalEq, signatureEq, _sameReceipt, position, interfaces⟩ := actual.bodySelection
  have typed := checked_body_of_actual_barriers_of_interfaces selected checked interfaces (barriers selected position)
  have originalTyped : CheckedBodyHasType compiled.program.signatures actual.receipt.signature retained.checked := by
    simpa only [originalEq, signatureEq] using typed
  have valid := actual.receipt.valid_of_body checked originalTyped
  simpa only [(compiled.artifact_fields artifact).1] using valid

theorem compile_cached_bodies_of_actual_barriers
    {raw : Workspace.RawWorkspace} {seeds : List SourceCoreCompiler.Seed}
    {options : SourceCoreCompiler.Options} {compiled : SourceCoreCompiler.Compiled}
    {cached : SourceCoreCompiler.Cached}
    (accepted : SourceCoreCompiler.compile raw seeds options = .ok compiled)
    (artifact : compiled.artifact? = some cached)
    (barriers : CachedActualBodyInitializerBarriers compiled cached options.checkingFuel) :
    CoreLowering.SelectedCompilationBodyTyping.Bodies cached := by
  have checked := SourceCoreCompiler.compile_checked_source accepted
  have actualChecked : Frontend.checkProgram raw options.checkingFuel = .ok cached.sourceProgram := by
    simpa only [(compiled.artifact_fields artifact).1] using checked
  let catalog := SignatureCatalogWellFormed.ofCheckProgram actualChecked
  obtain ⟨functionIds, methodIds⟩ := Frontend.checkProgram_success_ids actualChecked
  refine ⟨catalog, ?_, ?_, ?_, ?_⟩
  · simp only [Program.ofChecked, List.map_map, Function.comp_def,
      FunctionDefinition.ofChecked, BodyDefinition.ofChecked]
    rw [functionIds]
    exact catalog.function_ids
  · simp only [Program.ofChecked, List.map_map, Function.comp_def, MethodDefinition.ofChecked]
    rw [methodIds]
    exact catalog.implementation_method_ids
  · intro original origin
    exact cached_ordinary_valid_of_actual_barriers artifact checked barriers origin
  · intro retained origin
    exact cached_method_valid_of_actual_barriers artifact checked barriers origin

end Solcore.SourceSemantics.SourceCompiledGeneralizedSoundness
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceCompiledActualInitializerBarriers
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
end
