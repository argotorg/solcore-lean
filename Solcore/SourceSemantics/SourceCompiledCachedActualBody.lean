import Solcore.SourceSemantics.SourceCompiledCachedMethodValidity

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
