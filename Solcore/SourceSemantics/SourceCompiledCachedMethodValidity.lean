import Solcore.SourceSemantics.SourceCompiledCachedBodySelection
import Solcore.SourceSemantics.SourceCompiledCachedOrdinaryBody

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
