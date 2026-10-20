import Solcore.SourceSemantics.SourceCompiledGeneralizedFunctionValidity
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationBodyTyping

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
        (checkingContext selected).signatures selected.body.finalized.solvedRequirements
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
