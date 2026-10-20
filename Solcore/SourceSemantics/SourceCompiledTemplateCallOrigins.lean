import Solcore.Frontend.SourceInference.ClassifiedCallInference
import Solcore.SourceSemantics.SourceInferenceDirectCallInitializerOrigins
import Solcore.SourceSemantics.SourceCompiledSelectedFinalization

/-! Every finalized classified template in an actually checked selected body
retains its original declaration-call emitter. This removes the direct-ID
membership premise from the selected-row endpoint. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledTemplateCallOrigins
open Frontend SourceInference TypeSystem SourceInferenceSoundness
open SourceCompiledLocalFinalization DirectCallEvents

namespace BodyReceipt
variable {environment : ProgramEnvironment} {signatures : ProgramSignatures}
  {signature : ProgramFunctionSignature} {fuel : Nat} {checked : CheckedFunction}

theorem classified (receipt : BodyReceipt environment signatures signature fuel checked) :
    ClassifiedCallEvents.Classified receipt.returned :=
  ClassifiedCallEvents.Progress.unify receipt.unified
    (ClassifiedCallEvents.initializedStatements_classified receipt.inferred)

theorem direct_origins (receipt : BodyReceipt environment signatures signature fuel checked) :
    Origins receipt.returned :=
  Progress.unify receipt.unified (initializedStatements_origins receipt.inferred)

theorem finalized_template_direct
    (receipt : BodyReceipt environment signatures signature fuel checked)
    {id : RequirementId} (member : id ∈ sourceLocalSchemeTemplateIds receipt.finalized.typedSource) :
    id ∈ receipt.returned.directCallRequirements :=
  classified receipt ((finalize_templateIdsAligned_validated receipt.finalization id).mp member)

theorem finalized_template_emitter
    (receipt : BodyReceipt environment signatures signature fuel checked)
    {id : RequirementId} (member : id ∈ sourceLocalSchemeTemplateIds receipt.finalized.typedSource) :
    HasCall receipt.finalized.typedSource.nodes id := by
  have emitter := direct_origins receipt id (finalized_template_direct receipt member)
  rw [receipt.resources.source_eq]
  exact SourceCompiledDirectCallOrigins.solved_call emitter receipt.finalized.substitution

end BodyReceipt

/-- The same actual selected receipt supplies all source-template emitters,
including templates owned by nested local binders. -/
theorem selected_template_emitter
    {compiled : SourceCoreCompiler.Compiled} {row : SourceSpecialization.SpecializedFunction} {fuel : Nat}
    (selected : Selected compiled row fuel) {id : RequirementId}
    (member : id ∈ sourceLocalSchemeTemplateIds row.function.typedBody) :
    HasCall row.function.typedBody.nodes id := by
  rw [selected.source] at member ⊢
  have original : id ∈ sourceLocalSchemeTemplateIds selected.body.finalized.typedSource := by
    change id ∈ sourceLocalSchemeTemplateIds (StructuralSubstitution.applyTypedSource row.parameterSubstitution selected.body.finalized.typedSource) at member
    simpa only [StructuralSubstitution.sourceLocalSchemeTemplateIds_applyTypedSource] using member
  exact SourceCompiledDirectCallOrigins.specialized_call
    (BodyReceipt.finalized_template_emitter selected.body original) row.parameterSubstitution

/-- Raw public compilation itself supplies the checked body and provenance;
there is no direct-ID, body-typing, or ownership premise. -/
theorem compile_template_emitters
    {raw : Workspace.RawWorkspace} {seeds : List SourceCoreCompiler.Seed}
    {options : SourceCoreCompiler.Options} {compiled : SourceCoreCompiler.Compiled}
    (accepted : SourceCoreCompiler.compile raw seeds options = .ok compiled)
    {row : SourceSpecialization.SpecializedFunction} (member : row ∈ compiled.plan.specializations) :
    ∀ id ∈ sourceLocalSchemeTemplateIds row.function.typedBody,
      HasCall row.function.typedBody.nodes id := by
  obtain ⟨selected⟩ := SourceCompiledLocalFinalization.of_compile accepted member
  exact fun _ present => selected_template_emitter selected present

end Solcore.SourceSemantics.SourceCompiledTemplateCallOrigins
