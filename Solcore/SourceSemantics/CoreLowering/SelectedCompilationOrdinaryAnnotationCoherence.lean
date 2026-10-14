import Solcore.SourceSemantics.SourceBodyResultAnnotation
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationOrdinaryErasure
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationOrdinaryIdentity
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationBodyTyping

/-!
Ordinary stage coherence follows from the original body's stored result
annotation. Raw replacement types need no separate formation premise: equal
rigid sources already contain every annotation used by that result.
-/
set_option autoImplicit false
set_option Elab.async false

namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationOrdinaryAnnotationCoherence
open Frontend SourceInference TypeSystem CallableAncestryMetadata

/-- Typing is required only for the original definition at this selected owner. -/
def AtOwner (program : CheckedProgram) (owner : Resolved.DeclarationId) : Prop :=
  ∀ generic, generic ∈ program.functions → generic.declaration = owner →
    FunctionDefinition.Valid program.signatures (FunctionDefinition.ofChecked generic)

/-- A real cached preparation identifies the unique original checker body. -/
theorem at_prepared {compiled : SourceCoreUnifiedCompilation.Compiled}
    {row : SourceSpecialization.SpecializedFunction}
    (bodies : SelectedCompilationBodyTyping.Bodies compiled)
    (prepared : RecursiveNamedPublicSpecializationMeaning.Prepared compiled row) :
    AtOwner compiled.sourceProgram row.function.typedBody.owner := by
  obtain ⟨request, signature, generic, signatureMember, genericMember, _resolved, accepted⟩ := prepared.origin
  have valid := bodies.ordinary generic
    ⟨prepared.index, prepared.named, signature, request.parameterSubstitution, prepared.selected,
      signatureMember, genericMember, by simpa only [prepared.same] using accepted⟩
  have unique : (compiled.sourceProgram.functions.map (fun function => function.declaration)).Nodup := by
    simpa only [Program.ofChecked, List.map_map, Function.comp_def,
      FunctionDefinition.ofChecked, BodyDefinition.ofChecked] using bodies.function_ids
  have owner : row.function.typedBody.owner = generic.declaration := by
    rw [(CallableCoercionBodyProvenance.specialization_fields accepted).1]
    exact (RecursiveNamedSpecializationBodyFacts.identities accepted).2.1
  intro candidate member identity
  have same := StructuralSubstitution.eq_of_mem_of_mapped_nodup unique member genericMember
    (identity.trans owner)
  simpa only [same] using valid

private theorem original_body {program : CheckedProgram} {generic : CheckedFunction}
    (valid : FunctionDefinition.Valid program.signatures (FunctionDefinition.ofChecked generic)) :
    ∃ context facts, BodyHasType generic.typedBody context generic.inferredBodyType facts ∧
      facts.type = generic.inferredBodyType := by
  cases valid with
  | intro _ _ typed =>
      cases typed with
      | @intro lexicalContext _ _ _ _ _ resultType _ _ _ _ _ _ _ _ bodyTyped annotation =>
          refine ⟨lexicalContext, _, ?_, annotation.trans resultType.symm⟩
          rw [← resultType] at bodyTyped
          exact bodyTyped

/-- Actual ordinary origins and their equal contextual sources identify the
rigid source, annotated result and original return flag. -/
theorem source_and_result_of_origins {program : CheckedProgram}
    {left right : SourceSpecialization.SpecializedFunction}
    {leftLocal rightLocal : Substitution}
    (owners : ((Program.ofChecked program).functions.map fun definition => definition.body.owner).Nodup)
    (bodies : AtOwner program left.function.typedBody.owner)
    (leftOrigin : RecursiveNamedPublicSpecializationMeaning.Origin program left)
    (rightOrigin : RecursiveNamedPublicSpecializationMeaning.Origin program right)
    (sameSource : left.function.typedBody.applySubstitution leftLocal =
      right.function.typedBody.applySubstitution rightLocal) :
    left.function.declaration = right.function.declaration ∧
      left.function.typedBody = right.function.typedBody ∧
      left.function.inferredBodyType = right.function.inferredBodyType ∧
      left.function.returnComptime = right.function.returnComptime := by
  obtain ⟨leftSignature, rightSignature, generic, leftSupplied, rightSupplied,
    _leftMember, _rightMember, genericMember, leftAccepted, rightAccepted⟩ :=
    SelectedCompilationOrdinaryIdentity.common_generic_of_origins
      owners leftOrigin rightOrigin sameSource
  have leftFields := (CallableCoercionBodyProvenance.specialization_fields leftAccepted).1
  have rightFields := (CallableCoercionBodyProvenance.specialization_fields rightAccepted).1
  have rigidSame : left.function.typedBody = right.function.typedBody := by
    rw [leftFields, rightFields]
    exact CorrelatedTypedSourceInstances.apply_source_eq_of_equal_local_instances
      (fun parameter replacement found =>
        SourceSpecializationAcceptance.specializeFunction_parameterReplacement_flexibleClosed
          leftAccepted parameter replacement found)
      (fun parameter replacement found =>
        SourceSpecializationAcceptance.specializeFunction_parameterReplacement_flexibleClosed
          rightAccepted parameter replacement found)
      generic.typedBody leftLocal rightLocal
      (by simpa only [leftFields, rightFields, SourceSpecialization.applyCheckedFunction] using sameSource)
  obtain ⟨context, facts, typed, annotation⟩ := original_body (bodies generic genericMember (by
    rw [leftFields]
    exact (RecursiveNamedSpecializationBodyFacts.identities leftAccepted).2.1.symm))
  have sameAnnotation := SourceBodyResultAnnotation.parameter_instances_result_eq typed
    left.parameterSubstitution right.parameterSubstitution
    (by simpa only [RecursiveNamedSpecializationBodyFacts.body leftAccepted,
      RecursiveNamedSpecializationBodyFacts.body rightAccepted] using rigidSame)
  have resultSame : left.function.inferredBodyType = right.function.inferredBodyType := by
    rw [RecursiveNamedSpecializationBodyFacts.result leftAccepted,
      RecursiveNamedSpecializationBodyFacts.result rightAccepted]
    simpa only [annotation] using sameAnnotation
  refine ⟨?_, rigidSame, resultSame, ?_⟩
  · rw [leftFields, rightFields]; rfl
  · rw [leftFields, rightFields]; rfl

/-- Both successful analyzers therefore return the same complete analysis. -/
theorem analysis_eq_of_origins {program : CheckedProgram}
    {left right : SourceSpecialization.SpecializedFunction}
    {leftLocal rightLocal : Substitution}
    (owners : ((Program.ofChecked program).functions.map fun definition => definition.body.owner).Nodup)
    (bodies : AtOwner program left.function.typedBody.owner)
    (leftOrigin : RecursiveNamedPublicSpecializationMeaning.Origin program left)
    (rightOrigin : RecursiveNamedPublicSpecializationMeaning.Origin program right)
    (sameSource : left.function.typedBody.applySubstitution leftLocal =
      right.function.typedBody.applySubstitution rightLocal) :
    left.stageAnalysis = right.stageAnalysis := by
  obtain ⟨declarationEq, sourceEq, resultEq, returnEq⟩ :=
    source_and_result_of_origins owners bodies leftOrigin rightOrigin sameSource
  obtain ⟨_, _, _, _, _, _, leftAccepted⟩ := leftOrigin
  obtain ⟨_, _, _, _, _, _, rightAccepted⟩ := rightOrigin
  exact SourceStageAnalysisCongruence.analysis_eq_of_success declarationEq sourceEq
    (by rw [resultEq, returnEq])
    (RecursiveNamedSpecializationStageFacts.analyzed leftAccepted)
    (RecursiveNamedSpecializationStageFacts.analyzed rightAccepted)

/-- The full ledger frames agree, including when the sources are supplied
only through the actual requirement-erasure boundary. -/
theorem ledger_frame_eq_of_erased {program : CheckedProgram}
    {left right : SourceCoreStageContracts.Sidecar} {leftLocal rightLocal : Substitution}
    (owners : ((Program.ofChecked program).functions.map fun definition => definition.body.owner).Nodup)
    (bodies : AtOwner program left.caller.function.typedBody.owner)
    (samePlan : left.plan = right.plan)
    (leftOrigin : RecursiveNamedPublicSpecializationMeaning.Origin program left.caller)
    (rightOrigin : RecursiveNamedPublicSpecializationMeaning.Origin program right.caller)
    (sameSource : eraseRequirements (left.caller.function.typedBody.applySubstitution leftLocal) =
      eraseRequirements (right.caller.function.typedBody.applySubstitution rightLocal)) :
    CallableLedger.frame left = CallableLedger.frame right := by
  have exactSource :=
    SelectedCompilationOrdinaryErasure.contextual_source_eq_of_erased
      owners leftOrigin rightOrigin sameSource
  obtain ⟨_, _, resultEq, returnEq⟩ :=
    source_and_result_of_origins owners bodies leftOrigin rightOrigin exactSource
  have analysisEq := analysis_eq_of_origins owners bodies leftOrigin rightOrigin exactSource
  have stagesEq : CallStageGuard.frame left.caller = CallStageGuard.frame right.caller := by
    simp only [CallStageGuard.frame, resultEq, returnEq, analysisEq]
  simp only [CallableLedger.frame, stagesEq, samePlan]

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationOrdinaryAnnotationCoherence
