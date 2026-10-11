import Solcore.SourceSemantics.CoreLowering.CallableOrdinarySpecializationIdentity
import Solcore.Frontend.CorrelatedTypedSourceInstances
import Solcore.Frontend.SourceSpecializationAcceptance
import Solcore.Frontend.SourceStageAnalysisCongruence
import Solcore.SourceSemantics.SourceAnnotationSummaryUniqueness
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedSpecializationValidity
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedSpecializationStageFacts
import Solcore.SourceSemantics.CoreLowering.CallableLedger
import Solcore.SourceSemantics.TraitSubstitutionProperties

/-!
Two authentic ordinary specializations of the same contextual source recover
one original checked function. Its independent program typing constructs both
rigid body certificates, including their result annotations. The recovered
source and those annotations determine the enclosing result, original return
marker and stage analysis. Equal full keys are unnecessary.

Catalog-aware ordinary origins and complete raw range formation remain genuine
static inputs. Detached methods and extraction of these origins from every final
prepared row remain separate provenance boundaries.
-/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableOrdinarySpecializationStageCoherence
open Frontend SourceInference TypeSystem

private theorem original_annotation
    {signature : ProgramFunctionSignature} {generic : CheckedFunction} {facts : BodyFacts}
    {signatures : ProgramSignatures}
    (typed : BodyDefinitionHasType signatures signature.scheme.parameters
      signature.scheme.predicates signature.parameterNames signature.parameterTypes
      signature.parameterComptime signature.returnTypes signature.returnComptime
      (BodyDefinition.ofChecked generic) facts) :
    facts.type = generic.inferredBodyType := by
  cases typed with
  | intro _ _ _ _ _ resultEq _ _ _ _ _ _ _ _ _ annotation =>
      exact annotation.trans resultEq.symm

/-- The independent original body judgment and actual canonical specialization
construct both rigid typing and the annotation used to identify its result. -/
theorem annotated_body_of_program {program : CheckedProgram}
    {signature : ProgramFunctionSignature} {generic : CheckedFunction}
    {supplied : ParameterSubstitution} {specialized : SourceSpecialization.SpecializedFunction}
    (wellFormed : ProgramWellFormed (Program.ofChecked program))
    (signatureMember : signature ∈ program.signatures.functions)
    (genericMember : generic ∈ program.functions)
    (accepted : SourceSpecialization.specializeFunction signature generic supplied = .ok specialized)
    (range : SourceSemantics.ParameterSubstitution.RangeWellFormed
      (Context.ofSignatures program.signatures) specialized.parameterSubstitution) :
    ∃ context facts,
      BodyHasType specialized.function.typedBody context specialized.function.inferredBodyType facts ∧
      facts.type = specialized.function.inferredBodyType ∧
      NodeOccurrencesUnique specialized.function.typedBody := by
  have valid := wellFormed.functions_valid (FunctionDefinition.ofChecked generic)
    (List.mem_map.mpr ⟨generic, genericMember, rfl⟩)
  cases valid with
  | @intro typedSignature facts typedSignatureMember typedOwner typed =>
      have signatureEq : typedSignature = signature :=
        StructuralSubstitution.eq_of_mem_of_mapped_nodup
          wellFormed.signatures.function_ids typedSignatureMember signatureMember
          (typedOwner.symm.trans
            (RecursiveNamedSpecializationBodyFacts.identities accepted).1.symm)
      subst typedSignature
      have exactRange := RecursiveNamedSpecializationValidity.exact accepted
        (wellFormed.signatures.function_parameters signature signatureMember).1
      have rangeAfter :=
        StructuralSubstitution.ParameterSubstitution.RangeWellFormed.atApplyContextOfBase
          (context := declarationContext program.signatures generic.declaration
            signature.scheme.parameters signature.scheme.predicates generic.solvedRequirements) range
      obtain ⟨context, _inputs, bodyTyped⟩ :=
        StructuralSubstitution.BodyDefinitionHasType.instantiate
          (signatures := program.signatures)
          (assumptions := signature.scheme.predicates)
          (definition := BodyDefinition.ofChecked generic)
          specialized.parameterSubstitution wellFormed.signatures exactRange rangeAfter typed
      have annotation := original_annotation (signature := signature) (generic := generic) typed
      have bodyEq := RecursiveNamedSpecializationBodyFacts.body accepted
      have resultEq := RecursiveNamedSpecializationBodyFacts.result accepted
      refine ⟨context, StructuralSubstitution.applyBodyFacts specialized.parameterSubstitution facts,
        ?_, ?_, ?_⟩
      · rw [bodyEq, resultEq]
        exact bodyTyped
      · change specialized.parameterSubstitution.apply facts.type =
          specialized.function.inferredBodyType
        exact (congrArg specialized.parameterSubstitution.apply annotation).trans resultEq.symm
      · rw [bodyEq]
        exact (StructuralSubstitution.OccurrenceGraphClosed.applyParameters
          specialized.parameterSubstitution
          (StructuralSubstitution.BodyDefinitionHasType.graphClosed typed)).wellFormed.nodeOccurrencesUnique

/-- An actual ordinary origin supplies the selected catalog and original body
provenance; no body typing for a specialization is supplied by the caller. -/
theorem annotated_body_of_origin {program : CheckedProgram}
    {specialized : SourceSpecialization.SpecializedFunction}
    (wellFormed : ProgramWellFormed (Program.ofChecked program))
    (origin : RecursiveNamedPublicSpecializationMeaning.Origin program specialized)
    (range : SourceSemantics.ParameterSubstitution.RangeWellFormed
      (Context.ofSignatures program.signatures) specialized.parameterSubstitution) :
    ∃ context facts,
      BodyHasType specialized.function.typedBody context specialized.function.inferredBodyType facts ∧
      facts.type = specialized.function.inferredBodyType ∧
      NodeOccurrencesUnique specialized.function.typedBody := by
  obtain ⟨request, signature, generic, signatureMember, genericMember, _, accepted⟩ := origin
  exact annotated_body_of_program wellFormed signatureMember genericMember accepted range

/-- Original identity, accepted rigid ranges and the complete typed-source
recovery derive the two inputs absent from a source-only analyzer congruence. -/
theorem source_and_result_of_origins {program : CheckedProgram}
    {left right : SourceSpecialization.SpecializedFunction}
    {leftLocal rightLocal : Substitution}
    (wellFormed : ProgramWellFormed (Program.ofChecked program))
    (leftOrigin : RecursiveNamedPublicSpecializationMeaning.Origin program left)
    (rightOrigin : RecursiveNamedPublicSpecializationMeaning.Origin program right)
    (leftRange : SourceSemantics.ParameterSubstitution.RangeWellFormed
      (Context.ofSignatures program.signatures) left.parameterSubstitution)
    (rightRange : SourceSemantics.ParameterSubstitution.RangeWellFormed
      (Context.ofSignatures program.signatures) right.parameterSubstitution)
    (sameSource : left.function.typedBody.applySubstitution leftLocal =
      right.function.typedBody.applySubstitution rightLocal) :
    left.function.declaration = right.function.declaration ∧
      left.function.typedBody = right.function.typedBody ∧
      left.function.inferredBodyType = right.function.inferredBodyType ∧
      left.function.returnComptime = right.function.returnComptime := by
  obtain ⟨leftSignature, rightSignature, generic, leftSupplied, rightSupplied,
    _leftMember, _rightMember, _genericMember, leftAccepted, rightAccepted⟩ :=
    CallableOrdinarySpecializationIdentity.common_generic_of_origins
      wellFormed leftOrigin rightOrigin sameSource
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
  obtain ⟨leftContext, leftFacts, leftTyped, leftAnnotation, unique⟩ :=
    annotated_body_of_origin wellFormed leftOrigin leftRange
  obtain ⟨rightContext, rightFacts, rightTyped, rightAnnotation, _rightUnique⟩ :=
    annotated_body_of_origin wellFormed rightOrigin rightRange
  have factsSame : leftFacts.type = rightFacts.type :=
    SourceAnnotationSummaryUniqueness.body_facts_type_eq unique leftTyped
      (by simpa only [rigidSame] using rightTyped)
  have resultSame := leftAnnotation.symm.trans (factsSame.trans rightAnnotation)
  refine ⟨?_, rigidSame, resultSame, ?_⟩
  · rw [leftFields, rightFields]
    rfl
  · rw [leftFields, rightFields]
    rfl

/-- The genuine two successful analyzers retain the same complete analysis.
The effective return Boolean is derived from original typing and provenance. -/
theorem analysis_eq_of_origins {program : CheckedProgram}
    {left right : SourceSpecialization.SpecializedFunction}
    {leftLocal rightLocal : Substitution}
    (wellFormed : ProgramWellFormed (Program.ofChecked program))
    (leftOrigin : RecursiveNamedPublicSpecializationMeaning.Origin program left)
    (rightOrigin : RecursiveNamedPublicSpecializationMeaning.Origin program right)
    (leftRange : SourceSemantics.ParameterSubstitution.RangeWellFormed
      (Context.ofSignatures program.signatures) left.parameterSubstitution)
    (rightRange : SourceSemantics.ParameterSubstitution.RangeWellFormed
      (Context.ofSignatures program.signatures) right.parameterSubstitution)
    (sameSource : left.function.typedBody.applySubstitution leftLocal =
      right.function.typedBody.applySubstitution rightLocal) :
    left.stageAnalysis = right.stageAnalysis := by
  obtain ⟨sameDeclaration, rigidSame, resultSame, returnSame⟩ :=
    source_and_result_of_origins wellFormed leftOrigin rightOrigin leftRange rightRange sameSource
  obtain ⟨_, _, _, _, _, _, leftAccepted⟩ := leftOrigin
  obtain ⟨_, _, _, _, _, _, rightAccepted⟩ := rightOrigin
  exact SourceStageAnalysisCongruence.analysis_eq_of_success sameDeclaration rigidSame
    (by rw [resultSame, returnSame])
    (RecursiveNamedSpecializationStageFacts.analyzed leftAccepted)
    (RecursiveNamedSpecializationStageFacts.analyzed rightAccepted)

/-- Same-plan ordinary sidecars therefore agree in every literal guard-frame
field, even when their authenticated full specialization keys differ. -/
theorem ledger_frame_eq_of_origins {program : CheckedProgram}
    {left right : SourceCoreStageContracts.Sidecar} {leftLocal rightLocal : Substitution}
    (wellFormed : ProgramWellFormed (Program.ofChecked program))
    (samePlan : left.plan = right.plan)
    (leftOrigin : RecursiveNamedPublicSpecializationMeaning.Origin program left.caller)
    (rightOrigin : RecursiveNamedPublicSpecializationMeaning.Origin program right.caller)
    (leftRange : SourceSemantics.ParameterSubstitution.RangeWellFormed
      (Context.ofSignatures program.signatures) left.caller.parameterSubstitution)
    (rightRange : SourceSemantics.ParameterSubstitution.RangeWellFormed
      (Context.ofSignatures program.signatures) right.caller.parameterSubstitution)
    (sameSource : left.caller.function.typedBody.applySubstitution leftLocal =
      right.caller.function.typedBody.applySubstitution rightLocal) :
    CallableLedger.frame left = CallableLedger.frame right := by
  obtain ⟨_sameDeclaration, _rigidSame, resultSame, returnSame⟩ :=
    source_and_result_of_origins wellFormed leftOrigin rightOrigin leftRange rightRange sameSource
  have analysisSame := analysis_eq_of_origins wellFormed leftOrigin rightOrigin
    leftRange rightRange sameSource
  have stagesSame : CallStageGuard.frame left.caller = CallStageGuard.frame right.caller := by
    simp only [CallStageGuard.frame, resultSame, returnSame, analysisSame]
  simp only [CallableLedger.frame, stagesSame, samePlan]

end Solcore.SourceSemantics.CoreLowering.CallableOrdinarySpecializationStageCoherence
