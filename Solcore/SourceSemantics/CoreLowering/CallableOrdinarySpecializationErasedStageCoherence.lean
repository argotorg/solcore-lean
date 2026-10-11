import Solcore.SourceSemantics.CoreLowering.CallableOrdinarySpecializationStageCoherence
import Solcore.SourceSemantics.CoreLowering.CallableAncestryProfiles

/-!
Requirement rewriting in an applied view preserves the source with requirement
lists erased. For two genuine ordinary specializations, this weaker equality
still identifies their original checked function. Its requirement profiles
survive both rigid and local substitution, recovering full equality of the two
canonical contextual sources and their original stage frames.

The rewritten applied source itself is not equated with a canonical source.
Actual ancestry receipts must supply the erased equality. Ordinary catalog
origins and full raw substitution formation remain explicit static inputs.
-/
set_option autoImplicit false

namespace Solcore.SourceSemantics.CoreLowering.CallableOrdinarySpecializationErasedStageCoherence
open Frontend SourceInference TypeSystem CallableAncestryMetadata

private theorem rigid_profile (substitution : ParameterSubstitution) (source : TypedSource) :
    requirementProfile (SourceSpecialization.applyTypedSource substitution source) =
      requirementProfile source := by
  simp only [requirementProfile, SourceSpecialization.applyTypedSource, List.map_map]
  apply List.map_congr_left
  intro node _
  cases node <;> rfl

private theorem generic_eq_of_erased {program : CheckedProgram}
    {leftSignature rightSignature : ProgramFunctionSignature}
    {leftGeneric rightGeneric : CheckedFunction}
    {leftSupplied rightSupplied : ParameterSubstitution}
    {left right : SourceSpecialization.SpecializedFunction}
    {leftLocal rightLocal : Substitution}
    (wellFormed : ProgramWellFormed (Program.ofChecked program))
    (leftMember : leftGeneric ∈ program.functions)
    (rightMember : rightGeneric ∈ program.functions)
    (leftAccepted : SourceSpecialization.specializeFunction
      leftSignature leftGeneric leftSupplied = .ok left)
    (rightAccepted : SourceSpecialization.specializeFunction
      rightSignature rightGeneric rightSupplied = .ok right)
    (erased : eraseRequirements (left.function.typedBody.applySubstitution leftLocal) =
      eraseRequirements (right.function.typedBody.applySubstitution rightLocal)) :
    leftGeneric = rightGeneric := by
  have unique : (program.functions.map (fun function => function.declaration)).Nodup := by
    simpa only [Program.ofChecked, List.map_map, Function.comp_def,
      FunctionDefinition.ofChecked, BodyDefinition.ofChecked] using wellFormed.function_ids
  have owners := congrArg TypedSource.owner erased
  change left.function.typedBody.owner = right.function.typedBody.owner at owners
  rw [(CallableCoercionBodyProvenance.specialization_fields leftAccepted).1,
    (CallableCoercionBodyProvenance.specialization_fields rightAccepted).1] at owners
  change leftGeneric.typedBody.owner = rightGeneric.typedBody.owner at owners
  exact StructuralSubstitution.eq_of_mem_of_mapped_nodup unique leftMember rightMember
    ((RecursiveNamedSpecializationBodyFacts.identities leftAccepted).2.1.symm.trans
      (owners.trans (RecursiveNamedSpecializationBodyFacts.identities rightAccepted).2.1))

/-- The original ordinary function supplies both requirement profiles. Neither
profile equality nor equality of the original templates is assumed. -/
theorem contextual_source_eq_of_erased {program : CheckedProgram}
    {left right : SourceSpecialization.SpecializedFunction}
    {leftLocal rightLocal : Substitution}
    (wellFormed : ProgramWellFormed (Program.ofChecked program))
    (leftOrigin : RecursiveNamedPublicSpecializationMeaning.Origin program left)
    (rightOrigin : RecursiveNamedPublicSpecializationMeaning.Origin program right)
    (erased : eraseRequirements (left.function.typedBody.applySubstitution leftLocal) =
      eraseRequirements (right.function.typedBody.applySubstitution rightLocal)) :
    left.function.typedBody.applySubstitution leftLocal =
      right.function.typedBody.applySubstitution rightLocal := by
  obtain ⟨leftRequest, leftSignature, leftGeneric, _leftSignatureMember,
    leftMember, _leftResolved, leftAccepted⟩ := leftOrigin
  obtain ⟨rightRequest, rightSignature, rightGeneric, _rightSignatureMember,
    rightMember, _rightResolved, rightAccepted⟩ := rightOrigin
  have same := generic_eq_of_erased wellFormed leftMember rightMember
    leftAccepted rightAccepted erased
  subst rightGeneric
  apply FiniteProfiles.source_unique erased
  rw [CallableAncestryProfiles.profile_substitute, CallableAncestryProfiles.profile_substitute,
    (CallableCoercionBodyProvenance.specialization_fields leftAccepted).1,
    (CallableCoercionBodyProvenance.specialization_fields rightAccepted).1]
  change requirementProfile (SourceSpecialization.applyTypedSource
      left.parameterSubstitution leftGeneric.typedBody) =
    requirementProfile (SourceSpecialization.applyTypedSource
      right.parameterSubstitution leftGeneric.typedBody)
  rw [rigid_profile, rigid_profile]

/-- An erased-source correspondence suffices for ordinary canonical sidecars.
The existing typing and specialization proofs derive all stage-frame fields. -/
theorem ledger_frame_eq_of_erased {program : CheckedProgram}
    {left right : SourceCoreStageContracts.Sidecar} {leftLocal rightLocal : Substitution}
    (wellFormed : ProgramWellFormed (Program.ofChecked program))
    (samePlan : left.plan = right.plan)
    (leftOrigin : RecursiveNamedPublicSpecializationMeaning.Origin program left.caller)
    (rightOrigin : RecursiveNamedPublicSpecializationMeaning.Origin program right.caller)
    (leftRange : SourceSemantics.ParameterSubstitution.RangeWellFormed
      (Context.ofSignatures program.signatures) left.caller.parameterSubstitution)
    (rightRange : SourceSemantics.ParameterSubstitution.RangeWellFormed
      (Context.ofSignatures program.signatures) right.caller.parameterSubstitution)
    (erased : eraseRequirements (left.caller.function.typedBody.applySubstitution leftLocal) =
      eraseRequirements (right.caller.function.typedBody.applySubstitution rightLocal)) :
    CallableLedger.frame left = CallableLedger.frame right :=
  CallableOrdinarySpecializationStageCoherence.ledger_frame_eq_of_origins
    wellFormed samePlan leftOrigin rightOrigin leftRange rightRange
    (contextual_source_eq_of_erased wellFormed leftOrigin rightOrigin erased)

end Solcore.SourceSemantics.CoreLowering.CallableOrdinarySpecializationErasedStageCoherence
