import Solcore.SourceSemantics.CoreLowering.CallableOrdinarySpecializationStageCoherence
import Solcore.SourceSemantics.CoreLowering.CallableAncestryProfiles

/-! Ordinary origins keep their original identity using catalog uniqueness. -/
set_option autoImplicit false
set_option Elab.async false

namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationOrdinaryErasure
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
    (owners : ((Program.ofChecked program).functions.map fun definition => definition.body.owner).Nodup)
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
      FunctionDefinition.ofChecked, BodyDefinition.ofChecked] using owners
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
    (owners : ((Program.ofChecked program).functions.map fun definition => definition.body.owner).Nodup)
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
  have same := generic_eq_of_erased owners leftMember rightMember
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

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationOrdinaryErasure
