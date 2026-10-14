import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicSpecializationMeaning
import Solcore.SourceSemantics.SubstitutionProperties

/-! Ordinary origins keep their original identity using catalog uniqueness. -/

set_option autoImplicit false
set_option Elab.async false

namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationOrdinaryIdentity

open Frontend SourceInference TypeSystem

/-- Source-owner preservation and the genuine ordinary catalog identify the
entire original checker record even when the two full specialization keys differ. -/
theorem generic_eq_of_sources {program : CheckedProgram}
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
    (sameSource : left.function.typedBody.applySubstitution leftLocal =
      right.function.typedBody.applySubstitution rightLocal) :
    leftGeneric = rightGeneric := by
  have unique : (program.functions.map (fun function => function.declaration)).Nodup := by
    simpa only [Program.ofChecked, List.map_map, Function.comp_def,
      FunctionDefinition.ofChecked, BodyDefinition.ofChecked] using owners
  have leftOwner : (left.function.typedBody.applySubstitution leftLocal).owner =
      leftGeneric.declaration := by
    rw [(CallableCoercionBodyProvenance.specialization_fields leftAccepted).1]
    change leftGeneric.typedBody.owner = leftGeneric.declaration
    exact (RecursiveNamedSpecializationBodyFacts.identities leftAccepted).2.1
  have rightOwner : (right.function.typedBody.applySubstitution rightLocal).owner =
      rightGeneric.declaration := by
    rw [(CallableCoercionBodyProvenance.specialization_fields rightAccepted).1]
    change rightGeneric.typedBody.owner = rightGeneric.declaration
    exact (RecursiveNamedSpecializationBodyFacts.identities rightAccepted).2.1
  exact StructuralSubstitution.eq_of_mem_of_mapped_nodup unique leftMember rightMember
    (leftOwner.symm.trans ((congrArg TypedSource.owner sameSource).trans rightOwner))

/-- The actual ordinary producer witnesses supply membership and both accepted
specializer equations internally. No common-template equation is an input. -/
theorem common_generic_of_origins {program : CheckedProgram}
    {left right : SourceSpecialization.SpecializedFunction}
    {leftLocal rightLocal : Substitution}
    (owners : ((Program.ofChecked program).functions.map fun definition => definition.body.owner).Nodup)
    (leftOrigin : RecursiveNamedPublicSpecializationMeaning.Origin program left)
    (rightOrigin : RecursiveNamedPublicSpecializationMeaning.Origin program right)
    (sameSource : left.function.typedBody.applySubstitution leftLocal =
      right.function.typedBody.applySubstitution rightLocal) :
    ∃ leftSignature rightSignature generic leftSupplied rightSupplied,
      leftSignature ∈ program.signatures.functions ∧
      rightSignature ∈ program.signatures.functions ∧ generic ∈ program.functions ∧
      SourceSpecialization.specializeFunction leftSignature generic leftSupplied = .ok left ∧
      SourceSpecialization.specializeFunction rightSignature generic rightSupplied = .ok right := by
  obtain ⟨leftRequest, leftSignature, leftGeneric, leftSignatureMember,
    leftMember, _, leftAccepted⟩ := leftOrigin
  obtain ⟨rightRequest, rightSignature, rightGeneric, rightSignatureMember,
    rightMember, _, rightAccepted⟩ := rightOrigin
  have same := generic_eq_of_sources owners leftMember rightMember
    leftAccepted rightAccepted sameSource
  subst rightGeneric
  exact ⟨leftSignature, rightSignature, leftGeneric, leftRequest.parameterSubstitution,
    rightRequest.parameterSubstitution, leftSignatureMember, rightSignatureMember,
    leftMember, leftAccepted, rightAccepted⟩

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationOrdinaryIdentity
