import Solcore.SourceSemantics.SourceInferenceNormalizedBinderFormation

/-! The real declaration entry has an empty requirement ledger and only
monomorphic parameter binders. Its normalized formation comes from the
accepted signature catalog and the same final substitution range. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceNormalizedCoercionFormation
open Frontend SourceInference TypeSystem SourceInferenceRequirementFormation SourceInferenceSoundness

namespace NormalizedStateFormation

theorem initial
    {semantic : SourceSemantics.Context} {outer : Substitution}
    (owner : Resolved.DeclarationId) (locals : Environment) (comptime : List Bool)
    (monomorphic : ∀ entry ∈ locals, entry.2.quantified = [])
    (formed : ∀ entry ∈ locals, TypeAdmissible semantic (outer.apply entry.2.body)) :
    NormalizedStateFormation semantic outer (State.initial owner locals comptime) := by
  refine ⟨by simp [State.initial], ?_⟩
  intro binder member
  rw [← State.initial_inputs_eq_localBinders, State.initial_inputs_definition] at member
  obtain ⟨index, below, binderEq⟩ := List.exists_of_mem_mapIdx member
  subst binder
  have entryMember := List.getElem_mem below
  have quantified := monomorphic locals[index] entryMember
  refine ⟨?_, formed _ entryMember, by simp, ?_⟩
  · simpa only [quantified] using (List.nodup_nil : ([] : List TypeVarId).Nodup)
  · exact Detail.LocalBinderInstantiationNoCapture.of_quantified_eq_nil quantified

end NormalizedStateFormation

/-- All input formation hypotheses are discharged by the actual signature
and final range; no body typing or generalized-initializer law is used. -/
theorem function_entry_normalized_formation
    {semantic : SourceSemantics.Context} {context : SourceInference.Context}
    {outer : Substitution} {signature : ProgramFunctionSignature}
    (formation : FormationContext semantic context outer)
    (member : signature ∈ semantic.signatures.functions)
    (parameters : semantic.typeParameters = signature.scheme.parameters)
    (owner : semantic.currentDeclaration = some signature.id)
    (declaration : Resolved.DeclarationId) :
    NormalizedStateFormation semantic outer
      (State.initial declaration
        ((signature.parameterNames.zip signature.parameterTypes).map
          fun parameter => (parameter.1, Scheme.mono parameter.2))
        signature.parameterComptime) := by
  apply NormalizedStateFormation.initial
  · intro entry entryMember
    obtain ⟨parameter, _, rfl⟩ := List.mem_map.mp entryMember
    rfl
  · intro entry entryMember
    obtain ⟨parameter, parameterMember, rfl⟩ := List.mem_map.mp entryMember
    have formed := (formation.catalog.functions_semantic signature member).parameter_types
      parameter.2 (List.of_mem_zip parameterMember).2
    apply type_applySubstitution_residual formation.residual formation.range
    exact TypeAdmissible.ofWellFormed (StructuralSubstitution.TypeWellFormed.transportContext
      (source := signatureContext semantic.signatures signature.id
        signature.scheme.parameters signature.scheme.predicates)
      (target := semantic)
      rfl parameters owner formed)

end Solcore.SourceSemantics.SourceInferenceNormalizedCoercionFormation
