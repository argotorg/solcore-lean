import Solcore.SourceSemantics.SourceInferenceRequirementSubstitution
import Solcore.SourceSemantics.SourceInferenceCoercionRequirementFormation

/-! Actual producer predicates can be formed in the final inference context,
using the final types of their operands directly. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceRequirementFormation
open Frontend SourceInference TypeSystem
open SourceInferenceSoundness

theorem predicate_applyParameters_normalized_admissible
    {source target : SourceSemantics.Context} {predicate : ProgramPredicate}
    (outer : Substitution) (inner : TypeSystem.ParameterSubstitution)
    (exact : SourceSemantics.ParameterSubstitution.Exact inner source.typeParameters)
    (range : ∀ parameter replacement, (parameter, replacement) ∈ inner →
      TypeAdmissible target (outer.apply replacement))
    (signatures : target.signatures = source.signatures)
    (binders : TypeParameterBindersWellFormed target)
    (formed : PredicateWellFormed source predicate) :
    PredicateAdmissible target
      (TypedTraitResolution.applySubstitution outer (predicate.applyParameters inner)) := by
  rw [FlexibleSubstitution.PredicateWellFormed.applyFlexible_composeParameters outer inner exact formed]
  apply predicate_applyParameters_admissible
    (FlexibleSubstitution.ParameterSubstitution.mapRange outer inner)
    (FlexibleSubstitution.ParameterSubstitution.Exact.mapRange outer exact) ?_ signatures binders formed
  intro parameter replacement member
  obtain ⟨⟨original, type⟩, originalMember, same⟩ := List.mem_map.mp member
  cases same
  exact range original type originalMember

theorem operator_profile_predicates_normalized
    {context : SourceSemantics.Context} {traitName methodName : String}
    {operand : Ty} {parameters returns : List Ty} {predicates : List ProgramPredicate}
    {outer : Substitution}
    (catalog : SignatureCatalogWellFormed context.signatures)
    (operandFormed : TypeAdmissible context (outer.apply operand))
    (profile : OperatorProfileInstantiates context traitName methodName operand parameters returns predicates) :
    ∀ predicate ∈ predicates,
      PredicateAdmissible context (TypedTraitResolution.applySubstitution outer predicate) := by
  cases profile with
  | @intro signature method parameter signatureMember _ parametersEq methodUnique _ _ =>
    have signatureFormed := catalog.traits_semantic signature signatureMember
    have methodMember : method ∈ signature.methods := by
      have filtered : method ∈ signature.methods.filter
          (fun candidate => candidate.name == methodName) := by
        rw [methodUnique]
        simp
      exact (List.mem_filter.mp filtered).1
    have exactSubstitution : SourceSemantics.ParameterSubstitution.Exact
        [(parameter, operand)] signature.parameters := by
      rw [parametersEq]
      exact SourceSemantics.ParameterSubstitution.exact_singleton _ _
    intro predicate member
    rcases List.mem_cons.mp member with rfl | member
    · change PredicateAdmissible context
        {trait := .declaration signature.id, subject := outer.apply operand, arguments := []}
      exact ⟨operandFormed, by simp,
        signature, signatureMember, rfl, by simp [parametersEq]⟩
    · obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp member
      apply predicate_applyParameters_normalized_admissible
        (source := signatureContext context.signatures signature.id signature.parameters
          (signature.wherePredicates ++ method.wherePredicates))
        (target := context)
        outer [(parameter, operand)] exactSubstitution ?_ rfl operandFormed.binders
        ((signatureFormed.methods method methodMember).predicates original originalMember)
      intro candidate replacement member
      cases List.mem_singleton.mp member
      exact operandFormed

theorem operator_issuance_normalized
    {inferenceContext : SourceInference.Context} {context : SourceSemantics.Context}
    {trait : Resolved.DeclarationId} {traitName methodName : String}
    {operand : Ty} {parameters returns : List Ty} {predicates : List ProgramPredicate}
    {outer : Substitution}
    (catalog : SignatureCatalogWellFormed context.signatures)
    (signatures : context.signatures = inferenceContext.signatures)
    (traitNameEq : (inferenceContext.signatures.trait? trait).map (·.name) = some traitName)
    (operandFormed : TypeAdmissible context (outer.apply operand))
    (accepted : Detail.operatorTraitPredicates inferenceContext trait methodName operand
      parameters returns = .ok predicates) :
    ∀ predicate ∈ predicates,
      PredicateAdmissible context (TypedTraitResolution.applySubstitution outer predicate) :=
  operator_profile_predicates_normalized catalog operandFormed
    (operatorTraitPredicates_instantiates signatures traitNameEq accepted)

theorem coercion_issuance_normalized
    {inferenceContext : SourceInference.Context} {context : SourceSemantics.Context}
    {trait : Resolved.DeclarationId} {profile : Option Detail.CoercionMethodProfile}
    {source target : Ty} {predicates : List ProgramPredicate} {outer : Substitution}
    (catalog : SignatureCatalogWellFormed context.signatures)
    (signatures : context.signatures = inferenceContext.signatures)
    (sourceFormed : TypeAdmissible context (outer.apply source))
    (targetFormed : TypeAdmissible context (outer.apply target))
    (profileAccepted : Detail.coercionMethodProfile? inferenceContext trait = .ok profile)
    (predicatesAccepted : Detail.coercionMethodPredicates profile source target = .ok predicates) :
    PredicateAdmissible context (TypedTraitResolution.applySubstitution outer
      {trait := .declaration trait, subject := source, arguments := [target]}) ∧
      ∀ predicate ∈ predicates,
        PredicateAdmissible context (TypedTraitResolution.applySubstitution outer predicate) := by
  obtain ⟨signature, signatureMember, idEq, arity, selectedOrigin⟩ :=
    coercion_profile_origin profileAccepted
  have semanticMember : signature ∈ context.signatures.traits := signatures.symm ▸ signatureMember
  have signatureFormed := catalog.traits_semantic signature semanticMember
  constructor
  · exact ⟨sourceFormed, by intro argument member; cases List.mem_singleton.mp member; exact targetFormed,
      signature, semanticMember, idEq, arity.symm⟩
  · cases profile with
    | none =>
      simp [Detail.coercionMethodPredicates] at predicatesAccepted
      subst predicates
      simp
    | some profile =>
      have origin := selectedOrigin profile (by simp)
      have exactSubstitution : SourceSemantics.ParameterSubstitution.Exact
          (profile.parameters.zip [source, target]) signature.parameters := by
        rw [origin.2.1]
        exact SourceSemantics.ParameterSubstitution.exact_zip
          signatureFormed.parameters_nodup (by simpa using arity.symm)
      simp only [Detail.coercionMethodPredicates] at predicatesAccepted
      split at predicatesAccepted
      · simp only [pure, Pure.pure, Except.pure, Except.ok.injEq] at predicatesAccepted
        cases predicatesAccepted
        intro predicate member
        obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp member
        apply predicate_applyParameters_normalized_admissible
          (source := signatureContext context.signatures signature.id signature.parameters
            (signature.wherePredicates ++ profile.method.wherePredicates))
          (target := context)
          outer (profile.parameters.zip [source, target]) exactSubstitution ?_
          rfl sourceFormed.binders
          ((signatureFormed.methods profile.method origin.2.2).predicates original originalMember)
        intro parameter replacement member
        have choice := (List.of_mem_zip member).2
        rcases List.mem_cons.mp choice with rfl | choice
        · exact sourceFormed
        · cases List.mem_singleton.mp choice
          exact targetFormed
      · simp [throw, Functor.map, Except.map] at predicatesAccepted

end Solcore.SourceSemantics.SourceInferenceRequirementFormation
