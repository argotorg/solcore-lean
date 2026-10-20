import Solcore.SourceSemantics.SourceInferenceRequirementFormation

/-! Catalog and operand origins of actual coercion requirements. -/

set_option autoImplicit false

namespace Solcore.SourceSemantics.SourceInferenceRequirementFormation

open Frontend SourceInference TypeSystem

/-- The executable profile lookup retains a real trait signature and, when
present, one of its methods. Empty legacy marker traits keep the same origin. -/
def CoercionProfileOrigin (context : Frontend.SourceInference.Context)
    (trait : Resolved.DeclarationId) (profile : Option Detail.CoercionMethodProfile) : Prop :=
  ∃ signature ∈ context.signatures.traits,
    signature.id = trait ∧ signature.parameters.length = 2 ∧
      ∀ selected ∈ profile, selected.trait = trait ∧
        selected.parameters = signature.parameters ∧ selected.method ∈ signature.methods

theorem coercion_profile_origin
    {context : Frontend.SourceInference.Context} {trait : Resolved.DeclarationId}
    {profile : Option Detail.CoercionMethodProfile}
    (accepted : Detail.coercionMethodProfile? context trait = .ok profile) :
    CoercionProfileOrigin context trait profile := by
  unfold Detail.coercionMethodProfile? at accepted
  cases found : context.signatures.trait? trait with
  | none => simp [found, bind, Except.bind] at accepted
  | some signature =>
      have member : signature ∈ context.signatures.traits := List.mem_of_find?_eq_some found
      have idEq : signature.id = trait := of_decide_eq_true
        (List.find?_some (p := fun candidate : ProgramTraitSignature => decide (candidate.id = trait)) found)
      simp only [found, pure, Pure.pure, Except.pure, bind, Except.bind] at accepted
      split at accepted
      · rename_i arity
        cases methods : signature.methods.filter (fun method => method.name == "coerce") with
        | nil =>
            simp only [methods, Except.ok.injEq] at accepted
            cases accepted
            exact ⟨signature, member, idEq, arity, by simp⟩
        | cons method rest =>
            cases rest with
            | cons second rest => simp [methods] at accepted
            | nil =>
                simp only [methods, Except.ok.injEq] at accepted
                cases accepted
                refine ⟨signature, member, idEq, arity, ?_⟩
                intro selected selectedMember
                simp only [Option.mem_def, Option.some.injEq] at selectedMember
                cases selectedMember
                refine ⟨rfl, rfl, ?_⟩
                exact (List.mem_filter.mp (show method ∈ signature.methods.filter
                  (fun method => method.name == "coerce") by rw [methods]; simp)).1
      · simp_all

/-- Actual profile and method-predicate computation produce a formed primary
trait predicate and formed companion predicates from the two endpoint types.
The optional absent method is accepted exactly as by the inference runtime. -/
theorem coercion_issuance
    {inferenceContext : Frontend.SourceInference.Context}
    {context : SourceSemantics.Context} {trait : Resolved.DeclarationId}
    {profile : Option Detail.CoercionMethodProfile}
    {source target : Ty} {predicates : List ProgramPredicate}
    (catalog : SignatureCatalogWellFormed context.signatures)
    (binders : TypeParameterBindersWellFormed context)
    (signatures : context.signatures = inferenceContext.signatures)
    (sourceFormed : TypeAdmissible context source)
    (targetFormed : TypeAdmissible context target)
    (profileAccepted : Detail.coercionMethodProfile? inferenceContext trait = .ok profile)
    (predicatesAccepted : Detail.coercionMethodPredicates profile source target = .ok predicates) :
    PredicateAdmissible context { trait := .declaration trait, subject := source, arguments := [target] } ∧
      (∀ predicate ∈ predicates, PredicateAdmissible context predicate) := by
  obtain ⟨signature, signatureMember, idEq, arity, selectedOrigin⟩ :=
    coercion_profile_origin profileAccepted
  have semanticMember : signature ∈ context.signatures.traits := signatures.symm ▸ signatureMember
  have signatureFormed := catalog.traits_semantic signature semanticMember
  constructor
  · exact ⟨sourceFormed, by intro argument member; simp only [List.mem_singleton] at member; subst argument; exact targetFormed,
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
        have range : SourceSemantics.ParameterSubstitution.RangeAdmissible context
            (profile.parameters.zip [source, target]) := by
          intro parameter replacement member
          have choice := (List.of_mem_zip member).2
          simp only [List.mem_cons, List.not_mem_nil, or_false] at choice
          rcases choice with rfl | rfl
          · exact sourceFormed
          · exact targetFormed
        simp only [Detail.coercionMethodPredicates] at predicatesAccepted
        split at predicatesAccepted
        · simp only [pure, Pure.pure, Except.pure, Except.ok.injEq] at predicatesAccepted
          cases predicatesAccepted
          intro predicate member
          obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp member
          exact predicate_applyParameters_admissible
            (source := signatureContext context.signatures signature.id signature.parameters
              (signature.wherePredicates ++ profile.method.wherePredicates))
            (profile.parameters.zip [source, target]) exactSubstitution range rfl binders
            ((signatureFormed.methods profile.method origin.2.2).predicates original originalMember)
        · simp [throw, Functor.map, Except.map] at predicatesAccepted

end Solcore.SourceSemantics.SourceInferenceRequirementFormation
