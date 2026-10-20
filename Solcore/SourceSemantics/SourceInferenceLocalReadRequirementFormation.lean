import Solcore.SourceSemantics.SourceInferenceRetainedRequirementFormation
import Solcore.Frontend.SourceInference.LocalReadEvents

/-! Actual local-reference obligation formation under the final substitution. -/

set_option autoImplicit false

namespace Solcore.SourceSemantics.SourceInferenceRequirementFormation

open Frontend SourceInference TypeSystem
open SourceInferenceSoundness

/-- An actual lookup reuses the prior binder's final formation certificate.
The shared fresh substitution and finalizer no-capture facts transport every
qualified predicate into this occurrence's residual context. -/
theorem local_read_normalized_predicates
    (lookup : LocalReadEvents.Lookup)
    {outer : Substitution} {context : SourceSemantics.Context}
    (binders : TypeParameterBindersWellFormed context)
    (residual : context.residualTypeVariables = true)
    (range : SubstitutionRangeAdmissible context outer)
    (formation : LocalSchemeRequirementsWellFormed context
      (lookup.binder.applySubstitution outer))
    (scheme : SchemeWellFormed context (lookup.binder.applySubstitution outer).scheme)
    (noCapture : Detail.LocalBinderInstantiationNoCapture outer lookup.binder)
    (continuation : outer.SemanticallyExtends lookup.advanced.inference.substitution) :
    ∀ predicate ∈ lookup.predicates,
      PredicateAdmissible context (TypedTraitResolution.applySubstitution outer predicate) := by
  let inner := (lookup.binder.scheme.instantiateWithSubstitution
    lookup.allocated.inference.next).substitution
  have unique : lookup.binder.scheme.quantified.Nodup := by
    simpa using scheme.quantified_nodup
  have exactInner : ExactSubstitution inner lookup.binder.scheme.quantified := {
    variables_nodup := unique
    domain_permutation := lookup.binder.scheme.instantiateWithSubstitution_substitution_domain_permutation
      lookup.allocated.inference.next unique
  }
  have normalization (predicate : ProgramPredicate) :
      TypedTraitResolution.applySubstitution outer (Detail.applyPredicate lookup.advanced predicate) =
        TypedTraitResolution.applySubstitution outer predicate := by
    have restricted := FlexibleSubstitution.Substitution.without_eq_self_of_disjoint_domain
      outer lookup.binder.scheme.quantified noCapture.quantified_fresh
    simpa only [restricted] using
      retained_predicate_normalization continuation noCapture predicate
  have normalized : lookup.predicates.map (TypedTraitResolution.applySubstitution outer) =
      (instantiateLocalSchemePredicates inner lookup.binder).map
        (TypedTraitResolution.applySubstitution outer) := by
    unfold LocalReadEvents.Lookup.predicates instantiateLocalSchemePredicates
    simp only [List.map_map]
    apply List.map_congr_left
    intro requirement _
    exact normalization _
  have commutes :=
    FlexibleSubstitution.instantiateLocalSchemePredicates_applySubstitution_of_rangeAvoidsVariablesOn
      exactInner noCapture.quantified_fresh
      (localBinderInstantiationNoCapture_predicateRangeAvoids noCapture)
  have composedRange :=
    FlexibleSubstitution.SubstitutionRangeAdmissible.mapRange_instantiateWithSubstitution
      lookup.binder.scheme lookup.allocated.inference.next binders residual range
  intro predicate member
  have normalizedMember : TypedTraitResolution.applySubstitution outer predicate ∈
      instantiateLocalSchemePredicates (FlexibleSubstitution.Substitution.mapRange outer inner)
        (lookup.binder.applySubstitution outer) := by
    rw [← commutes, ← normalized]
    exact List.mem_map.mpr ⟨predicate, member, rfl⟩
  obtain ⟨requirement, requirementMember, same⟩ := List.mem_map.mp normalizedMember
  rw [← same]
  exact predicate_applySubstitution_residual residual composedRange
    (predicate_transport_residual
      (source := localSchemeInitializerContext context (lookup.binder.applySubstitution outer)) binders rfl rfl rfl residual
      (formation.entries requirement requirementMember).predicate)

/-- The accepted local-reference branch supplies the exact ledger identities;
formation comes from the same lookup's canonical instantiation, never from
assuming that a solved requirement is well formed. -/
theorem local_read_issuance
    (lookup : LocalReadEvents.Lookup)
    {outer : Substitution} {context : SourceSemantics.Context}
    (binders : TypeParameterBindersWellFormed context)
    (residual : context.residualTypeVariables = true)
    (range : SubstitutionRangeAdmissible context outer)
    (formation : LocalSchemeRequirementsWellFormed context
      (lookup.binder.applySubstitution outer))
    (scheme : SchemeWellFormed context (lookup.binder.applySubstitution outer).scheme)
    (noCapture : Detail.LocalBinderInstantiationNoCapture outer lookup.binder)
    (continuation : outer.SemanticallyExtends lookup.advanced.inference.substitution) :
    RequirementPredicatesCorrespond lookup.result.2.requirements lookup.predicates lookup.batch.1 ∧
      (∀ predicate ∈ lookup.predicates,
        PredicateAdmissible context (TypedTraitResolution.applySubstitution outer predicate)) := by
  have issued := Detail.inferExprFuel_localIdentifier_operational lookup.form lookup.allocation
    lookup.found lookup.accepted lookup.wellFormed lookup.directAllocated
  exact ⟨issued.1, local_read_normalized_predicates lookup binders residual range
    formation scheme noCapture continuation⟩

end Solcore.SourceSemantics.SourceInferenceRequirementFormation
