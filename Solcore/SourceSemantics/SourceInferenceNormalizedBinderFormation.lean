import Solcore.SourceSemantics.SourceInferenceNormalizedLocalFormation

/-! A producer invariant contains only structural normalized body/predicate
formation and actual allocator/no-capture facts. It does not contain evidence
entailment, template validity or typing for the current initializer. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceNormalizedCoercionFormation
open Frontend SourceInference TypeSystem SourceInferenceRequirementFormation SourceInferenceSoundness

structure NormalizedBinderFormation (semantic : SourceSemantics.Context)
    (outer : Substitution) (binder : TypedBinder) : Prop where
  unique : binder.scheme.quantified.Nodup
  body : TypeAdmissible semantic (outer.apply binder.scheme.body)
  predicates : ∀ requirement ∈ binder.schemeRequirements,
    PredicateAdmissible semantic (TypedTraitResolution.applySubstitution outer requirement.predicate)
  noCapture : Detail.LocalBinderInstantiationNoCapture outer binder

structure NormalizedStateFormation (semantic : SourceSemantics.Context)
    (outer : Substitution) (state : State) : Prop where
  requirements : ∀ row ∈ state.requirements,
    PredicateAdmissible semantic (TypedTraitResolution.applySubstitution outer row.predicate)
  binders : ∀ binder ∈ state.localBinders, NormalizedBinderFormation semantic outer binder

namespace NormalizedBinderFormation

theorem mono {semantic : SourceSemantics.Context} {outer : Substitution}
    (state : State) (name : String) (type : Ty) (span : Option Syntax.SourceSpan)
    (comptime : Bool) (body : TypeAdmissible semantic (outer.apply type)) :
    NormalizedBinderFormation semantic outer
      (state.allocateBinder name (.mono type) span comptime).1 :=
  ⟨by simp [State.allocateBinder, Scheme.mono], body, by simp [State.allocateBinder],
    Detail.LocalBinderInstantiationNoCapture.of_quantified_eq_nil rfl⟩

theorem instantiate {semantic : SourceSemantics.Context} {context : SourceInference.Context}
    {outer : Substitution} {binder : TypedBinder}
    (binderFormed : NormalizedBinderFormation semantic outer binder)
    (formation : FormationContext semantic context outer)
    (binders : TypeParameterBindersWellFormed semantic) (next : Nat) :
    TypeAdmissible semantic (outer.apply (binder.scheme.instantiateWithSubstitution next).body) ∧
      ∀ requirement ∈ binder.schemeRequirements,
        PredicateAdmissible semantic (TypedTraitResolution.applySubstitution outer
          (TypedTraitResolution.applySubstitution
            (binder.scheme.instantiateWithSubstitution next).substitution requirement.predicate)) := by
  let inner := (binder.scheme.instantiateWithSubstitution next).substitution
  have exactInner : ExactSubstitution inner binder.scheme.quantified := {
    variables_nodup := binderFormed.unique
    domain_permutation := binder.scheme.instantiateWithSubstitution_substitution_domain_permutation next binderFormed.unique }
  have range := FlexibleSubstitution.SubstitutionRangeAdmissible.mapRange_instantiateWithSubstitution
    binder.scheme next binders formation.residual formation.range
  constructor
  · change TypeAdmissible semantic (outer.apply (inner.apply binder.scheme.body))
    rw [FlexibleSubstitution.Ty.applyFlexible_compose_of_rangeAvoidsVariablesOn outer inner exactInner
      binderFormed.noCapture.quantified_fresh binderFormed.noCapture.body_range]
    exact type_applySubstitution_residual formation.residual range binderFormed.body
  · intro requirement member
    rw [FlexibleSubstitution.TypedTraitResolution.applySubstitution_compose_of_rangeAvoidsVariablesOn
      outer inner exactInner binderFormed.noCapture.quantified_fresh
      (localBinderInstantiationNoCapture_predicateRangeAvoids binderFormed.noCapture requirement member)]
    exact predicate_applySubstitution_residual formation.residual range (binderFormed.predicates requirement member)

/-- Generalization copies its actual input type and selects predicates from
its actual ready ledger. One final continuation normalizes both fields. -/
theorem generalized
    {semantic : SourceSemantics.Context} {outer : Substitution} {state : State} {type : Ty}
    (locals : Environment) (cutoff : Nat) (name : String)
    (span : Option Syntax.SourceSpan) (comptime : Bool)
    (continuation : outer.SemanticallyExtends state.inference.substitution)
    (body : TypeAdmissible semantic (outer.apply type))
    (requirements : ∀ row ∈ state.requirements,
      PredicateAdmissible semantic (TypedTraitResolution.applySubstitution outer row.predicate))
    (noCapture : Detail.LocalBinderInstantiationNoCapture outer
      (state.allocateBinder name (Detail.generalizeValue state locals cutoff type).scheme span comptime
        (Detail.generalizeValue state locals cutoff type).requirements).1) :
    NormalizedBinderFormation semantic outer
      (state.allocateBinder name (Detail.generalizeValue state locals cutoff type).scheme span comptime
        (Detail.generalizeValue state locals cutoff type).requirements).1 := by
  refine ⟨Detail.generalizeValue_scheme_quantified_nodup state locals cutoff type, body, ?_, noCapture⟩
  intro requirement member
  obtain ⟨raw, rawMember, _, predicateEq⟩ :=
    Detail.generalizeValue_requirement_source state locals cutoff type requirement member
  rw [predicateEq]
  have normalized : TypedTraitResolution.applySubstitution outer (Detail.applyPredicate state raw.predicate) =
      TypedTraitResolution.applySubstitution outer raw.predicate := by
    cases raw.predicate with
    | mk trait subject arguments =>
      simp only [Detail.applyPredicate, TypedTraitResolution.applySubstitution]
      congr 1
      · exact continuation subject
      · simp only [List.map_map]
        exact List.map_congr_left (fun type _ => continuation type)
  rw [normalized]
  exact requirements raw rawMember

end NormalizedBinderFormation

namespace NormalizedStateFormation

theorem of_new_rows {semantic : SourceSemantics.Context} {outer : Substitution}
    {before after : State} (formed : NormalizedStateFormation semantic outer before)
    (binders : after.localBinders = before.localBinders)
    (issued : ∀ row ∈ after.requirements, row ∉ before.requirements →
      PredicateAdmissible semantic (TypedTraitResolution.applySubstitution outer row.predicate)) :
    NormalizedStateFormation semantic outer after := by
  refine ⟨?_, ?_⟩
  · intro row member
    by_cases old : row ∈ before.requirements
    · exact formed.requirements row old
    · exact issued row member old
  · intro binder member
    exact formed.binders binder (binders ▸ member)

theorem congr {semantic : SourceSemantics.Context} {outer : Substitution}
    {before after : State} (formed : NormalizedStateFormation semantic outer before)
    (binders : after.localBinders = before.localBinders)
    (rows : after.requirements = before.requirements) :
    NormalizedStateFormation semantic outer after :=
  formed.of_new_rows binders (fun _ member fresh => (fresh (rows ▸ member)).elim)

/-- Scope restoration uses a real saved scope whose binders had formation at
entry. The later ledger keeps the facts accumulated inside the scope. -/
theorem restore {semantic : SourceSemantics.Context} {outer : Substitution}
    {before after : State} (entry : NormalizedStateFormation semantic outer before)
    (later : NormalizedStateFormation semantic outer after)
    (scope : LexicalScope) (saved : scope.binders ⊆ before.localBinders) :
    NormalizedStateFormation semantic outer (after.restoreLexicalScope scope) :=
  ⟨later.requirements, fun binder member => entry.binders binder (saved member)⟩

theorem allocate {semantic : SourceSemantics.Context} {outer : Substitution}
    {state : State} (formed : NormalizedStateFormation semantic outer state)
    (name : String) (scheme : Scheme) (span : Option Syntax.SourceSpan) (comptime : Bool)
    (requirements : List LocalSchemeRequirement)
    (newBinder : NormalizedBinderFormation semantic outer
      (state.allocateBinder name scheme span comptime requirements).1) :
    NormalizedStateFormation semantic outer
      (state.allocateBinder name scheme span comptime requirements).2 := by
  refine ⟨formed.requirements, ?_⟩
  intro binder member
  rcases List.mem_cons.mp member with rfl | old
  · exact newBinder
  · exact formed.binders binder old

end NormalizedStateFormation

end Solcore.SourceSemantics.SourceInferenceNormalizedCoercionFormation
