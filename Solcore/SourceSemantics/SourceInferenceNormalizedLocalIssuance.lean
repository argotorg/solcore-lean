import Solcore.SourceSemantics.SourceInferenceNormalizedBinderFormation

/-! A local-reference producer needs structural facts about the earlier
binder; template evidence and current-expression typing are not inputs. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceNormalizedCoercionFormation
open Frontend SourceInference TypeSystem SourceInferenceRequirementFormation SourceInferenceSoundness

private theorem normalize_predicate {outer : Substitution} {state : State}
    (continuation : outer.SemanticallyExtends state.inference.substitution) (predicate : ProgramPredicate) :
    TypedTraitResolution.applySubstitution outer (Detail.applyPredicate state predicate) =
      TypedTraitResolution.applySubstitution outer predicate := by
  cases predicate with
  | mk trait subject arguments =>
    simp only [Detail.applyPredicate, TypedTraitResolution.applySubstitution]
    congr 1
    · exact continuation subject
    · simp only [List.map_map]
      exact List.map_congr_left (fun type _ => continuation type)

private theorem batch_origin (state : State) (predicates : List ProgramPredicate)
    {row : Requirement} (member : row ∈ (state.addRequirementsWithIds predicates).2.requirements) :
    row ∈ state.requirements ∨ row.predicate ∈ predicates := by
  induction predicates generalizing state with
  | nil => exact Or.inl member
  | cons predicate predicates ih =>
    rcases ih (state.addRequirementWithId predicate).2 member with old | issued
    · rcases List.mem_append.mp old with old | new
      · exact .inl old
      · simp only [List.mem_singleton] at new
        subst row
        exact .inr (by simp)
    · exact .inr (by simp [issued])

theorem lookup_normalized_formation
    (lookup : LocalReadEvents.Lookup) {semantic : SourceSemantics.Context} {outer : Substitution}
    (formation : FormationContext semantic lookup.context outer)
    (binders : TypeParameterBindersWellFormed semantic)
    (earlier : NormalizedBinderFormation semantic outer lookup.binder)
    (beforeContinuation : outer.SemanticallyExtends lookup.advanced.inference.substitution)
    (afterContinuation : outer.SemanticallyExtends lookup.result.2.inference.substitution)
    (expectedFormed : ∀ type ∈ lookup.expected, TypeAdmissible semantic (outer.apply type)) :
    TypeAdmissible semantic (outer.apply lookup.result.1.type) ∧
      ∀ row ∈ lookup.result.2.requirements, row ∉ lookup.initial.requirements →
        PredicateAdmissible semantic (TypedTraitResolution.applySubstitution outer row.predicate) := by
  have instantiated := earlier.instantiate formation binders lookup.allocated.inference.next
  have resolvedFormed : TypeAdmissible semantic
      (outer.apply (lookup.advanced.resolve
        (lookup.binder.scheme.instantiateWithSubstitution lookup.allocated.inference.next).body)) :=
    (beforeContinuation _).symm ▸ instantiated.1
  have predicatesFormed : ∀ predicate ∈ lookup.predicates,
      PredicateAdmissible semantic (TypedTraitResolution.applySubstitution outer predicate) := by
    intro predicate member
    obtain ⟨requirement, requirementMember, rfl⟩ := List.mem_map.mp member
    rw [normalize_predicate beforeContinuation]
    exact instantiated.2 requirement requirementMember
  have recorded := recordExpressionWithExpected_normalized_formation formation afterContinuation
    resolvedFormed expectedFormed lookup.recorded
  refine ⟨recorded.1, new_normalized_requirements_trans (middle := lookup.batch.2) ?_ recorded.2⟩
  intro row member fresh
  rcases batch_origin lookup.advanced lookup.predicates member with old | issued
  · have present : row ∈ lookup.allocated.requirements := old
    have allocatedEq : lookup.allocated = lookup.initial.allocateExpressionId.2 :=
      (congrArg Prod.snd lookup.allocation).symm
    rw [allocatedEq] at present
    exact (fresh present).elim
  · exact predicatesFormed row.predicate issued

/-- Actual lookup membership selects the earlier binder from the input
invariant. The complete accepted branch updates the real ledger and returns
the same executable lexical scope. -/
theorem lookup_normalized_state
    (lookup : LocalReadEvents.Lookup) {semantic : SourceSemantics.Context} {outer : Substitution}
    (formation : FormationContext semantic lookup.context outer)
    (binders : TypeParameterBindersWellFormed semantic)
    (initial : NormalizedStateFormation semantic outer lookup.initial)
    (beforeContinuation : outer.SemanticallyExtends lookup.advanced.inference.substitution)
    (afterContinuation : outer.SemanticallyExtends lookup.result.2.inference.substitution)
    (expectedFormed : ∀ type ∈ lookup.expected, TypeAdmissible semantic (outer.apply type)) :
    TypeAdmissible semantic (outer.apply lookup.result.1.type) ∧
      NormalizedStateFormation semantic outer lookup.result.2 := by
  have member := (State.lookupBinder?_eq_some_facts lookup.found).1
  have allocatedEq : lookup.allocated = lookup.initial.allocateExpressionId.2 :=
    (congrArg Prod.snd lookup.allocation).symm
  rw [allocatedEq] at member
  have produced := lookup_normalized_formation lookup formation binders
    (initial.binders lookup.binder member) beforeContinuation afterContinuation expectedFormed
  exact ⟨produced.1, initial.of_new_rows
    (congrArg LexicalScope.binders (Detail.inferExprFuel_success_lexicalScope_eq lookup.accepted)) produced.2⟩

end Solcore.SourceSemantics.SourceInferenceNormalizedCoercionFormation
