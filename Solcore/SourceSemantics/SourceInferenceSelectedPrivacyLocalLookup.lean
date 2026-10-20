import Solcore.SourceSemantics.SourceInferenceSelectedPrivacyReferences

/-! Actual local lookup privacy uses allocator domain coverage. It does not
require uniqueness of the stored scheme quantifier list. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables.UnrestrictedLocalLookup
open Frontend SourceInference TypeSystem

private theorem instantiated_variable_origin {state : State} (ready : state.InferenceReady)
    (scheme : Scheme) (type : Ty)
    (metavariable : TypeVarId)
    (occurs : metavariable ∈ (state.resolve
      ((scheme.instantiateWithSubstitution state.inference.next).substitution.apply type)).freeVariables) :
    (∃ source, source ∈ type.freeVariables ∧ source ∉ scheme.quantified ∧
      metavariable ∈ (state.resolve (.variable source)).freeVariables) ∨
    (state.inference.next ≤ metavariable.index ∧
      metavariable.index < (scheme.instantiateWithSubstitution state.inference.next).next) := by
  let instantiated := scheme.instantiateWithSubstitution state.inference.next
  change metavariable ∈ (state.inference.substitution.apply
    (instantiated.substitution.apply type)).freeVariables at occurs
  rw [← Substitution.compose_apply] at occurs
  obtain ⟨source, sourceMember, image⟩ := apply_variable_origin _ _ _ occurs
  rw [Substitution.compose_apply] at image
  cases found : instantiated.substitution.lookup? source with
  | none =>
    apply Or.inl
    refine ⟨source, sourceMember, ?_, ?_⟩
    · intro quantified
      exact ((Substitution.lookup?_eq_none_iff_not_mem_domain _ _).mp found)
        (Scheme.instantiateWithSubstitution_substitution_domain_covers scheme state.inference.next quantified)
    · simpa only [State.resolve, InferState.resolve, Substitution.apply, found, Option.getD_none] using image
  | some replacement =>
    obtain ⟨fresh, replacementEq, lower, upper⟩ :=
      Scheme.instantiateWithSubstitution_substitution_range_fresh scheme
        state.inference.next (Substitution.lookup?_eq_some_mem found)
    have same : metavariable = fresh := by
      change metavariable ∈ (state.resolve (instantiated.substitution.apply (.variable source))).freeVariables at image
      rw [Substitution.apply, found, Option.getD_some, replacementEq,
        resolve_fresh_variable ready fresh lower] at image
      simpa only [Ty.freeVariables, List.mem_singleton] using image
    subst metavariable
    exact Or.inr ⟨lower, upper⟩

private theorem safe_instantiated_type {protectedVars : List TypeVarId} {state : State}
    (ready : state.InferenceReady)
    (bound : ∀ metavariable ∈ protectedVars, metavariable.index < state.inference.next)
    (scheme : Scheme) (type : Ty)
    (sourceSafe : ∀ metavariable ∈ type.freeVariables,
      metavariable ∉ scheme.quantified → Safe protectedVars state (.variable metavariable)) :
    Safe protectedVars state
      ((scheme.instantiateWithSubstitution state.inference.next).substitution.apply type) := by
  intro metavariable member protectedMember
  rcases instantiated_variable_origin ready scheme type metavariable member with old | fresh
  · obtain ⟨source, sourceMember, outside, image⟩ := old
    exact sourceSafe source sourceMember outside metavariable image protectedMember
  · exact (Nat.not_lt.mpr fresh.1) (bound metavariable protectedMember)

private theorem instantiated_predicate_safe {protectedVars : List TypeVarId} {state : State}
    (ready : state.InferenceReady)
    (bound : ∀ metavariable ∈ protectedVars, metavariable.index < state.inference.next)
    (scheme : Scheme) (predicate : ProgramPredicate)
    (sourceSafe : ∀ type ∈ predicate.subject :: predicate.arguments,
      ∀ metavariable ∈ type.freeVariables,
        metavariable ∉ scheme.quantified → Safe protectedVars state (.variable metavariable)) :
    PredicateSafe protectedVars (instantiatedState state scheme)
      (Detail.applyPredicate (instantiatedState state scheme)
        (TypedTraitResolution.applySubstitution
          (scheme.instantiateWithSubstitution state.inference.next).substitution predicate)) := by
  have each (type : Ty) (member : type ∈ predicate.subject :: predicate.arguments) :
      Safe protectedVars (instantiatedState state scheme)
        (state.resolve ((scheme.instantiateWithSubstitution state.inference.next).substitution.apply type)) :=
    instantiate_transport _ _ _ _ (safe_resolved ready
      (safe_instantiated_type ready bound scheme type (sourceSafe type member)))
  intro type member
  change type ∈ state.resolve ((scheme.instantiateWithSubstitution state.inference.next).substitution.apply predicate.subject) ::
    (predicate.arguments.map (scheme.instantiateWithSubstitution state.inference.next).substitution.apply).map state.resolve at member
  rcases List.mem_cons.mp member with rfl | argument
  · exact each _ (by simp)
  · obtain ⟨instantiated, instMember, rfl⟩ := List.mem_map.mp argument
    obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp instMember
    exact each original (List.mem_cons.mpr (.inr originalMember))

private theorem local_instantiation_safe {protectedVars : List TypeVarId} {state : State}
    {binder : TypedBinder} (ready : state.InferenceReady)
    (bound : ∀ metavariable ∈ protectedVars, metavariable.index < state.inference.next)
    (safe : BinderSafe protectedVars state binder) :
    SafeTransport protectedVars state (instantiatedState state binder.scheme) ∧
    Safe protectedVars (instantiatedState state binder.scheme)
      ((instantiatedState state binder.scheme).resolve
        (binder.scheme.instantiateWithSubstitution state.inference.next).body) ∧
    ∀ predicate ∈ binder.schemeRequirements.map (fun requirement =>
      Detail.applyPredicate (instantiatedState state binder.scheme)
        (TypedTraitResolution.applySubstitution
          (binder.scheme.instantiateWithSubstitution state.inference.next).substitution requirement.predicate)),
      PredicateSafe protectedVars (instantiatedState state binder.scheme) predicate := by
  refine ⟨instantiate_transport _ _ _, ?_, ?_⟩
  · apply instantiate_transport protectedVars state binder.scheme
    apply safe_resolved ready
    apply safe_instantiated_type ready bound binder.scheme binder.scheme.body
    intro v member outside
    exact safe.body v (List.mem_filter.mpr ⟨member, by simp [outside]⟩)
  · intro predicate member
    obtain ⟨requirement, requirementMember, rfl⟩ := List.mem_map.mp member
    exact instantiated_predicate_safe ready bound binder.scheme requirement.predicate
      (safe.requirements requirement requirementMember)

private theorem lookup_instantiation_safe {protectedVars : List TypeVarId} {state : State}
    {name : String} {binder : TypedBinder} (ready : state.InferenceReady)
    (bound : ∀ metavariable ∈ protectedVars, metavariable.index < state.inference.next)
    (safe : LiveBindersSafe protectedVars state)
    (found : state.lookupBinder? name = some binder) :
    SafeTransport protectedVars state (instantiatedState state binder.scheme) ∧
    Safe protectedVars (instantiatedState state binder.scheme)
      ((instantiatedState state binder.scheme).resolve
        (binder.scheme.instantiateWithSubstitution state.inference.next).body) ∧
    ∀ predicate ∈ binder.schemeRequirements.map (fun requirement =>
      Detail.applyPredicate (instantiatedState state binder.scheme)
        (TypedTraitResolution.applySubstitution
          (binder.scheme.instantiateWithSubstitution state.inference.next).substitution requirement.predicate)),
      PredicateSafe protectedVars (instantiatedState state binder.scheme) predicate :=
  local_instantiation_safe ready bound
    (safe binder (State.lookupBinder?_eq_some_facts found).1)

theorem inferExprFuel_local_private
    {protectedVars : List TypeVarId} {fuel : Nat} {context : SourceInference.Context}
    {expression : Syntax.Expr} {initial allocated : State} {id : ExpressionId}
    {name : Syntax.Identifier} {binder : TypedBinder} {expected : Option Ty}
    {result : InferredExpression × State}
    (catalog : SignatureCatalogWellFormed context.signatures)
    (form : expression.value = .identifier name)
    (allocation : initial.allocateExpressionId = (id, allocated))
    (found : allocated.lookupBinder? name.value = some binder)
    (accepted : Detail.inferExprFuel (fuel + 1) context expression expected initial = .ok result)
    (ready : initial.InferenceReady)
    (bound : ∀ metavariable ∈ protectedVars, metavariable.index < initial.inference.next)
    (live : LiveBindersSafe protectedVars initial)
    (expectedBelow : ∀ type ∈ expected, type.VariablesBelow initial.inference.next)
    (expectedSafe : ∀ type ∈ expected, Safe protectedVars initial type) :
    SafeTransport protectedVars initial result.2 ∧
    Safe protectedVars result.2 result.1.type ∧
    LiveBindersSafe protectedVars result.2 ∧
    ∀ row ∈ result.2.requirements, row ∉ initial.requirements →
      PredicateSafe protectedVars result.2 row.predicate := by
  have allocatedEq : allocated = initial.allocateExpressionId.2 := (congrArg Prod.snd allocation).symm
  have readyAllocated : allocated.InferenceReady := by
    rw [allocatedEq]
    exact ⟨ready.solved, ready.bindersBelow⟩
  have boundAllocated : ∀ metavariable ∈ protectedVars, metavariable.index < allocated.inference.next := by
    intro metavariable member
    rw [allocatedEq]
    exact bound metavariable member
  have allocationTransport : SafeTransport protectedVars initial allocated := by
    apply SafeTransport.of_substitution_eq
    rw [allocatedEq]
    rfl
  have liveAllocated : LiveBindersSafe protectedVars allocated := by
    apply live.transport _ allocationTransport
    rw [allocatedEq]
    rfl
  have privacy := lookup_instantiation_safe readyAllocated boundAllocated liveAllocated found
  have inference := Detail.localBinderInstantiation_inferenceProperties readyAllocated found
  let advanced := instantiatedState allocated binder.scheme
  let predicates := binder.schemeRequirements.map fun requirement =>
    Detail.applyPredicate advanced
      (TypedTraitResolution.applySubstitution
        (binder.scheme.instantiateWithSubstitution allocated.inference.next).substitution requirement.predicate)
  let recorded := (advanced.addRequirementsWithIds predicates).2
  have advancedReady : advanced.InferenceReady := inference.2.1
  have recordedReady : recorded.InferenceReady :=
    State.InferenceReady.addRequirementsWithIds predicates advancedReady
  have sameInference : recorded.inference = advanced.inference := requirementBatch_inference _ _
  have sameBinders : recorded.localBinders = initial.localBinders := by
    rw [requirementBatch_binders]
    change allocated.localBinders = initial.localBinders
    rw [allocatedEq]
    rfl
  have beforeFit : SafeTransport protectedVars initial recorded := by
    apply SafeTransport.of_substitution_eq
    rw [sameInference]
    change allocated.inference.substitution = initial.inference.substitution
    rw [allocatedEq]
    rfl
  have nextBound : initial.inference.next ≤ recorded.inference.next := by
    rw [sameInference]
    have sameNext : allocated.inference.next = initial.inference.next := by
      rw [allocatedEq]
      rfl
    rw [← sameNext]
    exact inference.1.next_le
  have typeBelow : (advanced.resolve
      (binder.scheme.instantiateWithSubstitution allocated.inference.next).body).VariablesBelow
        recorded.inference.next := by
    rw [sameInference]
    exact inference.2.2
  have typeSafe : Safe protectedVars recorded (advanced.resolve
      (binder.scheme.instantiateWithSubstitution allocated.inference.next).body) := by
    simpa only [Safe, State.resolve, InferState.resolve, sameInference] using privacy.2.1
  have recordAccepted := Detail.inferExprFuel_success_localIdentifier_record form allocation found accepted
  change Detail.recordExpressionWithExpected context expression id
    (advanced.resolve (binder.scheme.instantiateWithSubstitution allocated.inference.next).body)
    (.reference name.value (.local binder.id)) (advanced.addRequirementsWithIds predicates).1 expected
    recorded (some allocated.inference.next) = .ok result at recordAccepted
  have tail := recordExpressionWithExpected_private catalog recordedReady typeBelow
    (fun type member => (expectedBelow type member).weaken nextBound) typeSafe
    (fun type member => beforeFit type (expectedSafe type member))
    (live.transport sameBinders beforeFit) recordAccepted
  refine ⟨beforeFit.trans tail.1, tail.2.1, tail.2.2.1, ?_⟩
  intro row member fresh
  by_cases earlier : row ∈ recorded.requirements
  · rcases requirementBatch_row_origin advanced predicates earlier with old | issued
    · apply False.elim
      apply fresh
      change row ∈ allocated.requirements at old
      rw [allocatedEq] at old
      exact old
    · intro type typeMember
      apply tail.1
      have safe := privacy.2.2 row.predicate issued type typeMember
      simpa only [Safe, State.resolve, InferState.resolve, sameInference] using safe
  · exact tail.2.2.2 row member earlier

end Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables.UnrestrictedLocalLookup
