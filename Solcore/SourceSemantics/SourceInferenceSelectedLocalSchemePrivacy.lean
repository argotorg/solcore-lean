import Solcore.SourceSemantics.SourceInferenceProtectedVariables

set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceSoundness
open Frontend Frontend.SourceInference TypeSystem
namespace ProtectedVariables

/-- Every variable in a substituted type comes from the substituted image of
one variable that occurred in the original type. -/
theorem apply_variable_origin (substitution : Substitution) (type : Ty)
    (metavariable : TypeVarId)
    (occurs : metavariable ∈ (substitution.apply type).freeVariables) :
    ∃ source, source ∈ type.freeVariables ∧
      metavariable ∈ (substitution.apply (.variable source)).freeVariables := by
  induction type with
  | «variable» source => exact ⟨source, by simp [Ty.freeVariables], occurs⟩
  | parameter _ => simp [Substitution.apply, Ty.freeVariables] at occurs
  | constructor _ => simp [Substitution.apply, Ty.freeVariables] at occurs
  | error => simp [Substitution.apply, Ty.freeVariables] at occurs
  | proxy inner induction => exact induction occurs
  | comptime inner induction => exact induction occurs
  | application left right leftIH rightIH =>
    rcases (Ty.mem_freeVariables_application_iff _ _ _).mp occurs with h | h
    · obtain ⟨v, member, image⟩ := leftIH h
      exact ⟨v, (Ty.mem_freeVariables_application_iff _ _ _).mpr (.inl member), image⟩
    · obtain ⟨v, member, image⟩ := rightIH h
      exact ⟨v, (Ty.mem_freeVariables_application_iff _ _ _).mpr (.inr member), image⟩
  | function left right leftIH rightIH =>
    rcases (Ty.mem_freeVariables_function_iff _ _ _).mp occurs with h | h
    · obtain ⟨v, member, image⟩ := leftIH h
      exact ⟨v, (Ty.mem_freeVariables_function_iff _ _ _).mpr (.inl member), image⟩
    · obtain ⟨v, member, image⟩ := rightIH h
      exact ⟨v, (Ty.mem_freeVariables_function_iff _ _ _).mpr (.inr member), image⟩
  | product left right leftIH rightIH =>
    rcases (Ty.mem_freeVariables_product_iff _ _ _).mp occurs with h | h
    · obtain ⟨v, member, image⟩ := leftIH h
      exact ⟨v, (Ty.mem_freeVariables_product_iff _ _ _).mpr (.inl member), image⟩
    · obtain ⟨v, member, image⟩ := rightIH h
      exact ⟨v, (Ty.mem_freeVariables_product_iff _ _ _).mpr (.inr member), image⟩
  | mapping left right leftIH rightIH =>
    rcases (Ty.mem_freeVariables_mapping_iff _ _ _).mp occurs with h | h
    · obtain ⟨v, member, image⟩ := leftIH h
      exact ⟨v, (Ty.mem_freeVariables_mapping_iff _ _ _).mpr (.inl member), image⟩
    · obtain ⟨v, member, image⟩ := rightIH h
      exact ⟨v, (Ty.mem_freeVariables_mapping_iff _ _ _).mpr (.inr member), image⟩

/-- The current solved substitution cannot rewrite variables allocated after
its own allocation bound. -/
theorem resolve_fresh_variable {state : State} (ready : state.InferenceReady)
    (metavariable : TypeVarId) (fresh : state.inference.next ≤ metavariable.index) :
    state.resolve (.variable metavariable) = .variable metavariable := by
  have absent : metavariable ∉ state.inference.substitution.domain := by
    intro member
    exact (Nat.not_lt.mpr fresh) (ready.solved.domain_below _ member)
  have found := (Substitution.lookup?_eq_none_iff_not_mem_domain _ _).mpr absent
  simp [State.resolve, InferState.resolve, Substitution.apply, found]

/-- Local scheme instantiation exposes only an unquantified source variable's
resolved image or a variable from this allocation. This also applies to the
scheme's associated predicates. -/
theorem instantiated_variable_origin {state : State} (ready : state.InferenceReady)
    (scheme : Scheme) (unique : scheme.quantified.Nodup) (type : Ty)
    (metavariable : TypeVarId)
    (occurs : metavariable ∈ (state.resolve
      ((scheme.instantiateWithSubstitution state.inference.next).substitution.apply type)).freeVariables) :
    (∃ source, source ∈ type.freeVariables ∧ source ∉ scheme.quantified ∧
      metavariable ∈ (state.resolve (.variable source)).freeVariables) ∨
    (state.inference.next ≤ metavariable.index ∧
      metavariable.index < (scheme.instantiateWithSubstitution state.inference.next).next) := by
  let instantiated := scheme.instantiateWithSubstitution state.inference.next
  have domain := Scheme.instantiateWithSubstitution_substitution_domain_permutation
    scheme state.inference.next unique
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
        (domain.mem_iff.mpr quantified)
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

/-- Privacy depends on live unquantified variables, never on dead substitution
entries or on the bound variables in a stored polymorphic scheme. -/
structure BinderSafe (protectedVars : List TypeVarId) (state : State)
    (binder : TypedBinder) : Prop where
  body : ∀ metavariable ∈ binder.scheme.freeVariables,
    Safe protectedVars state (.variable metavariable)
  requirements : ∀ requirement ∈ binder.schemeRequirements,
    ∀ type ∈ requirement.predicate.subject :: requirement.predicate.arguments,
      ∀ metavariable ∈ type.freeVariables, metavariable ∉ binder.scheme.quantified →
        Safe protectedVars state (.variable metavariable)

def LiveBindersSafe (protectedVars : List TypeVarId) (state : State) : Prop :=
  ∀ binder ∈ state.localBinders, BinderSafe protectedVars state binder

theorem safe_instantiated_type {protectedVars : List TypeVarId} {state : State}
    (ready : state.InferenceReady)
    (bound : ∀ metavariable ∈ protectedVars, metavariable.index < state.inference.next)
    (scheme : Scheme) (unique : scheme.quantified.Nodup) (type : Ty)
    (sourceSafe : ∀ metavariable ∈ type.freeVariables,
      metavariable ∉ scheme.quantified → Safe protectedVars state (.variable metavariable)) :
    Safe protectedVars state
      ((scheme.instantiateWithSubstitution state.inference.next).substitution.apply type) := by
  intro metavariable member protectedMember
  rcases instantiated_variable_origin ready scheme unique type metavariable member with old | fresh
  · obtain ⟨source, sourceMember, outside, image⟩ := old
    exact sourceSafe source sourceMember outside metavariable image protectedMember
  · exact (Nat.not_lt.mpr fresh.1) (bound metavariable protectedMember)

theorem BinderSafe.transport {protectedVars : List TypeVarId} {before after : State}
    {binder : TypedBinder} (safe : BinderSafe protectedVars before binder)
    (transport : SafeTransport protectedVars before after) :
    BinderSafe protectedVars after binder := by
  constructor
  · intro v member
    exact transport _ (safe.body v member)
  · intro requirement member type typeMember v occurs outside
    exact transport _ (safe.requirements requirement member type typeMember v occurs outside)

theorem LiveBindersSafe.transport {protectedVars : List TypeVarId} {before after : State}
    (safe : LiveBindersSafe protectedVars before)
    (same : after.localBinders = before.localBinders)
    (transport : SafeTransport protectedVars before after) :
    LiveBindersSafe protectedVars after := by
  intro binder member
  exact (safe binder (same ▸ member)).transport transport

theorem LiveBindersSafe.unify {protectedVars : List TypeVarId} {before after : State}
    {left right : Ty} (safe : LiveBindersSafe protectedVars before)
    (leftSafe : Safe protectedVars before left)
    (rightSafe : Safe protectedVars before right)
    (accepted : Detail.unify before left right = .ok after) :
    LiveBindersSafe protectedVars after := by
  apply safe.transport _ (ProtectedVariables.unify leftSafe rightSafe accepted)
  unfold Detail.unify at accepted
  cases unified : before.inference.unify left right with
  | error error => simp [unified, Detail.liftUnification, bind, Except.bind] at accepted
  | ok inference =>
    simp only [unified, Detail.liftUnification, bind, Except.bind, pure, Pure.pure, Except.pure] at accepted
    cases accepted
    rfl

/-- The allocator-only update used by the actual local identifier branch. -/
def instantiatedState (state : State) (scheme : Scheme) : State :=
  { state with inference := { state.inference with
      next := (scheme.instantiateWithSubstitution state.inference.next).next } }

theorem instantiate_transport (protectedVars : List TypeVarId) (state : State)
    (scheme : Scheme) : SafeTransport protectedVars state (instantiatedState state scheme) :=
  .of_substitution_eq rfl

def PredicateSafe (protectedVars : List TypeVarId) (state : State)
    (predicate : ProgramPredicate) : Prop :=
  ∀ type ∈ predicate.subject :: predicate.arguments, Safe protectedVars state type

theorem instantiated_predicate_safe {protectedVars : List TypeVarId} {state : State}
    (ready : state.InferenceReady)
    (bound : ∀ metavariable ∈ protectedVars, metavariable.index < state.inference.next)
    (scheme : Scheme) (unique : scheme.quantified.Nodup) (predicate : ProgramPredicate)
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
      (safe_instantiated_type ready bound scheme unique type (sourceSafe type member)))
  intro type member
  change type ∈ state.resolve ((scheme.instantiateWithSubstitution state.inference.next).substitution.apply predicate.subject) ::
    (predicate.arguments.map (scheme.instantiateWithSubstitution state.inference.next).substitution.apply).map state.resolve at member
  rcases List.mem_cons.mp member with rfl | argument
  · exact each _ (by simp)
  · obtain ⟨instantiated, instMember, rfl⟩ := List.mem_map.mp argument
    obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp instMember
    exact each original (List.mem_cons.mpr (.inr originalMember))

/-- Both the returned type and every reissued scheme predicate remain private
through the exact allocator update and normalization of local lookup. -/
theorem local_instantiation_safe {protectedVars : List TypeVarId} {state : State}
    {binder : TypedBinder} (ready : state.InferenceReady)
    (bound : ∀ metavariable ∈ protectedVars, metavariable.index < state.inference.next)
    (unique : binder.scheme.quantified.Nodup) (safe : BinderSafe protectedVars state binder) :
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
    apply safe_instantiated_type ready bound binder.scheme unique binder.scheme.body
    intro v member outside
    exact safe.body v (List.mem_filter.mpr ⟨member, by simp [outside]⟩)
  · intro predicate member
    obtain ⟨requirement, requirementMember, rfl⟩ := List.mem_map.mp member
    exact instantiated_predicate_safe ready bound binder.scheme unique requirement.predicate
      (safe.requirements requirement requirementMember)

theorem lookup_instantiation_safe {protectedVars : List TypeVarId} {state : State}
    {name : String} {binder : TypedBinder} (ready : state.InferenceReady)
    (bound : ∀ metavariable ∈ protectedVars, metavariable.index < state.inference.next)
    (unique : binder.scheme.quantified.Nodup)
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
  local_instantiation_safe ready bound unique
    (safe binder (State.lookupBinder?_eq_some_facts found).1)

end ProtectedVariables
end Solcore.SourceSemantics.SourceInferenceSoundness
