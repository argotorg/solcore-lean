import Solcore.TypeSystem.Inference

/-! Structural projection laws for reusable inference state operations. -/

set_option autoImplicit false

namespace Solcore.TypeSystem.InferState

/-- The inference allocator stays strictly above every variable mentioned by
its solved substitution. -/
def Solved (state : InferState) : Prop :=
  state.substitution.SolvedBelow state.next

@[simp] theorem fresh_substitution (state : InferState) :
    state.fresh.2.substitution = state.substitution := by
  rfl

@[simp] theorem fresh_next (state : InferState) :
    state.fresh.2.next = state.next + 1 := by
  rfl

/-- Scheme instantiation can only advance the state's allocator. -/
theorem instantiate_next_le (state : InferState) (scheme : Scheme) :
    state.next ≤ (state.instantiate scheme).2.next := by
  simpa [instantiate] using Scheme.instantiate_next_le scheme state.next

@[simp] theorem instantiate_substitution (state : InferState)
    (scheme : Scheme) :
    (state.instantiate scheme).2.substitution = state.substitution := by
  simp [instantiate]

@[simp] theorem instantiateDeclaration_substitution (state : InferState)
    (scheme : DeclarationScheme) :
    (state.instantiateDeclaration scheme).2.substitution =
      state.substitution := by
  simp [instantiateDeclaration]

/-- Declaration instantiation can only advance the state's allocator. -/
theorem instantiateDeclaration_next_le (state : InferState)
    (scheme : DeclarationScheme) :
    state.next ≤ (state.instantiateDeclaration scheme).2.next := by
  simpa [instantiateDeclaration] using
    DeclarationScheme.instantiate_next_le scheme state.next

theorem unify_next {state result : InferState} {left right : Ty}
    (success : state.unify left right = .ok result) :
    result.next = state.next := by
  unfold unify at success
  cases unified : Unification.unifyTypes (state.resolve left)
      (state.resolve right) <;>
    simp [unified, bind, Except.bind] at success
  cases success
  rfl

theorem solve_next {state result : InferState}
    {constraints : List Constraint}
    (success : state.solve constraints = .ok result) :
    result.next = state.next := by
  unfold solve at success
  cases unified : Unification.unify
      (constraints.map (Constraint.apply state.substitution)) <;>
    simp [unified, bind, Except.bind] at success
  cases success
  rfl

namespace Solved

/-- Every initial inference state has a solved empty substitution. -/
theorem initial (next : Nat := 0) : (InferState.initial next).Solved := by
  exact Substitution.SolvedBelow.empty next

/-- Allocating one fresh variable preserves the solved-state invariant. -/
theorem fresh {state : InferState} (solved : state.Solved) :
    state.fresh.2.Solved := by
  exact solved.weaken (Nat.le_succ state.next)

/-- Rank-1 scheme instantiation preserves the solved-state invariant. -/
theorem instantiate {state : InferState} (solved : state.Solved)
    (scheme : Scheme) :
    (state.instantiate scheme).2.Solved := by
  exact solved.weaken (InferState.instantiate_next_le state scheme)

/-- Declaration scheme instantiation preserves the solved-state invariant. -/
theorem instantiateDeclaration {state : InferState} (solved : state.Solved)
    (scheme : DeclarationScheme) :
    (state.instantiateDeclaration scheme).2.Solved := by
  exact solved.weaken
    (InferState.instantiateDeclaration_next_le state scheme)

/-- Successful binary unification preserves solved inference state when the
two types actually passed to the unifier lie below the allocator bound. -/
theorem unify
    {state result : InferState} {left right : Ty}
    (solved : state.Solved)
    (leftBelow : (state.resolve left).VariablesBelow state.next)
    (rightBelow : (state.resolve right).VariablesBelow state.next)
    (success : state.unify left right = .ok result) :
    result.Solved := by
  unfold InferState.unify at success
  cases unified : Unification.unifyTypes (state.resolve left)
      (state.resolve right) with
  | error error =>
      simp [unified, bind, Except.bind] at success
  | ok update =>
      simp [unified, bind, Except.bind] at success
      cases success
      apply (Unification.unifyTypes_solvedBelow leftBelow rightBelow
        unified).compose solved
      apply Unification.unifyTypes_rangeAvoidsDomain
      · simpa [InferState.resolve] using
          solved.apply_variables_outside_domain left
      · simpa [InferState.resolve] using
          solved.apply_variables_outside_domain right
      · exact unified

/-- Successful constraint solving preserves solved inference state when the
normalized constraints actually passed to the unifier lie below the allocator
bound. -/
theorem solve
    {state result : InferState} {constraints : List Constraint}
    (solved : state.Solved)
    (normalizedBelow : ConstraintsBelow state.next
      (constraints.map (·.apply state.substitution)))
    (success : state.solve constraints = .ok result) :
    result.Solved := by
  have normalizedOutside : ConstraintsOutsideDomain state.substitution
      (constraints.map (·.apply state.substitution)) := by
    intro constraint member
    rcases List.mem_map.mp member with
      ⟨source, sourceMember, sourceEq⟩
    subst constraint
    exact
      ⟨solved.apply_variables_outside_domain source.left,
        solved.apply_variables_outside_domain source.right⟩
  unfold InferState.solve at success
  cases unified : Unification.unify
      (constraints.map (·.apply state.substitution)) with
  | error error =>
      simp [unified, bind, Except.bind] at success
  | ok update =>
      simp [unified, bind, Except.bind] at success
      cases success
      apply (Unification.unify_solvedBelow normalizedBelow unified).compose solved
      exact Unification.unify_rangeAvoidsDomain normalizedOutside unified

end Solved

end Solcore.TypeSystem.InferState
