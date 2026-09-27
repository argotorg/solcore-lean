import Solcore.TypeSystem.Inference

/-! Structural projection laws for reusable inference state operations. -/

set_option autoImplicit false

namespace Solcore.TypeSystem.InferState

@[simp] theorem fresh_substitution (state : InferState) :
    state.fresh.2.substitution = state.substitution := by
  rfl

@[simp] theorem fresh_next (state : InferState) :
    state.fresh.2.next = state.next + 1 := by
  rfl

@[simp] theorem instantiate_substitution (state : InferState)
    (scheme : Scheme) :
    (state.instantiate scheme).2.substitution = state.substitution := by
  simp [instantiate]

@[simp] theorem instantiateDeclaration_substitution (state : InferState)
    (scheme : DeclarationScheme) :
    (state.instantiateDeclaration scheme).2.substitution =
      state.substitution := by
  simp [instantiateDeclaration]

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

end Solcore.TypeSystem.InferState
