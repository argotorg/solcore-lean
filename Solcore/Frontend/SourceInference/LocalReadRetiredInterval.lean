import Solcore.Frontend.SourceInference.LocalReadScopeProgress

/-! Reads of locals retired by an initializer stay inside that initializer's
recorded nodes. Restoring an enclosing scope is justified by its actual ID
bound, even when that scope is no longer a subset of the current binders. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.Frontend.SourceInference.LocalReadScopeProgress

structure Barrier (low high : Nat) (readyNodes : List Node) (state : State) : Prop where
  allocated : high ≤ state.nextLocal
  absent : ∀ id : Resolved.LocalId, low ≤ id.binderIndex → id.binderIndex < high →
    Absent id state.localBinders
  reads : ∀ id : Resolved.LocalId, low ≤ id.binderIndex → id.binderIndex < high →
    ReadsFrom id readyNodes state.nodes

namespace Barrier

theorem progress {low high : Nat} {readyNodes : List Node} {before after : State}
    (barrier : Barrier low high readyNodes before) (step : Progress before after) :
    Barrier low high readyNodes after := by
  refine ⟨Nat.le_trans barrier.allocated step.next, ?_, ?_⟩
  · intro id lower upper
    exact step.absent id (Nat.lt_of_lt_of_le upper barrier.allocated)
      (barrier.absent id lower upper)
  · intro id lower upper occurrence read
    exact barrier.reads id lower upper occurrence
      (step.reads id (Nat.lt_of_lt_of_le upper barrier.allocated)
        (barrier.absent id lower upper) occurrence read)

theorem restore {low high : Nat} {readyNodes : List Node} {state : State}
    (barrier : Barrier low high readyNodes state) (scope : LexicalScope)
    (absent : ∀ id : Resolved.LocalId, low ≤ id.binderIndex → id.binderIndex < high →
      Absent id scope.binders) :
    Barrier low high readyNodes (state.restoreLexicalScope scope) :=
  ⟨barrier.allocated, absent, barrier.reads⟩

theorem restore_below {low high : Nat} {readyNodes : List Node} {state : State}
    (barrier : Barrier low high readyNodes state) (scope : LexicalScope)
    (below : ∀ binder ∈ scope.binders, binder.id.binderIndex < low) :
    Barrier low high readyNodes (state.restoreLexicalScope scope) := by
  apply barrier.restore scope
  intro id lower _ binder present same
  have upper := below binder present
  rw [same] at upper
  omega

theorem restore_saved {low high : Nat} {readyNodes : List Node} {state initial : State}
    (barrier : Barrier low high readyNodes state) (scope : LexicalScope)
    (saved : scope.binders ⊆ initial.localBinders)
    (below : initial.LocalBindersBelowNextLocal) (entered : initial.nextLocal ≤ low) :
    Barrier low high readyNodes (state.restoreLexicalScope scope) := by
  apply barrier.restore_below scope
  intro binder present
  exact Nat.lt_of_lt_of_le (below binder (saved present)) entered

theorem of_unchanged {low high : Nat} {readyNodes : List Node} {before after : State}
    (barrier : Barrier low high readyNodes before)
    (next : before.nextLocal ≤ after.nextLocal)
    (binders : after.localBinders = before.localBinders)
    (nodes : after.nodes = before.nodes) : Barrier low high readyNodes after :=
  barrier.progress (Progress.of_unchanged next binders nodes)

theorem read {low high : Nat} {readyNodes : List Node} {state : State}
    (barrier : Barrier low high readyNodes state) {id : Resolved.LocalId}
    (lower : low ≤ id.binderIndex) (upper : id.binderIndex < high)
    {node : ExpressionNode} (member : .expression node ∈ state.nodes)
    {name : String} (form : node.form = .reference name (.local id)) :
    ReadAt readyNodes node.id id :=
  barrier.reads id lower upper node.id ⟨node, member, rfl, name, form⟩

end Barrier
end Solcore.Frontend.SourceInference.LocalReadScopeProgress
