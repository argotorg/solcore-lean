import Solcore.Frontend.SourceInference.LocalGeneralizationEvents
import Solcore.Frontend.SourceInference.LocalReadRetiredInterval

/-! Generalization events retain an interval of initializer-local identities.
The final state is explicit: later reads of a retired initializer local must
come from the recorded initializer, including across saved scope restoration. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.Frontend.SourceInference.LocalGeneralizationBoundaries
open TypeSystem Detail
open LocalGeneralizationEvents (Ready)
open LocalReadScopeProgress (Barrier Progress)

/-- Both event constructors retain the actual initializer entry, return state,
annotation resolution and generalization cutoff. -/
inductive Boundary : TypedBinder → ExpressionId → Nat → Nat → List Node → Prop where
  | statement {fuel context source initial result}
      (receipt : LocalLetRequirementTiming.Receipt fuel context source initial result)
      (ready : Ready initial) (below : initial.LocalBindersBelowNextLocal) :
      Boundary receipt.binding.1 receipt.value.id initial.nextLocal receipt.ready.nextLocal receipt.ready.nodes
  | header {fuel context source initial result}
      (receipt : LocalHeaderRequirementTiming.Receipt fuel context source initial result)
      (ready : Ready initial) (below : initial.LocalBindersBelowNextLocal) :
      Boundary receipt.binding.1 receipt.value.id initial.nextLocal receipt.ready.nextLocal receipt.ready.nodes

/-- The event occurred after a real traversal entry boundary. This lower bound
justifies restoring outer binders saved before the event's initializer. -/
def OriginSince (entry : Nat) (state : State) (binder : TypedBinder) (initializer : ExpressionId) : Prop :=
  ∃ low high nodes, entry ≤ low ∧ Boundary binder initializer low high nodes ∧ Barrier low high nodes state

def ItemSince (entry : Nat) (state : State) (item : ForItemForm) : Prop :=
  ∀ binder initializer, item = .letDecl binder (some initializer) → OriginSince entry state binder initializer

def ItemsSince (entry : Nat) (state : State) (items : List ForItemForm) : Prop :=
  ∀ item ∈ items, ItemSince entry state item

def StatementSince (entry : Nat) (state : State) (node : StatementNode) : Prop :=
  match node.form with
  | .letDecl binder (some initializer) => OriginSince entry state binder initializer
  | .forLoop initial _ post _ => ItemsSince entry state initial ∧ ItemsSince entry state post
  | _ => True

namespace OriginSince

theorem weaken {entry earlier : Nat} {state : State} {binder : TypedBinder} {initializer : ExpressionId}
    (origin : OriginSince entry state binder initializer) (before : earlier ≤ entry) :
    OriginSince earlier state binder initializer := by
  obtain ⟨low, high, nodes, entered, event, barrier⟩ := origin
  exact ⟨low, high, nodes, Nat.le_trans before entered, event, barrier⟩

theorem progress {entry : Nat} {before after : State} {binder : TypedBinder} {initializer : ExpressionId}
    (origin : OriginSince entry before binder initializer) (step : Progress before after) :
    OriginSince entry after binder initializer := by
  obtain ⟨low, high, nodes, entered, event, barrier⟩ := origin
  exact ⟨low, high, nodes, entered, event, barrier.progress step⟩

/-- The exact saved scope is checked against the actual entry allocator bound;
it need not still be a subset of the current binder stack. -/
theorem restore_saved {entry : Nat} {state initial : State} {binder : TypedBinder} {initializer : ExpressionId}
    (origin : OriginSince entry state binder initializer) (scope : LexicalScope)
    (saved : scope.binders ⊆ initial.localBinders) (below : initial.LocalBindersBelowNextLocal)
    (entered : initial.nextLocal ≤ entry) :
    OriginSince entry (state.restoreLexicalScope scope) binder initializer := by
  obtain ⟨low, high, nodes, later, event, barrier⟩ := origin
  exact ⟨low, high, nodes, later, event,
    barrier.restore_saved scope saved below (Nat.le_trans entered later)⟩

/-- Erasing the continuation evidence preserves the genuine inference event. -/
theorem origin {entry : Nat} {state : State} {binder : TypedBinder} {initializer : ExpressionId}
    (bounded : OriginSince entry state binder initializer) : LocalGeneralizationEvents.Origin binder initializer := by
  obtain ⟨low, high, nodes, _, event, _⟩ := bounded
  cases event with
  | statement receipt ready _ => exact .statement receipt ready
  | header receipt ready _ => exact .header receipt ready

end OriginSince

namespace ItemSince

theorem progress {entry : Nat} {before after : State} {item : ForItemForm}
    (origin : ItemSince entry before item) (step : Progress before after) : ItemSince entry after item :=
  fun _ _ same => (origin _ _ same).progress step

theorem weaken {entry earlier : Nat} {state : State} {item : ForItemForm}
    (origin : ItemSince entry state item) (before : earlier ≤ entry) : ItemSince earlier state item :=
  fun _ _ same => (origin _ _ same).weaken before

theorem restore_saved {entry : Nat} {state initial : State} {item : ForItemForm}
    (origin : ItemSince entry state item) (scope : LexicalScope)
    (saved : scope.binders ⊆ initial.localBinders) (below : initial.LocalBindersBelowNextLocal)
    (entered : initial.nextLocal ≤ entry) : ItemSince entry (state.restoreLexicalScope scope) item :=
  fun _ _ same => (origin _ _ same).restore_saved scope saved below entered

end ItemSince

namespace ItemsSince

theorem progress {entry : Nat} {before after : State} {items : List ForItemForm}
    (origin : ItemsSince entry before items) (step : Progress before after) : ItemsSince entry after items :=
  fun _ member => (origin _ member).progress step

theorem weaken {entry earlier : Nat} {state : State} {items : List ForItemForm}
    (origin : ItemsSince entry state items) (before : earlier ≤ entry) : ItemsSince earlier state items :=
  fun _ member => (origin _ member).weaken before

theorem restore_saved {entry : Nat} {state initial : State} {items : List ForItemForm}
    (origin : ItemsSince entry state items) (scope : LexicalScope)
    (saved : scope.binders ⊆ initial.localBinders) (below : initial.LocalBindersBelowNextLocal)
    (entered : initial.nextLocal ≤ entry) : ItemsSince entry (state.restoreLexicalScope scope) items :=
  fun _ member => (origin _ member).restore_saved scope saved below entered

end ItemsSince

namespace StatementSince

theorem progress {entry : Nat} {before after : State} {node : StatementNode}
    (origin : StatementSince entry before node) (step : Progress before after) : StatementSince entry after node := by
  unfold StatementSince at *
  split at origin
  · exact origin.progress step
  · exact ⟨origin.1.progress step, origin.2.progress step⟩
  · trivial

theorem weaken {entry earlier : Nat} {state : State} {node : StatementNode}
    (origin : StatementSince entry state node) (before : earlier ≤ entry) : StatementSince earlier state node := by
  unfold StatementSince at *
  split at origin
  · exact origin.weaken before
  · exact ⟨origin.1.weaken before, origin.2.weaken before⟩
  · trivial

theorem restore_saved {entry : Nat} {state initial : State} {node : StatementNode}
    (origin : StatementSince entry state node) (scope : LexicalScope)
    (saved : scope.binders ⊆ initial.localBinders) (below : initial.LocalBindersBelowNextLocal)
    (entered : initial.nextLocal ≤ entry) : StatementSince entry (state.restoreLexicalScope scope) node := by
  unfold StatementSince at *
  split at origin
  · exact origin.restore_saved scope saved below entered
  · exact ⟨origin.1.restore_saved scope saved below entered, origin.2.restore_saved scope saved below entered⟩
  · trivial

theorem same_form {entry : Nat} {state : State} {before after : StatementNode}
    (origin : StatementSince entry state before) (same : after.form = before.form) :
    StatementSince entry state after := by
  unfold StatementSince
  rw [same]
  exact origin

end StatementSince
end Solcore.Frontend.SourceInference.LocalGeneralizationBoundaries
