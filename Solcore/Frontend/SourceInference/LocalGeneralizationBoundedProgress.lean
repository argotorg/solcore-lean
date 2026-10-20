import Solcore.Frontend.SourceInference.LocalGeneralizationBoundaryReceipts

/-! A traversal distinguishes declarations already present on entry from the
new generalization events it creates. Only new events use the traversal's
allocator cutoff to justify restoring its saved outer lexical scope. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.Frontend.SourceInference.LocalGeneralizationBoundaries
open TypeSystem Detail
open LocalGeneralizationEvents (Ready)

def PriorStatement (nodes : List Node) (node : StatementNode) : Prop :=
  ∃ prior : StatementNode, .statement prior ∈ nodes ∧ prior.id = node.id ∧ prior.form = node.form

def Coverage (entry : State) (state : State) : Prop :=
  ∀ node : StatementNode, .statement node ∈ state.nodes →
    PriorStatement entry.nodes node ∨ StatementSince entry.nextLocal state node

structure Progress (before after : State) : Prop where
  reads : LocalReadEvents.Progress before after
  scope : LocalReadScopeProgress.Progress before after
  binders : before.LocalBindersBelowNextLocal → after.LocalBindersBelowNextLocal
  events : Ready before → before.LocalBindersBelowNextLocal → Coverage before after

namespace Progress

theorem of_retained {before after : State}
    (retained : ∀ node : StatementNode, .statement node ∈ after.nodes → PriorStatement before.nodes node)
    (reads : LocalReadEvents.Progress before after)
    (scope : LocalReadScopeProgress.Progress before after)
    (binders : before.LocalBindersBelowNextLocal → after.LocalBindersBelowNextLocal) : Progress before after :=
  ⟨reads, scope, binders, fun _ _ node member => .inl (retained node member)⟩

theorem refl (state : State) : Progress state state := by
  refine ⟨LocalReadEvents.Progress.refl _, LocalReadScopeProgress.Progress.refl _, fun below => below, ?_⟩
  intro _ _ node present
  exact .inl ⟨node, present, rfl, rfl⟩

theorem trans {before middle after : State} (first : Progress before middle) (second : Progress middle after) :
    Progress before after := by
  refine ⟨first.reads.trans second.reads, first.scope.trans second.scope,
    fun below => second.binders (first.binders below), ?_⟩
  intro ready below node present
  rcases second.events (ready.progress first.reads) (first.binders below) node present with old | fresh
  · obtain ⟨prior, member, sameId, sameForm⟩ := old
    rcases first.events ready below prior member with old | fresh
    · obtain ⟨original, present, originalId, originalForm⟩ := old
      exact .inl ⟨original, present, originalId.trans sameId, originalForm.trans sameForm⟩
    · exact .inr ((fresh.progress second.scope).same_form sameForm.symm)
  · exact .inr (fresh.weaken first.scope.next)

/-- Existing entry nodes stay classified as entry nodes. New events carry the
entry cutoff, so scope restoration uses real earlier binder identities. -/
theorem restore {before state : State} (progress : Progress before state) (scope : LexicalScope)
    (saved : scope.binders ⊆ before.localBinders) : Progress before (state.restoreLexicalScope scope) := by
  refine ⟨progress.reads, progress.scope.restore saved, ?_, ?_⟩
  · intro below binder member
    exact Nat.lt_of_lt_of_le (below binder (saved member)) progress.scope.next
  · intro ready below node present
    rcases progress.events ready below node present with old | fresh
    · exact .inl old
    · exact .inr (fresh.restore_saved scope saved below (Nat.le_refl _))

theorem of_nodes_eq {before after : State}
    (nodes : after.nodes = before.nodes) (reads : LocalReadEvents.Progress before after)
    (scope : LocalReadScopeProgress.Progress before after)
    (binders : before.LocalBindersBelowNextLocal → after.LocalBindersBelowNextLocal) : Progress before after := by
  refine ⟨reads, scope, binders, ?_⟩
  intro _ _ node member
  exact .inl ⟨node, nodes ▸ member, rfl, rfl⟩

theorem recordStatement (state : State) (node : StatementNode)
    (event : StatementSince state.nextLocal state node) : Progress state (state.recordNode (.statement node)) := by
  refine ⟨LocalReadEvents.Progress.recordStatement _ _, LocalReadScopeProgress.Progress.recordStatement _ _,
    fun below => below, ?_⟩
  intro _ _ actual member
  rcases List.mem_append.mp member with old | fresh
  · exact .inl ⟨actual, old, rfl, rfl⟩
  · cases List.mem_singleton.mp fresh
    exact .inr (event.progress (LocalReadScopeProgress.Progress.recordStatement _ _))

/-- An append of an expression cannot introduce a declaration event. The
actual expression rule supplies its read ledger and binder-scope evidence. -/
theorem appendExpression {before after : State} (node : ExpressionNode)
    (nodes : after.nodes = before.nodes ++ [.expression node])
    (reads : LocalReadEvents.Progress before after)
    (scope : LocalReadScopeProgress.Progress before after)
    (binders : before.LocalBindersBelowNextLocal → after.LocalBindersBelowNextLocal) : Progress before after := by
  refine ⟨reads, scope, binders, ?_⟩
  intro _ _ statement present
  rw [nodes] at present
  rcases List.mem_append.mp present with old | fresh
  · exact .inl ⟨statement, old, rfl, rfl⟩
  · cases List.mem_singleton.mp fresh

/-- A genuine map which retains statement identity and form creates no new
generalization event; expression coercion changes are permitted. -/
theorem mapNodes {before after : State} (modify : Node → Node)
    (nodes : after.nodes = before.nodes.map modify)
    (statements : ∀ source target, modify source = .statement target →
      ∃ prior : StatementNode, source = .statement prior ∧ prior.id = target.id ∧ prior.form = target.form)
    (reads : LocalReadEvents.Progress before after)
    (scope : LocalReadScopeProgress.Progress before after)
    (binders : before.LocalBindersBelowNextLocal → after.LocalBindersBelowNextLocal) : Progress before after := by
  refine ⟨reads, scope, binders, ?_⟩
  intro _ _ statement present
  rw [nodes] at present
  obtain ⟨source, member, same⟩ := List.mem_map.mp present
  obtain ⟨prior, sourceForm, sameId, sameForm⟩ := statements source statement same
  exact .inl ⟨prior, sourceForm ▸ member, sameId, sameForm⟩

end Progress
end Solcore.Frontend.SourceInference.LocalGeneralizationBoundaries
