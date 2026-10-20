import Solcore.Frontend.SourceInference.LocalGeneralizationBoundedHelpers

/-! The completed traversal transports entry events and newly created events
through the same reached state, while retaining their separate allocator bounds. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.Frontend.SourceInference.LocalGeneralizationBoundaries
open TypeSystem Detail
open LocalGeneralizationEvents (Ready)

def OriginsSince (entry : Nat) (state : State) : Prop :=
  ∀ node : StatementNode, .statement node ∈ state.nodes → StatementSince entry state node

theorem OriginsSince.empty {entry : Nat} {state : State} (empty : state.nodes = []) : OriginsSince entry state := by
  intro _ member
  rw [empty] at member
  cases member

theorem Progress.origins {entry : Nat} {before after : State} (progress : Progress before after)
    (ready : Ready before) (below : before.LocalBindersBelowNextLocal) (entered : entry ≤ before.nextLocal)
    (origins : OriginsSince entry before) : OriginsSince entry after := by
  intro node present
  rcases progress.events ready below node present with old | fresh
  · obtain ⟨prior, member, _, sameForm⟩ := old
    exact ((origins prior member).progress progress.scope).same_form sameForm.symm
  · exact fresh.weaken entered

/-- An enclosing statement may aggregate initializer events that precede its
own recording. The existing traversal cutoff is retained for those events. -/
theorem Progress.recordAfter {before state : State} (progress : Progress before state)
    (node : StatementNode) (event : StatementSince before.nextLocal state node) :
    Progress before (state.recordNode (.statement node)) := by
  have step := LocalReadScopeProgress.Progress.recordStatement state node
  refine ⟨progress.reads.trans (LocalReadEvents.Progress.recordStatement _ _), progress.scope.trans step,
    progress.binders, ?_⟩
  intro ready below actual member
  rcases List.mem_append.mp member with old | fresh
  · rcases progress.events ready below actual old with old | fresh
    · exact .inl old
    · exact .inr (fresh.progress step)
  · cases Node.statement.inj (List.mem_singleton.mp fresh)
    exact .inr (event.progress step)

/-- At a genuine empty function entry all final events come from this traversal;
there are no pre-existing nodes whose origin could be assumed. -/
theorem Progress.empty_entry {before after : State} (progress : Progress before after)
    (ready : Ready before) (below : before.LocalBindersBelowNextLocal) (empty : before.nodes = []) :
    OriginsSince before.nextLocal after :=
  progress.origins ready below (Nat.le_refl _) (OriginsSince.empty empty)

end Solcore.Frontend.SourceInference.LocalGeneralizationBoundaries
