import Solcore.Frontend.SourceInference.LocalGeneralizationBoundedProgress

/-! Initialized statements and header items close their actual initializer
traversal. Earlier events and nested events remain distinct when the new
binder is allocated and its enclosing statement is recorded. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.Frontend.SourceInference.LocalGeneralizationBoundaries
open TypeSystem Detail
open LocalGeneralizationEvents (Ready)

namespace Progress

theorem initializedStatement {fuel : Nat} {context : Context} {statement : Syntax.Statement}
    {initial : State} {result : StatementResult} {expected : Ty}
    (receipt : LocalLetRequirementTiming.Receipt fuel context statement initial result)
    (accepted : inferStatementFuel (fuel + 1) context statement expected initial = .ok result)
    (child : Progress initial.allocateStatementId.2 receipt.ready) : Progress initial result.state := by
  have suffix : LocalReadScopeProgress.Progress receipt.ready result.state := by
    rw [congrArg StatementResult.state receipt.completed]
    exact (LocalReadScopeProgress.Progress.allocateBinder (receipt.ready.withLocals receipt.locals)
      receipt.name.value receipt.generalized.scheme (some receipt.name.span) false receipt.generalized.requirements).trans
        (LocalReadScopeProgress.Progress.recordStatement _ _)
  refine ⟨LocalReadEvents.inferStatementFuel_origins_progress accepted,
    child.scope.trans suffix, ?_, ?_⟩
  · intro below
    have readyBelow := child.binders below
    rw [congrArg StatementResult.state receipt.completed]
    exact State.allocateBinder_preserves_localBindersBelowNextLocal _ _ _ _ _ _
      (State.withLocals_preserves_localBindersBelowNextLocal _ _ readyBelow)
  · intro ready below node present
    have nodes := congrArg (fun value : StatementResult => value.state.nodes) receipt.completed
    rw [nodes] at present
    rcases List.mem_append.mp present with earlier | recorded
    · rcases child.events ⟨ready.wellFormed, ready.allocated, ready.origins⟩ below node earlier with old | fresh
      · exact .inl old
      · exact .inr (fresh.progress suffix)
    · cases Node.statement.inj (List.mem_singleton.mp recorded)
      exact .inr (StatementSince.of_let receipt ready below rfl)

theorem initializedHeader {fuel : Nat} {context : Context} {item : Syntax.ForItem}
    {initial : State} {result : ForItemForm × State}
    (receipt : LocalHeaderRequirementTiming.Receipt fuel context item initial result)
    (accepted : inferForItemFuel (fuel + 1) context item initial = .ok result)
    (child : Progress initial receipt.ready) : Progress initial result.2 := by
  have suffix : LocalReadScopeProgress.Progress receipt.ready result.2 := by
    rw [congrArg Prod.snd receipt.completed]
    exact LocalReadScopeProgress.Progress.allocateBinder (receipt.ready.withLocals receipt.locals)
      receipt.name.value receipt.generalized.scheme (some receipt.name.span) false receipt.generalized.requirements
  refine ⟨LocalReadEvents.inferForItemFuel_origins_progress accepted,
    child.scope.trans suffix, ?_, ?_⟩
  · intro below
    have readyBelow := child.binders below
    rw [congrArg Prod.snd receipt.completed]
    exact State.allocateBinder_preserves_localBindersBelowNextLocal _ _ _ _ _ _
      (State.withLocals_preserves_localBindersBelowNextLocal _ _ readyBelow)
  · intro ready below node present
    have nodes : result.2.nodes = receipt.ready.nodes :=
      congrArg (fun value : ForItemForm × State => value.2.nodes) receipt.completed
    rw [nodes] at present
    rcases child.events ready below node present with old | fresh
    · exact .inl old
    · exact .inr (fresh.progress suffix)

end Progress
end Solcore.Frontend.SourceInference.LocalGeneralizationBoundaries
