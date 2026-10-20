import Solcore.Frontend.SourceInference.LocalReadRetiredInterval
import Solcore.Frontend.SourceInference.LocalHeaderRequirementTiming

/-! Actual initialized let receipts establish the retired-local interval at
the return of the initializer. Header declarations and ordinary statements
retain their respective allocation and node-recording behavior. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.Frontend.SourceInference
open TypeSystem Detail LocalReadScopeProgress

namespace LocalLetRequirementTiming.Receipt
variable {fuel : Nat} {context : Context} {statement : Syntax.Statement}
    {initial : State} {result : StatementResult}

theorem retired_interval (receipt : Receipt fuel context statement initial result)
    (below : initial.LocalBindersBelowNextLocal) :
    Barrier initial.nextLocal receipt.ready.nextLocal receipt.ready.nodes result.state := by
  have next := congrArg (fun value : StatementResult => value.state.nextLocal) receipt.completed
  change result.state.nextLocal = receipt.ready.nextLocal + 1 at next
  have nodes := congrArg (fun value : StatementResult => value.state.nodes) receipt.completed
  refine ⟨by rw [next]; omega, ?_, ?_⟩
  · intro id created retired binder present same
    rw [receipt.result_binders] at present
    rcases List.mem_cons.mp present with current | entering
    · subst binder
      have index := congrArg Resolved.LocalId.binderIndex same
      change receipt.ready.nextLocal = id.binderIndex at index
      omega
    · have older := below binder entering
      rw [same] at older
      omega
  · intro id _ _ occurrence ⟨expression, member, same, name, form⟩
    rw [nodes] at member
    rcases List.mem_append.mp member with old | recorded
    · exact ⟨expression, old, same, name, form⟩
    · cases List.mem_singleton.mp recorded

end LocalLetRequirementTiming.Receipt

namespace LocalHeaderRequirementTiming.Receipt
variable {fuel : Nat} {context : Context} {item : Syntax.ForItem}
    {initial : State} {result : ForItemForm × State}

theorem retired_interval (receipt : Receipt fuel context item initial result)
    (below : initial.LocalBindersBelowNextLocal) :
    Barrier initial.nextLocal receipt.ready.nextLocal receipt.ready.nodes result.2 := by
  have next := congrArg (fun value : ForItemForm × State => value.2.nextLocal) receipt.completed
  change result.2.nextLocal = receipt.ready.nextLocal + 1 at next
  have nodes : result.2.nodes = receipt.ready.nodes :=
    congrArg (fun value : ForItemForm × State => value.2.nodes) receipt.completed
  refine ⟨by rw [next]; omega, ?_, ?_⟩
  · intro id created retired binder present same
    rw [receipt.result_binders] at present
    rcases List.mem_cons.mp present with current | entering
    · subst binder
      have index := congrArg Resolved.LocalId.binderIndex same
      change receipt.ready.nextLocal = id.binderIndex at index
      omega
    · have older := below binder entering
      rw [same] at older
      omega
  · intro id _ _ occurrence read
    simpa only [nodes] using read

end LocalHeaderRequirementTiming.Receipt
end Solcore.Frontend.SourceInference
