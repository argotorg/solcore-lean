import Solcore.SourceSemantics.Staging.SelectedControlPreservationContracts
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.Staging.Recursive.SelectedPreservation
open Frontend SourceInference TypeSystem
open Solcore.SourceSemantics.Dynamic
variable {program : Program} {registry : Registry}

theorem while_step (size : Nat)
    (expressionIH : ∀ smaller, smaller < size → ExpressionAt program registry smaller)
    (statementsIH : ∀ smaller, smaller < size → StatementsAt program registry smaller)
    (whileIH : ∀ smaller, smaller < size → WhileAt program registry smaller) :
    WhileAt program registry size := by
  intro scope context bodyFinal environment before after condition statements outcome control facts
    runtime covers locals heap conditionTyped bodyTyped trace
  cases trace with
  | @done testSize scope context environment before after condition statements test =>
      have post := expressionIH testSize (Size.child_lt_stepSize (by simp)) runtime covers locals heap conditionTyped test
      exact ⟨post.heap_typed, post.heap_extends, by intro value equal; cases equal⟩
  | @conditionFault testSize scope context environment before after condition statements failure test =>
      have post := expressionIH testSize (Size.child_lt_stepSize (by simp)) runtime covers locals heap conditionTyped test
      exact ⟨post.heap_typed, post.heap_extends, by intro value equal; cases equal⟩
  | @returned testSize bodySize scope context innerContext environment before middle after condition statements value test body =>
      have first := expressionIH testSize (Size.child_lt_stepSize (by simp)) runtime covers locals heap conditionTyped test
      have post := statementsIH bodySize (Size.child_lt_stepSize (by simp)) runtime covers
        (locals.mono first.heap_extends) first.heap_typed bodyTyped body
      exact ⟨post.heap_typed, first.heap_extends.trans post.heap_extends, post.returned (by simp)⟩
  | @bodyFault testSize bodySize scope context innerContext environment before middle after condition statements failure test body =>
      have first := expressionIH testSize (Size.child_lt_stepSize (by simp)) runtime covers locals heap conditionTyped test
      have post := statementsIH bodySize (Size.child_lt_stepSize (by simp)) runtime covers
        (locals.mono first.heap_extends) first.heap_typed bodyTyped body
      exact ⟨post.heap_typed, first.heap_extends.trans post.heap_extends, post.returned (by simp)⟩
  | @next testSize bodySize nextSize scope context innerContext environment innerEnvironment before middle bodyHeap after condition statements outcome test body next =>
      have first := expressionIH testSize (Size.child_lt_stepSize (by simp)) runtime covers locals heap conditionTyped test
      have middlePost := statementsIH bodySize (Size.child_lt_stepSize (by simp)) runtime covers
        (locals.mono first.heap_extends) first.heap_typed bodyTyped body
      have post := whileIH nextSize (Size.child_lt_stepSize (by simp)) runtime covers
        (locals.mono (first.heap_extends.trans middlePost.heap_extends)) middlePost.heap_typed conditionTyped bodyTyped next
      exact ⟨post.heap_typed, first.heap_extends.trans (middlePost.heap_extends.trans post.heap_extends), post.returned⟩

theorem for_loop_step (size : Nat)
    (expressionIH : ∀ smaller, smaller < size → ExpressionAt program registry smaller)
    (statementsIH : ∀ smaller, smaller < size → StatementsAt program registry smaller)
    (itemsIH : ∀ smaller, smaller < size → ForItemsAt program registry smaller)
    (loopIH : ∀ smaller, smaller < size → ForLoopAt program registry smaller) :
    ForLoopAt program registry size := by
  intro scope context bodyFinal postFinal environment before after condition post body outcome control facts
    runtime covers locals heap conditionTyped bodyTyped postTyped trace
  cases trace with
  | @testFault testSize scope context environment before after condition post body failure test =>
      have result := expressionIH testSize (Size.child_lt_stepSize (by simp)) runtime covers locals heap conditionTyped test
      exact ⟨result.heap_typed, result.heap_extends, by intro value equal; cases equal⟩
  | @finished testSize scope context environment before after condition post body test =>
      have result := expressionIH testSize (Size.child_lt_stepSize (by simp)) runtime covers locals heap conditionTyped test
      exact ⟨result.heap_typed, result.heap_extends, by intro value equal; cases equal⟩
  | @bodyFailure testSize branchSize scope context innerContext environment before middle after condition post body failure test branch =>
      have first := expressionIH testSize (Size.child_lt_stepSize (by simp)) runtime covers locals heap conditionTyped test
      have result := statementsIH branchSize (Size.child_lt_stepSize (by simp)) runtime covers
        (locals.mono first.heap_extends) first.heap_typed bodyTyped branch
      exact ⟨result.heap_typed, first.heap_extends.trans result.heap_extends, result.returned (by simp)⟩
  | @returnedFromBody testSize branchSize scope context innerContext environment before middle after condition post body value test branch =>
      have first := expressionIH testSize (Size.child_lt_stepSize (by simp)) runtime covers locals heap conditionTyped test
      have result := statementsIH branchSize (Size.child_lt_stepSize (by simp)) runtime covers
        (locals.mono first.heap_extends) first.heap_typed bodyTyped branch
      exact ⟨result.heap_typed, first.heap_extends.trans result.heap_extends, result.returned (by simp)⟩
  | @postFailure testSize branchSize postTraceSize scope context innerContext postContext environment innerEnvironment
      before middle bodyHeap after condition post body failure test branch postTrace =>
      have first := expressionIH testSize (Size.child_lt_stepSize (by simp)) runtime covers locals heap conditionTyped test
      have second := statementsIH branchSize (Size.child_lt_stepSize (by simp)) runtime covers
        (locals.mono first.heap_extends) first.heap_typed bodyTyped branch
      have result := itemsIH postTraceSize (Size.child_lt_stepSize (by simp)) runtime covers
        (locals.mono (first.heap_extends.trans second.heap_extends)) second.heap_typed postTyped postTrace
      exact ⟨result.heap_typed, first.heap_extends.trans (second.heap_extends.trans result.heap_extends), by intro value equal; cases equal⟩
  | @iterate testSize branchSize postTraceSize nextSize scope context innerContext postContext environment innerEnvironment postEnvironment
      before middle bodyHeap postHeap after condition post body outcome test branch postTrace next =>
      have first := expressionIH testSize (Size.child_lt_stepSize (by simp)) runtime covers locals heap conditionTyped test
      have second := statementsIH branchSize (Size.child_lt_stepSize (by simp)) runtime covers
        (locals.mono first.heap_extends) first.heap_typed bodyTyped branch
      have third := itemsIH postTraceSize (Size.child_lt_stepSize (by simp)) runtime covers
        (locals.mono (first.heap_extends.trans second.heap_extends)) second.heap_typed postTyped postTrace
      have result := loopIH nextSize (Size.child_lt_stepSize (by simp)) runtime covers
        (locals.mono (first.heap_extends.trans (second.heap_extends.trans third.heap_extends)))
        third.heap_typed conditionTyped bodyTyped postTyped next
      exact ⟨result.heap_typed, first.heap_extends.trans (second.heap_extends.trans (third.heap_extends.trans result.heap_extends)), result.returned⟩

end Solcore.SourceSemantics.Staging.Recursive.SelectedPreservation
