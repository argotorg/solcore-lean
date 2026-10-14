import Solcore.SourceSemantics.CoreLowering.AcceptedNamedBodyFlow
import Solcore.SourceSemantics.CoreLowering.AcceptedCompilerBodyCompletion

/-! Completion is indexed by the original result type. The grammar receipt
retains actual dead suffixes while a stopped head supplies the execution path. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.AcceptedNamedBodyFlow
open Core Frontend SourceInference AcceptedCompilerBodyCompletion

variable {policy : SourceCoreLoops.Policy} {source : TypedSource} {result : Ty}
  {reasonAt : ExpressionId → Word}

def Tree.formed {mode : Bool} {escaped : Word} {fuel scope statements code}
    (tree : Tree policy source result reasonAt mode escaped fuel scope statements code) : Bool :=
  match tree with
  | .boundary .. | .assigning .. | .forBoundary .. | .matching .. => false
  | .nil | .returning .. | .returnUnit .. | .breaking .. | .continuing .. | .tailValue .. => true
  | .initialized _ _ _ _ _ _ _ tail _ | .absent _ _ _ _ tail _ => tail.formed
  | .assigned _ _ _ tail _ _ | .discard _ _ _ _ _ tail => tail.formed
  | .valueDiscard _ _ _ _ _ _ tail => !mode && tail.formed
  | .block _ _ inner tail => inner.formed && tail.formed
  | .conditional _ _ _ _ _ left right tail => left.formed && right.formed && tail.formed
  | .matched _ _ receipt branches tail =>
      receipt.requests.attach.all (fun request => (branches request.val request.property).formed) && tail.formed
  | .whileLoop _ _ _ _ _ _ inner tail => inner.formed && tail.formed
  | .forLoop _ _ _ _ _ _ initial inner after tail => initial.closed && inner.formed && after.closed && tail.formed

def Tree.complete {mode : Bool} {escaped : Word} {fuel scope statements code}
    (tree : Tree policy source result reasonAt mode escaped fuel scope statements code)
    (expected : TypeSystem.Ty) : Bool :=
  match tree with
  | .nil => !mode || decide (expected = .unit)
  | .boundary .. | .assigning .. | .forBoundary .. | .matching .. => false
  | .returning .. | .returnUnit .. | .breaking .. | .continuing .. => true
  | @Tree.tailValue _ _ _ _ _ _ _ _ node _ _ _ _ _ _ _ _ => decide (node.type = expected)
  | .initialized _ _ _ _ _ _ _ tail _ | .absent _ _ _ _ tail _ => tail.complete expected
  | .assigned _ _ _ tail _ _ | .discard _ _ _ _ _ tail => tail.complete expected
  | .valueDiscard _ _ _ _ _ _ tail => !mode && tail.complete expected
  | @Tree.block _ _ _ _ _ _ _ _ _ _ _ _ statements _ _ _ _ inner tail =>
      inner.complete expected && tail.formed &&
        (tail.complete expected || (stopped? source statements).isSome)
  | @Tree.conditional _ _ _ _ _ _ _ _ _ _ _ _ _ leftBody rightBody _ _ _ _ _ _ _ _ left right tail =>
      left.complete expected && right.complete expected && tail.formed &&
        (tail.complete expected ||
          ((stopped? source leftBody).isSome &&
            (stopped? source (rightBody.getD [])).isSome))
  | @Tree.matched _ _ _ _ _ _ _ _ _ _ _ _ resolution _ _ _ _ _ receipt branches tail =>
      receipt.requests.attach.all (fun request => (branches request.val request.property).complete expected) && tail.formed &&
        (tail.complete expected || matchStops source resolution)
  | .whileLoop _ _ _ _ _ _ inner tail => inner.complete expected && tail.complete expected
  | .forLoop _ _ _ _ _ _ initial inner after tail =>
      initial.closed && inner.complete expected && after.closed && tail.complete expected

private theorem and_true {left right : Bool} (both : left = true ∧ right = true) :
    (left && right) = true := by simp [both.1, both.2]

private theorem all_map {α : Type} {items : List α} {p q : α → Bool}
    (all : items.all p = true) (mapped : ∀ item ∈ items, p item = true → q item = true) :
    items.all q = true :=
  List.all_eq_true.mpr (fun item member => mapped item member (List.all_eq_true.mp all item member))

theorem Tree.complete_formed {mode : Bool} {escaped : Word} {fuel scope statements code}
    (tree : Tree policy source result reasonAt mode escaped fuel scope statements code)
    {expected : TypeSystem.Ty} (complete : tree.complete expected = true) : tree.formed = true := by
  induction tree with
  | nil | returning | returnUnit | breaking | continuing | tailValue => rfl
  | assigning | boundary | forBoundary | matching => cases complete
  | initialized _ _ _ _ _ _ _ _ _ ih | absent _ _ _ _ _ _ ih
  | assigned _ _ _ _ _ _ ih | discard _ _ _ _ _ _ ih => exact ih complete
  | valueDiscard read form notTail child generated statementType remaining ih =>
    simp only [Tree.complete, Bool.and_eq_true] at complete
    exact and_true ⟨complete.1, ih complete.2⟩
  | block read form inner remaining innerIH _ =>
    simp only [Tree.complete, Bool.and_eq_true] at complete
    exact and_true ⟨innerIH complete.1.1, complete.1.2⟩
  | conditional read form child generated conditionType left right remaining leftIH rightIH _ =>
    simp only [Tree.complete, Bool.and_eq_true] at complete
    exact and_true ⟨and_true ⟨leftIH complete.1.1.1, rightIH complete.1.1.2⟩, complete.1.2⟩
  | matched read form receipt branches remaining branchIH _ =>
    simp only [Tree.complete, Bool.and_eq_true] at complete
    exact and_true ⟨all_map complete.1.1 (fun request _ => branchIH request.val request.property), complete.1.2⟩
  | whileLoop read form statementType child generated conditionType inner remaining innerIH tailIH =>
    simp only [Tree.complete, Bool.and_eq_true] at complete
    exact and_true ⟨innerIH complete.1, tailIH complete.2⟩
  | forLoop read form statementType child generated conditionType initial inner after remaining innerIH tailIH =>
    simp only [Tree.complete, Bool.and_eq_true] at complete
    exact and_true ⟨and_true ⟨and_true
      ⟨complete.1.1.1, innerIH complete.1.1.2⟩, complete.1.2⟩, tailIH complete.2⟩

theorem Tree.closed_complete {mode : Bool} {escaped : Word} {fuel scope statements code}
    (tree : Tree policy source result reasonAt mode escaped fuel scope statements code)
    (closed : tree.closed = true) (expected : TypeSystem.Ty) : tree.complete expected = true := by
  induction tree with
  | nil =>
    simp only [Tree.closed] at closed
    simp [Tree.complete, closed]
  | returning | returnUnit | breaking | continuing => rfl
  | tailValue | assigning | boundary | forBoundary | matching => cases closed
  | initialized _ _ _ _ _ _ _ _ _ ih | absent _ _ _ _ _ _ ih
  | assigned _ _ _ _ _ _ ih | discard _ _ _ _ _ _ ih => exact ih closed
  | valueDiscard read form notTail child generated statementType remaining ih =>
    simp only [Tree.closed, Bool.and_eq_true] at closed
    exact and_true ⟨closed.1, ih closed.2⟩
  | block read form inner remaining innerIH tailIH =>
    simp only [Tree.closed, Bool.and_eq_true] at closed
    have tail := tailIH closed.2
    simp only [Tree.complete, innerIH closed.1, tail, remaining.complete_formed tail, Bool.true_and, Bool.true_or]
  | conditional read form child generated conditionType left right remaining leftIH rightIH tailIH =>
    simp only [Tree.closed, Bool.and_eq_true] at closed
    have tail := tailIH closed.2
    simp only [Tree.complete, leftIH closed.1.1, rightIH closed.1.2, tail,
      remaining.complete_formed tail, Bool.true_and, Bool.true_or]
  | matched read form receipt branches remaining branchIH tailIH =>
    simp only [Tree.closed, Bool.and_eq_true] at closed
    have tail := tailIH closed.2
    have heads := all_map closed.1 (fun request _ => branchIH request.val request.property)
    simp only [Tree.complete, heads, tail, remaining.complete_formed tail, Bool.true_and, Bool.true_or]
  | whileLoop read form statementType child generated conditionType inner remaining innerIH tailIH =>
    simp only [Tree.closed, Bool.and_eq_true] at closed
    exact and_true ⟨innerIH closed.1, tailIH closed.2⟩
  | forLoop read form statementType child generated conditionType initial inner after remaining innerIH tailIH =>
    simp only [Tree.closed, Bool.and_eq_true] at closed
    exact and_true ⟨and_true ⟨and_true
      ⟨closed.1.1.1, innerIH closed.1.1.2⟩, closed.1.2⟩, tailIH closed.2⟩

end Solcore.SourceSemantics.CoreLowering.AcceptedNamedBodyFlow
