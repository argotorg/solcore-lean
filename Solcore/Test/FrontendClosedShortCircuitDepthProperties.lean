import Solcore.Frontend.ClosedSource

/- Exact-depth composition. The selected right operand starts from
the actual left endpoint; skipped operands have no depth or execution premise. -/
set_option autoImplicit false
open Solcore Frontend
namespace Tests.ClosedShortCircuitDepth

variable {owner : Resolved.DeclarationId} {names : LocalNameTable}
  {captured : Resolved.LocalScope RuntimeValue}
  {initialStore middleStore finalStore : List RuntimeValue}
  {span operatorSpan : Syntax.SourceSpan} {left right : Syntax.Expr}
  {value : RuntimeValue} {leftDepth rightDepth : Nat}

theorem skipped_and_exact_depth
    (leftCutoff : ∀ n,
      evaluateClosedSourceExpression? n owner names captured initialStore left =
        if leftDepth ≤ n then some (.bool false, finalStore) else none) :
    ∀ budget, evaluateClosedSourceExpression? budget owner names captured initialStore
      ⟨span, .binary left ⟨operatorSpan, .logicalAnd⟩ right⟩ =
        if leftDepth + 1 ≤ budget then some (.bool false, finalStore) else none := by
  intro budget
  cases budget with
  | zero => simp [evaluateClosedSourceExpression?]
  | succ n =>
      rw [evaluateClosedSourceExpression?_logicalAnd, leftCutoff]
      by_cases enough : leftDepth ≤ n
      · rw [if_pos enough, if_pos (show leftDepth + 1 ≤ n + 1 by omega)]
        rfl
      · rw [if_neg enough, if_neg (show ¬ leftDepth + 1 ≤ n + 1 by omega)]
        rfl

theorem skipped_or_exact_depth
    (leftCutoff : ∀ n,
      evaluateClosedSourceExpression? n owner names captured initialStore left =
        if leftDepth ≤ n then some (.bool true, finalStore) else none) :
    ∀ budget, evaluateClosedSourceExpression? budget owner names captured initialStore
      ⟨span, .binary left ⟨operatorSpan, .logicalOr⟩ right⟩ =
        if leftDepth + 1 ≤ budget then some (.bool true, finalStore) else none := by
  intro budget
  cases budget with
  | zero => simp [evaluateClosedSourceExpression?]
  | succ n =>
      rw [evaluateClosedSourceExpression?_logicalOr, leftCutoff]
      by_cases enough : leftDepth ≤ n
      · rw [if_pos enough, if_pos (show leftDepth + 1 ≤ n + 1 by omega)]
        rfl
      · rw [if_neg enough, if_neg (show ¬ leftDepth + 1 ≤ n + 1 by omega)]
        rfl

theorem selected_and_exact_depth
    (leftCutoff : ∀ n,
      evaluateClosedSourceExpression? n owner names captured initialStore left =
        if leftDepth ≤ n then some (.bool true, middleStore) else none)
    (rightCutoff : ∀ n,
      evaluateClosedSourceExpression? n owner names captured middleStore right =
        if rightDepth ≤ n then some (value, finalStore) else none) :
    ∀ budget, evaluateClosedSourceExpression? budget owner names captured initialStore
      ⟨span, .binary left ⟨operatorSpan, .logicalAnd⟩ right⟩ =
        if max leftDepth rightDepth + 1 ≤ budget then some (value, finalStore) else none := by
  intro budget
  cases budget with
  | zero => simp [evaluateClosedSourceExpression?]
  | succ n =>
      rw [evaluateClosedSourceExpression?_logicalAnd, leftCutoff]
      by_cases leftEnough : leftDepth ≤ n
      · rw [if_pos leftEnough]
        change evaluateClosedSourceExpression? n owner names captured middleStore right = _
        rw [rightCutoff]
        by_cases rightEnough : rightDepth ≤ n
        · rw [if_pos rightEnough, if_pos (show max leftDepth rightDepth + 1 ≤ n + 1 from
            Nat.succ_le_succ (Nat.max_le.mpr ⟨leftEnough, rightEnough⟩))]
        · have insufficient : ¬ max leftDepth rightDepth + 1 ≤ n + 1 := by
            intro enough
            exact rightEnough (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_of_succ_le_succ enough))
          rw [if_neg rightEnough, if_neg insufficient]
      · have insufficient : ¬ max leftDepth rightDepth + 1 ≤ n + 1 := by
          intro enough
          exact leftEnough (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_of_succ_le_succ enough))
        rw [if_neg leftEnough, if_neg insufficient]
        rfl

theorem selected_or_exact_depth
    (leftCutoff : ∀ n,
      evaluateClosedSourceExpression? n owner names captured initialStore left =
        if leftDepth ≤ n then some (.bool false, middleStore) else none)
    (rightCutoff : ∀ n,
      evaluateClosedSourceExpression? n owner names captured middleStore right =
        if rightDepth ≤ n then some (value, finalStore) else none) :
    ∀ budget, evaluateClosedSourceExpression? budget owner names captured initialStore
      ⟨span, .binary left ⟨operatorSpan, .logicalOr⟩ right⟩ =
        if max leftDepth rightDepth + 1 ≤ budget then some (value, finalStore) else none := by
  intro budget
  cases budget with
  | zero => simp [evaluateClosedSourceExpression?]
  | succ n =>
      rw [evaluateClosedSourceExpression?_logicalOr, leftCutoff]
      by_cases leftEnough : leftDepth ≤ n
      · rw [if_pos leftEnough]
        change evaluateClosedSourceExpression? n owner names captured middleStore right = _
        rw [rightCutoff]
        by_cases rightEnough : rightDepth ≤ n
        · rw [if_pos rightEnough, if_pos (show max leftDepth rightDepth + 1 ≤ n + 1 from
            Nat.succ_le_succ (Nat.max_le.mpr ⟨leftEnough, rightEnough⟩))]
        · have insufficient : ¬ max leftDepth rightDepth + 1 ≤ n + 1 := by
            intro enough
            exact rightEnough (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_of_succ_le_succ enough))
          rw [if_neg rightEnough, if_neg insufficient]
      · have insufficient : ¬ max leftDepth rightDepth + 1 ≤ n + 1 := by
          intro enough
          exact leftEnough (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_of_succ_le_succ enough))
        rw [if_neg leftEnough, if_neg insufficient]
        rfl

end Tests.ClosedShortCircuitDepth
