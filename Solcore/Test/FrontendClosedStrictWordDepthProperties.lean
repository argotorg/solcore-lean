import Solcore.Frontend.ClosedSource
import Solcore.Frontend.StrictWordBinary

/- Exact search depth composes both actual Word children in their original order.
This is a cutoff theorem at every budget, not a Core transition-cost equation. -/
set_option autoImplicit false
open Solcore Frontend
namespace Tests.ClosedStrictWordDepth

theorem strict_binary_exact_depth
    {owner : Resolved.DeclarationId} {names : LocalNameTable}
    {captured : Resolved.LocalScope RuntimeValue}
    {initialStore middleStore finalStore : List RuntimeValue}
    {span operatorSpan : Syntax.SourceSpan} {operator : Syntax.BinaryOp}
    {left right : Syntax.Expr} {leftWord rightWord : Core.Word}
    {result : Core.Value} {leftDepth rightDepth : Nat}
    (meaning : StrictWordBinaryDenotes operator leftWord rightWord result)
    (leftCutoff : ∀ n,
      evaluateClosedSourceExpression? n owner names captured initialStore left =
        if leftDepth ≤ n then some (.word leftWord, middleStore) else none)
    (rightCutoff : ∀ n,
      evaluateClosedSourceExpression? n owner names captured middleStore right =
        if rightDepth ≤ n then some (.word rightWord, finalStore) else none) :
    ∀ budget, evaluateClosedSourceExpression? budget owner names captured initialStore
      ⟨span, .binary left ⟨operatorSpan, operator⟩ right⟩ =
        if max leftDepth rightDepth + 1 ≤ budget then
          some (RuntimeValue.ofCore result, finalStore) else none := by
  intro budget
  cases budget with
  | zero => simp [evaluateClosedSourceExpression?]
  | succ n =>
      rw [evaluateClosedSourceExpression?_strictWordBinary _ _ _ _ _ _ _ _
        meaning.operator_is_strict.1 meaning.operator_is_strict.2, leftCutoff]
      by_cases leftEnough : leftDepth ≤ n
      · rw [if_pos leftEnough]
        simp only [bind, Option.bind_some]
        rw [rightCutoff]
        by_cases rightEnough : rightDepth ≤ n
        · rw [if_pos rightEnough,
            if_pos (show max leftDepth rightDepth + 1 ≤ n + 1 by omega)]
          simp only [Option.bind_some, evaluateStrictWordBinary?_iff.mpr meaning]
          rfl
        · rw [if_neg rightEnough,
            if_neg (show ¬ max leftDepth rightDepth + 1 ≤ n + 1 by omega)]
          rfl
      · rw [if_neg leftEnough,
          if_neg (show ¬ max leftDepth rightDepth + 1 ≤ n + 1 by omega)]
        rfl

end Tests.ClosedStrictWordDepth
