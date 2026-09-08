import Solcore.Core.DerivedComparisons
import Solcore.Core.LocalFragmentInsertionProperties

/-! Untyped ordered evaluation of the existing Word less-than expansion.
Only the right operand is restricted; left effects and all three actual stores
are retained. These results do not assume typed runtime values or stores. -/

set_option autoImplicit false

namespace Solcore.Core

theorem Evaluates.wordLt_local_right
    {environment : Environment} {initialStore middleStore finalStore : Store}
    {left right : Expr} {leftWord rightWord : Word}
    (leftEvaluation : Evaluates environment initialStore left (.word leftWord) middleStore)
    (rightEvaluation : Evaluates environment middleStore right (.word rightWord) finalStore)
    (rightFragment : right.LocalFragment) :
    Evaluates environment initialStore (left.wordLt right)
      (.bool (decide (leftWord < rightWord))) finalStore := by
  rw [Expr.wordLt_expansion]
  exact .letE leftEvaluation
    (.letE (rightEvaluation.weakenAt_zero_localFragment rightFragment (.word leftWord))
      (.binary (.var rfl) (.var rfl) rfl))

/-- Recover the original operand evaluations and the actual intermediate store,
not merely the evaluation of the shifted right operand beneath its new binding. -/
theorem Evaluates.wordLt_inv_local_right
    {environment : Environment} {initialStore finalStore : Store}
    {left right : Expr} {value : Value}
    (evaluation : Evaluates environment initialStore (left.wordLt right) value finalStore)
    (rightFragment : right.LocalFragment) :
    ∃ leftWord rightWord middleStore,
      Evaluates environment initialStore left (.word leftWord) middleStore ∧
      Evaluates environment middleStore right (.word rightWord) finalStore ∧
      value = .bool (decide (leftWord < rightWord)) := by
  rw [Expr.wordLt_expansion] at evaluation
  cases evaluation with
  | @letE _ _ _ _ _ _ boundLeft _ leftEvaluation bodyEvaluation =>
      cases bodyEvaluation with
      | @letE _ _ _ _ _ _ boundRight _ rightEvaluation comparison =>
          cases comparison with
          | @binary _ _ _ _ _ _ _ rightValue leftValue _ rightReference leftReference applied =>
              cases rightReference with
              | var foundRight =>
                  have rightEq : boundRight = rightValue := by simpa using foundRight
                  subst rightValue
                  cases leftReference with
                  | var foundLeft =>
                      have leftEq : boundLeft = leftValue := by simpa using foundLeft
                      subst leftValue
                      cases boundRight <;> cases boundLeft <;>
                        simp only [BinaryOp.apply, reduceCtorEq] at applied
                      case word.word rightWord leftWord =>
                        cases applied
                        exact ⟨leftWord, rightWord, _, leftEvaluation,
                          rightEvaluation.reflect_weakenAt_zero_localFragment rightFragment, rfl⟩

theorem wordLt_evaluates_iff_local_right
    {environment : Environment} {initialStore finalStore : Store}
    {left right : Expr} {value : Value} (rightFragment : right.LocalFragment) :
    Evaluates environment initialStore (left.wordLt right) value finalStore ↔
      ∃ leftWord rightWord middleStore,
        Evaluates environment initialStore left (.word leftWord) middleStore ∧
        Evaluates environment middleStore right (.word rightWord) finalStore ∧
        value = .bool (decide (leftWord < rightWord)) := by
  constructor
  · intro evaluation
    exact evaluation.wordLt_inv_local_right rightFragment
  · rintro ⟨leftWord, rightWord, middleStore, leftEvaluation, rightEvaluation, rfl⟩
    exact leftEvaluation.wordLt_local_right rightEvaluation rightFragment

end Solcore.Core
