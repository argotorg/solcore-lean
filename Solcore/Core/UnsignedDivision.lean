import Solcore.Core.Eval

set_option autoImplicit false

namespace Solcore.Core

/-! Focused value and evaluation interface for unsigned division and modulo. -/

namespace Word

@[simp] theorem udiv_zero (left : Word) :
    left.udiv Word.zero = Word.zero := by
  rfl

@[simp] theorem umod_zero (left : Word) :
    left.umod Word.zero = Word.zero := by
  rfl

theorem udiv_nonzero (left right : Word) (nonzero : right ≠ Word.zero) :
    left.udiv right = left / right := by
  have valueNonzero : right.val ≠ 0 := by
    intro valueZero
    apply nonzero
    exact Fin.ext (by
      change right.val = 0
      exact valueZero)
  simp [udiv, valueNonzero]

theorem umod_nonzero (left right : Word) (nonzero : right ≠ Word.zero) :
    left.umod right = left % right := by
  have valueNonzero : right.val ≠ 0 := by
    intro valueZero
    apply nonzero
    exact Fin.ext (by
      change right.val = 0
      exact valueZero)
  simp [umod, valueNonzero]

end Word

namespace BinaryOp

@[simp] theorem apply_wordDiv (left right : Word) :
    BinaryOp.wordDiv.apply (.word left) (.word right) =
      some (.word (left.udiv right)) := by
  rfl

@[simp] theorem apply_wordMod (left right : Word) :
    BinaryOp.wordMod.apply (.word left) (.word right) =
      some (.word (left.umod right)) := by
  rfl

end BinaryOp

namespace Evaluates

theorem wordDiv
    {environment : Environment} {initialStore intermediateStore finalStore : Store}
    {left right : Expr} {leftValue rightValue : Word}
    (leftEvaluation :
      Evaluates environment initialStore left (.word leftValue) intermediateStore)
    (rightEvaluation :
      Evaluates environment intermediateStore right (.word rightValue) finalStore) :
    Evaluates environment initialStore (.binary .wordDiv left right)
      (.word (leftValue.udiv rightValue)) finalStore :=
  .binary leftEvaluation rightEvaluation rfl

theorem wordDiv_zero
    {environment : Environment} {initialStore intermediateStore finalStore : Store}
    {left right : Expr} {leftValue : Word}
    (leftEvaluation :
      Evaluates environment initialStore left (.word leftValue) intermediateStore)
    (rightEvaluation :
      Evaluates environment intermediateStore right (.word Word.zero) finalStore) :
    Evaluates environment initialStore (.binary .wordDiv left right)
      (.word Word.zero) finalStore := by
  simpa using leftEvaluation.wordDiv rightEvaluation

theorem wordDiv_nonzero
    {environment : Environment} {initialStore intermediateStore finalStore : Store}
    {left right : Expr} {leftValue rightValue : Word}
    (divisorNonzero : rightValue ≠ Word.zero)
    (leftEvaluation :
      Evaluates environment initialStore left (.word leftValue) intermediateStore)
    (rightEvaluation :
      Evaluates environment intermediateStore right (.word rightValue) finalStore) :
    Evaluates environment initialStore (.binary .wordDiv left right)
      (.word (leftValue / rightValue)) finalStore := by
  simpa [Word.udiv_nonzero leftValue rightValue divisorNonzero] using
    leftEvaluation.wordDiv rightEvaluation

theorem wordMod
    {environment : Environment} {initialStore intermediateStore finalStore : Store}
    {left right : Expr} {leftValue rightValue : Word}
    (leftEvaluation :
      Evaluates environment initialStore left (.word leftValue) intermediateStore)
    (rightEvaluation :
      Evaluates environment intermediateStore right (.word rightValue) finalStore) :
    Evaluates environment initialStore (.binary .wordMod left right)
      (.word (leftValue.umod rightValue)) finalStore :=
  .binary leftEvaluation rightEvaluation rfl

theorem wordMod_zero
    {environment : Environment} {initialStore intermediateStore finalStore : Store}
    {left right : Expr} {leftValue : Word}
    (leftEvaluation :
      Evaluates environment initialStore left (.word leftValue) intermediateStore)
    (rightEvaluation :
      Evaluates environment intermediateStore right (.word Word.zero) finalStore) :
    Evaluates environment initialStore (.binary .wordMod left right)
      (.word Word.zero) finalStore := by
  simpa using leftEvaluation.wordMod rightEvaluation

theorem wordMod_nonzero
    {environment : Environment} {initialStore intermediateStore finalStore : Store}
    {left right : Expr} {leftValue rightValue : Word}
    (divisorNonzero : rightValue ≠ Word.zero)
    (leftEvaluation :
      Evaluates environment initialStore left (.word leftValue) intermediateStore)
    (rightEvaluation :
      Evaluates environment intermediateStore right (.word rightValue) finalStore) :
    Evaluates environment initialStore (.binary .wordMod left right)
      (.word (leftValue % rightValue)) finalStore := by
  simpa [Word.umod_nonzero leftValue rightValue divisorNonzero] using
    leftEvaluation.wordMod rightEvaluation

end Evaluates

end Solcore.Core
