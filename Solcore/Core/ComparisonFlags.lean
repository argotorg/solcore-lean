import Solcore.Core.Conversions

set_option autoImplicit false

namespace Solcore.Core

/-! Proof interface for derived word-valued comparison flags. -/

@[simp] theorem Expr.wordEqFlag_expansion (left right : Expr) :
    left.wordEqFlag right =
      (Expr.binary .wordEq left right).boolToWord :=
  rfl

@[simp] theorem Expr.wordGtFlag_expansion (left right : Expr) :
    left.wordGtFlag right =
      (Expr.binary .wordGt left right).boolToWord :=
  rfl

namespace HasType

theorem wordEqFlag
    {context : Context} {definitions : DataEnvironment} {left right : Expr}
    (leftTyping : HasType context left .word definitions)
    (rightTyping : HasType context right .word definitions) :
    HasType context (left.wordEqFlag right) .word definitions :=
  HasType.boolToWord (HasType.binary leftTyping rightTyping)

theorem wordGtFlag
    {context : Context} {definitions : DataEnvironment} {left right : Expr}
    (leftTyping : HasType context left .word definitions)
    (rightTyping : HasType context right .word definitions) :
    HasType context (left.wordGtFlag right) .word definitions :=
  HasType.boolToWord (HasType.binary leftTyping rightTyping)

end HasType

theorem infer_wordEqFlag
    {context : Context} {definitions : DataEnvironment} {left right : Expr}
    (leftInferred : infer? context left definitions = some .word)
    (rightInferred : infer? context right definitions = some .word) :
    infer? context (left.wordEqFlag right) definitions = some .word :=
  infer_complete
    ((infer_sound leftInferred).wordEqFlag (infer_sound rightInferred))

theorem infer_wordGtFlag
    {context : Context} {definitions : DataEnvironment} {left right : Expr}
    (leftInferred : infer? context left definitions = some .word)
    (rightInferred : infer? context right definitions = some .word) :
    infer? context (left.wordGtFlag right) definitions = some .word :=
  infer_complete
    ((infer_sound leftInferred).wordGtFlag (infer_sound rightInferred))

namespace Evaluates

theorem wordEqFlag
    {environment : Environment} {initialStore intermediateStore finalStore : Store}
    {left right : Expr} {leftValue rightValue : Word}
    (leftEvaluation :
      Evaluates environment initialStore left (.word leftValue) intermediateStore)
    (rightEvaluation :
      Evaluates environment intermediateStore right (.word rightValue) finalStore) :
    Evaluates environment initialStore (left.wordEqFlag right)
      (.word (if leftValue == rightValue then Word.ofNatModulo 1 else Word.zero))
      finalStore :=
  (Evaluates.binary leftEvaluation rightEvaluation rfl).boolToWord

theorem wordEqFlag_eq
    {environment : Environment} {initialStore intermediateStore finalStore : Store}
    {left right : Expr} {leftValue rightValue : Word}
    (valuesEqual : leftValue = rightValue)
    (leftEvaluation :
      Evaluates environment initialStore left (.word leftValue) intermediateStore)
    (rightEvaluation :
      Evaluates environment intermediateStore right (.word rightValue) finalStore) :
    Evaluates environment initialStore (left.wordEqFlag right)
      (.word (Word.ofNatModulo 1)) finalStore := by
  subst rightValue
  simpa using leftEvaluation.wordEqFlag rightEvaluation

theorem wordEqFlag_ne
    {environment : Environment} {initialStore intermediateStore finalStore : Store}
    {left right : Expr} {leftValue rightValue : Word}
    (valuesNotEqual : leftValue ≠ rightValue)
    (leftEvaluation :
      Evaluates environment initialStore left (.word leftValue) intermediateStore)
    (rightEvaluation :
      Evaluates environment intermediateStore right (.word rightValue) finalStore) :
    Evaluates environment initialStore (left.wordEqFlag right)
      (.word Word.zero) finalStore := by
  have valuesBeq : (leftValue == rightValue) = false :=
    beq_eq_false_iff_ne.mpr valuesNotEqual
  simpa [valuesBeq] using leftEvaluation.wordEqFlag rightEvaluation

theorem wordGtFlag
    {environment : Environment} {initialStore intermediateStore finalStore : Store}
    {left right : Expr} {leftValue rightValue : Word}
    (leftEvaluation :
      Evaluates environment initialStore left (.word leftValue) intermediateStore)
    (rightEvaluation :
      Evaluates environment intermediateStore right (.word rightValue) finalStore) :
    Evaluates environment initialStore (left.wordGtFlag right)
      (.word (if decide (leftValue > rightValue) then
        Word.ofNatModulo 1 else Word.zero)) finalStore :=
  (Evaluates.binary leftEvaluation rightEvaluation rfl).boolToWord

theorem wordGtFlag_gt
    {environment : Environment} {initialStore intermediateStore finalStore : Store}
    {left right : Expr} {leftValue rightValue : Word}
    (greater : leftValue > rightValue)
    (leftEvaluation :
      Evaluates environment initialStore left (.word leftValue) intermediateStore)
    (rightEvaluation :
      Evaluates environment intermediateStore right (.word rightValue) finalStore) :
    Evaluates environment initialStore (left.wordGtFlag right)
      (.word (Word.ofNatModulo 1)) finalStore := by
  simpa [greater] using leftEvaluation.wordGtFlag rightEvaluation

theorem wordGtFlag_not_gt
    {environment : Environment} {initialStore intermediateStore finalStore : Store}
    {left right : Expr} {leftValue rightValue : Word}
    (notGreater : ¬ leftValue > rightValue)
    (leftEvaluation :
      Evaluates environment initialStore left (.word leftValue) intermediateStore)
    (rightEvaluation :
      Evaluates environment intermediateStore right (.word rightValue) finalStore) :
    Evaluates environment initialStore (left.wordGtFlag right)
      (.word Word.zero) finalStore := by
  simpa [notGreater] using leftEvaluation.wordGtFlag rightEvaluation

end Evaluates

@[simp] theorem Expr.rename_wordEqFlag
    (left right : Expr) (mapping : Renaming) :
    (left.wordEqFlag right).rename mapping =
      (left.rename mapping).wordEqFlag (right.rename mapping) := by
  rw [Expr.wordEqFlag_expansion, Expr.rename_boolToWord]
  simp [Expr.rename, Expr.wordEqFlag_expansion]

@[simp] theorem Expr.rename_wordGtFlag
    (left right : Expr) (mapping : Renaming) :
    (left.wordGtFlag right).rename mapping =
      (left.rename mapping).wordGtFlag (right.rename mapping) := by
  rw [Expr.wordGtFlag_expansion, Expr.rename_boolToWord]
  simp [Expr.rename, Expr.wordGtFlag_expansion]

@[simp] theorem Expr.weakenAt_wordEqFlag
    (left right : Expr) (cutoff : Nat) :
    (left.wordEqFlag right).weakenAt cutoff =
      (left.weakenAt cutoff).wordEqFlag (right.weakenAt cutoff) := by
  simp [Expr.wordEqFlag, Expr.boolToWord, Expr.weakenAt]

@[simp] theorem Expr.weakenAt_wordGtFlag
    (left right : Expr) (cutoff : Nat) :
    (left.wordGtFlag right).weakenAt cutoff =
      (left.weakenAt cutoff).wordGtFlag (right.weakenAt cutoff) := by
  simp [Expr.wordGtFlag, Expr.boolToWord, Expr.weakenAt]

end Solcore.Core
