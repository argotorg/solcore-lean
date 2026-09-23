import Solcore.Core.Conversions
import Solcore.Core.DirectWordComparisons
import Solcore.Core.Renaming
import Solcore.Core.RenamingInsertion
import Solcore.Core.SignedComparison

/-!
# Derived comparisons

Static and dynamic proof interfaces for boolean- and word-valued derived
comparisons, including signed and non-strict variants.
-/

set_option autoImplicit false

/-!
## Boolean comparison builders and static laws
-/

namespace Solcore.Core

/-! Static proof interface for the derived boolean-valued word comparisons. -/

@[simp] theorem Expr.wordNe_expansion (left right : Expr) :
    left.wordNe right = .unary .boolNot (.binary .wordEq left right) :=
  rfl

@[simp] theorem Expr.wordLt_expansion (left right : Expr) :
    left.wordLt right =
      .letE left
        (.letE (right.weakenAt 0)
          (.binary .wordGt (.var 0) (.var 1))) :=
  rfl

@[simp] theorem Expr.wordLe_expansion (left right : Expr) :
    left.wordLe right = .unary .boolNot (.binary .wordGt left right) :=
  rfl

@[simp] theorem Expr.wordGe_expansion (left right : Expr) :
    left.wordGe right =
      .unary .boolNot
        (.letE left
          (.letE (right.weakenAt 0)
            (.binary .wordGt (.var 0) (.var 1)))) :=
  rfl

namespace HasType

theorem wordNe
    {context : Context} {definitions : DataEnvironment} {left right : Expr}
    (leftTyping : HasType context left .word definitions)
    (rightTyping : HasType context right .word definitions) :
    HasType context (left.wordNe right) .bool definitions :=
  .unary (.binary leftTyping rightTyping)

theorem wordLt
    {context : Context} {definitions : DataEnvironment} {left right : Expr}
    (leftTyping : HasType context left .word definitions)
    (rightTyping : HasType context right .word definitions) :
    HasType context (left.wordLt right) .bool definitions := by
  rw [Expr.wordLt_expansion]
  apply HasType.letE leftTyping
  apply HasType.letE
  · simpa [Context.insertAt] using
      rightTyping.weakenAt (inserted := .word) 0
  · exact .binary (.var (by simp [BinaryOp.leftType]))
      (.var (by simp [BinaryOp.rightType]))

theorem wordLe
    {context : Context} {definitions : DataEnvironment} {left right : Expr}
    (leftTyping : HasType context left .word definitions)
    (rightTyping : HasType context right .word definitions) :
    HasType context (left.wordLe right) .bool definitions :=
  .unary (.binary leftTyping rightTyping)

theorem wordGe
    {context : Context} {definitions : DataEnvironment} {left right : Expr}
    (leftTyping : HasType context left .word definitions)
    (rightTyping : HasType context right .word definitions) :
    HasType context (left.wordGe right) .bool definitions := by
  change HasType context (.unary .boolNot (left.wordLt right)) .bool definitions
  exact .unary (leftTyping.wordLt rightTyping)

end HasType

theorem infer_wordNe
    {context : Context} {definitions : DataEnvironment} {left right : Expr}
    (leftInferred : infer? context left definitions = some .word)
    (rightInferred : infer? context right definitions = some .word) :
    infer? context (left.wordNe right) definitions = some .bool :=
  infer_complete ((infer_sound leftInferred).wordNe (infer_sound rightInferred))

theorem infer_wordLt
    {context : Context} {definitions : DataEnvironment} {left right : Expr}
    (leftInferred : infer? context left definitions = some .word)
    (rightInferred : infer? context right definitions = some .word) :
    infer? context (left.wordLt right) definitions = some .bool :=
  infer_complete ((infer_sound leftInferred).wordLt (infer_sound rightInferred))

theorem infer_wordLe
    {context : Context} {definitions : DataEnvironment} {left right : Expr}
    (leftInferred : infer? context left definitions = some .word)
    (rightInferred : infer? context right definitions = some .word) :
    infer? context (left.wordLe right) definitions = some .bool :=
  infer_complete ((infer_sound leftInferred).wordLe (infer_sound rightInferred))

theorem infer_wordGe
    {context : Context} {definitions : DataEnvironment} {left right : Expr}
    (leftInferred : infer? context left definitions = some .word)
    (rightInferred : infer? context right definitions = some .word) :
    infer? context (left.wordGe right) definitions = some .bool :=
  infer_complete ((infer_sound leftInferred).wordGe (infer_sound rightInferred))

@[simp] theorem Expr.rename_weakenAt_zero
    (expr : Expr) (mapping : Renaming) :
    (expr.weakenAt 0).rename mapping.lift =
      (expr.rename mapping).weakenAt 0 := by
  rw [← Expr.rename_insertion, ← Expr.rename_insertion,
    Expr.rename_comp, Expr.rename_comp,
    Renaming.lift_comp_insertion_zero]

@[simp] theorem Expr.rename_wordNe
    (left right : Expr) (mapping : Renaming) :
    (left.wordNe right).rename mapping =
      (left.rename mapping).wordNe (right.rename mapping) := by
  simp [Expr.wordNe, Expr.rename]

@[simp] theorem Expr.rename_wordLt
    (left right : Expr) (mapping : Renaming) :
    (left.wordLt right).rename mapping =
      (left.rename mapping).wordLt (right.rename mapping) := by
  rw [Expr.wordLt_expansion, Expr.wordLt_expansion]
  simp [Expr.rename, Renaming.lift]

@[simp] theorem Expr.rename_wordLe
    (left right : Expr) (mapping : Renaming) :
    (left.wordLe right).rename mapping =
      (left.rename mapping).wordLe (right.rename mapping) := by
  simp [Expr.wordLe, Expr.rename]

@[simp] theorem Expr.rename_wordGe
    (left right : Expr) (mapping : Renaming) :
    (left.wordGe right).rename mapping =
      (left.rename mapping).wordGe (right.rename mapping) := by
  rw [Expr.wordGe_expansion, Expr.wordGe_expansion]
  simp [Expr.rename, Renaming.lift]

@[simp] theorem Expr.weakenAt_wordNe
    (left right : Expr) (cutoff : Nat) :
    (left.wordNe right).weakenAt cutoff =
      (left.weakenAt cutoff).wordNe (right.weakenAt cutoff) := by
  simpa [← Expr.rename_insertion] using
    Expr.rename_wordNe left right (Renaming.insertion cutoff)

@[simp] theorem Expr.weakenAt_wordLt
    (left right : Expr) (cutoff : Nat) :
    (left.wordLt right).weakenAt cutoff =
      (left.weakenAt cutoff).wordLt (right.weakenAt cutoff) := by
  simpa [← Expr.rename_insertion] using
    Expr.rename_wordLt left right (Renaming.insertion cutoff)

@[simp] theorem Expr.weakenAt_wordLe
    (left right : Expr) (cutoff : Nat) :
    (left.wordLe right).weakenAt cutoff =
      (left.weakenAt cutoff).wordLe (right.weakenAt cutoff) := by
  simpa [← Expr.rename_insertion] using
    Expr.rename_wordLe left right (Renaming.insertion cutoff)

@[simp] theorem Expr.weakenAt_wordGe
    (left right : Expr) (cutoff : Nat) :
    (left.wordGe right).weakenAt cutoff =
      (left.weakenAt cutoff).wordGe (right.weakenAt cutoff) := by
  simpa [← Expr.rename_insertion] using
    Expr.rename_wordGe left right (Renaming.insertion cutoff)

end Solcore.Core

/-!
## Signed strict comparison builders and static laws
-/

namespace Solcore.Core

/-! Static proof interface for derived signed word less-than. -/

@[simp] theorem Expr.wordSlt_expansion (left right : Expr) :
    left.wordSlt right =
      .letE left
        (.letE (right.weakenAt 0)
          (.binary .wordSgt (.var 0) (.var 1))) :=
  rfl

namespace HasType

theorem wordSlt
    {context : Context} {definitions : DataEnvironment} {left right : Expr}
    (leftTyping : HasType context left .word definitions)
    (rightTyping : HasType context right .word definitions) :
    HasType context (left.wordSlt right) .bool definitions := by
  rw [Expr.wordSlt_expansion]
  apply HasType.letE leftTyping
  apply HasType.letE
  · simpa [Context.insertAt] using
      rightTyping.weakenAt (inserted := .word) 0
  · exact .binary (.var (by simp [BinaryOp.leftType]))
      (.var (by simp [BinaryOp.rightType]))

end HasType

theorem infer_wordSlt
    {context : Context} {definitions : DataEnvironment} {left right : Expr}
    (leftInferred : infer? context left definitions = some .word)
    (rightInferred : infer? context right definitions = some .word) :
    infer? context (left.wordSlt right) definitions = some .bool :=
  infer_complete
    ((infer_sound leftInferred).wordSlt (infer_sound rightInferred))

@[simp] theorem Expr.rename_wordSlt
    (left right : Expr) (mapping : Renaming) :
    (left.wordSlt right).rename mapping =
      (left.rename mapping).wordSlt (right.rename mapping) := by
  rw [Expr.wordSlt_expansion, Expr.wordSlt_expansion]
  simp [Expr.rename, Renaming.lift]

@[simp] theorem Expr.weakenAt_wordSlt
    (left right : Expr) (cutoff : Nat) :
    (left.wordSlt right).weakenAt cutoff =
      (left.weakenAt cutoff).wordSlt (right.weakenAt cutoff) := by
  simpa [← Expr.rename_insertion] using
    Expr.rename_wordSlt left right (Renaming.insertion cutoff)

end Solcore.Core

/-!
## Signed non-strict comparison builders and static laws
-/

namespace Solcore.Core

/-! Static proof interface for derived signed non-strict word comparisons. -/

@[simp] theorem Expr.wordSle_expansion (left right : Expr) :
    left.wordSle right =
      .unary .boolNot (.binary .wordSgt left right) :=
  rfl

@[simp] theorem Expr.wordSge_expansion (left right : Expr) :
    left.wordSge right = .unary .boolNot (left.wordSlt right) :=
  rfl

namespace HasType

theorem wordSle
    {context : Context} {definitions : DataEnvironment} {left right : Expr}
    (leftTyping : HasType context left .word definitions)
    (rightTyping : HasType context right .word definitions) :
    HasType context (left.wordSle right) .bool definitions :=
  .unary (.binary leftTyping rightTyping)

theorem wordSge
    {context : Context} {definitions : DataEnvironment} {left right : Expr}
    (leftTyping : HasType context left .word definitions)
    (rightTyping : HasType context right .word definitions) :
    HasType context (left.wordSge right) .bool definitions :=
  .unary (leftTyping.wordSlt rightTyping)

end HasType

theorem infer_wordSle
    {context : Context} {definitions : DataEnvironment} {left right : Expr}
    (leftInferred : infer? context left definitions = some .word)
    (rightInferred : infer? context right definitions = some .word) :
    infer? context (left.wordSle right) definitions = some .bool :=
  infer_complete
    ((infer_sound leftInferred).wordSle (infer_sound rightInferred))

theorem infer_wordSge
    {context : Context} {definitions : DataEnvironment} {left right : Expr}
    (leftInferred : infer? context left definitions = some .word)
    (rightInferred : infer? context right definitions = some .word) :
    infer? context (left.wordSge right) definitions = some .bool :=
  infer_complete
    ((infer_sound leftInferred).wordSge (infer_sound rightInferred))

@[simp] theorem Expr.rename_wordSle
    (left right : Expr) (mapping : Renaming) :
    (left.wordSle right).rename mapping =
      (left.rename mapping).wordSle (right.rename mapping) := by
  simp [Expr.wordSle, Expr.rename]

@[simp] theorem Expr.rename_wordSge
    (left right : Expr) (mapping : Renaming) :
    (left.wordSge right).rename mapping =
      (left.rename mapping).wordSge (right.rename mapping) := by
  rw [Expr.wordSge_expansion, Expr.wordSge_expansion]
  simp only [Expr.rename]
  rw [Expr.rename_wordSlt]

@[simp] theorem Expr.weakenAt_wordSle
    (left right : Expr) (cutoff : Nat) :
    (left.wordSle right).weakenAt cutoff =
      (left.weakenAt cutoff).wordSle (right.weakenAt cutoff) := by
  simpa [← Expr.rename_insertion] using
    Expr.rename_wordSle left right (Renaming.insertion cutoff)

@[simp] theorem Expr.weakenAt_wordSge
    (left right : Expr) (cutoff : Nat) :
    (left.wordSge right).weakenAt cutoff =
      (left.weakenAt cutoff).wordSge (right.weakenAt cutoff) := by
  simpa [← Expr.rename_insertion] using
    Expr.rename_wordSge left right (Renaming.insertion cutoff)

end Solcore.Core

/-!
## Primitive comparison flags
-/

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
  (leftEvaluation.wordEq rightEvaluation).boolToWord

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
  (leftEvaluation.wordGt rightEvaluation).boolToWord

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

/-!
## Derived unsigned comparison flags
-/

namespace Solcore.Core

/-! Static proof interface for derived word-valued comparison flags. -/

@[simp] theorem Expr.wordNeFlag_expansion (left right : Expr) :
    left.wordNeFlag right = (left.wordNe right).boolToWord :=
  rfl

@[simp] theorem Expr.wordLtFlag_expansion (left right : Expr) :
    left.wordLtFlag right = (left.wordLt right).boolToWord :=
  rfl

@[simp] theorem Expr.wordLeFlag_expansion (left right : Expr) :
    left.wordLeFlag right = (left.wordLe right).boolToWord :=
  rfl

@[simp] theorem Expr.wordGeFlag_expansion (left right : Expr) :
    left.wordGeFlag right = (left.wordGe right).boolToWord :=
  rfl

namespace HasType

theorem wordNeFlag
    {context : Context} {definitions : DataEnvironment} {left right : Expr}
    (leftTyping : HasType context left .word definitions)
    (rightTyping : HasType context right .word definitions) :
    HasType context (left.wordNeFlag right) .word definitions :=
  HasType.boolToWord (leftTyping.wordNe rightTyping)

theorem wordLtFlag
    {context : Context} {definitions : DataEnvironment} {left right : Expr}
    (leftTyping : HasType context left .word definitions)
    (rightTyping : HasType context right .word definitions) :
    HasType context (left.wordLtFlag right) .word definitions :=
  HasType.boolToWord (leftTyping.wordLt rightTyping)

theorem wordLeFlag
    {context : Context} {definitions : DataEnvironment} {left right : Expr}
    (leftTyping : HasType context left .word definitions)
    (rightTyping : HasType context right .word definitions) :
    HasType context (left.wordLeFlag right) .word definitions :=
  HasType.boolToWord (leftTyping.wordLe rightTyping)

theorem wordGeFlag
    {context : Context} {definitions : DataEnvironment} {left right : Expr}
    (leftTyping : HasType context left .word definitions)
    (rightTyping : HasType context right .word definitions) :
    HasType context (left.wordGeFlag right) .word definitions :=
  HasType.boolToWord (leftTyping.wordGe rightTyping)

end HasType

theorem infer_wordNeFlag
    {context : Context} {definitions : DataEnvironment} {left right : Expr}
    (leftInferred : infer? context left definitions = some .word)
    (rightInferred : infer? context right definitions = some .word) :
    infer? context (left.wordNeFlag right) definitions = some .word :=
  infer_complete
    ((infer_sound leftInferred).wordNeFlag (infer_sound rightInferred))

theorem infer_wordLtFlag
    {context : Context} {definitions : DataEnvironment} {left right : Expr}
    (leftInferred : infer? context left definitions = some .word)
    (rightInferred : infer? context right definitions = some .word) :
    infer? context (left.wordLtFlag right) definitions = some .word :=
  infer_complete
    ((infer_sound leftInferred).wordLtFlag (infer_sound rightInferred))

theorem infer_wordLeFlag
    {context : Context} {definitions : DataEnvironment} {left right : Expr}
    (leftInferred : infer? context left definitions = some .word)
    (rightInferred : infer? context right definitions = some .word) :
    infer? context (left.wordLeFlag right) definitions = some .word :=
  infer_complete
    ((infer_sound leftInferred).wordLeFlag (infer_sound rightInferred))

theorem infer_wordGeFlag
    {context : Context} {definitions : DataEnvironment} {left right : Expr}
    (leftInferred : infer? context left definitions = some .word)
    (rightInferred : infer? context right definitions = some .word) :
    infer? context (left.wordGeFlag right) definitions = some .word :=
  infer_complete
    ((infer_sound leftInferred).wordGeFlag (infer_sound rightInferred))

@[simp] theorem Expr.rename_wordNeFlag
    (left right : Expr) (mapping : Renaming) :
    (left.wordNeFlag right).rename mapping =
      (left.rename mapping).wordNeFlag (right.rename mapping) := by
  rw [Expr.wordNeFlag_expansion, Expr.rename_boolToWord,
    Expr.rename_wordNe, Expr.wordNeFlag_expansion]

@[simp] theorem Expr.rename_wordLtFlag
    (left right : Expr) (mapping : Renaming) :
    (left.wordLtFlag right).rename mapping =
      (left.rename mapping).wordLtFlag (right.rename mapping) := by
  rw [Expr.wordLtFlag_expansion, Expr.rename_boolToWord,
    Expr.rename_wordLt, Expr.wordLtFlag_expansion]

@[simp] theorem Expr.rename_wordLeFlag
    (left right : Expr) (mapping : Renaming) :
    (left.wordLeFlag right).rename mapping =
      (left.rename mapping).wordLeFlag (right.rename mapping) := by
  rw [Expr.wordLeFlag_expansion, Expr.rename_boolToWord,
    Expr.rename_wordLe, Expr.wordLeFlag_expansion]

@[simp] theorem Expr.rename_wordGeFlag
    (left right : Expr) (mapping : Renaming) :
    (left.wordGeFlag right).rename mapping =
      (left.rename mapping).wordGeFlag (right.rename mapping) := by
  rw [Expr.wordGeFlag_expansion, Expr.rename_boolToWord,
    Expr.rename_wordGe, Expr.wordGeFlag_expansion]

@[simp] theorem Expr.weakenAt_wordNeFlag
    (left right : Expr) (cutoff : Nat) :
    (left.wordNeFlag right).weakenAt cutoff =
      (left.weakenAt cutoff).wordNeFlag (right.weakenAt cutoff) := by
  simpa [← Expr.rename_insertion] using
    Expr.rename_wordNeFlag left right (Renaming.insertion cutoff)

@[simp] theorem Expr.weakenAt_wordLtFlag
    (left right : Expr) (cutoff : Nat) :
    (left.wordLtFlag right).weakenAt cutoff =
      (left.weakenAt cutoff).wordLtFlag (right.weakenAt cutoff) := by
  simpa [← Expr.rename_insertion] using
    Expr.rename_wordLtFlag left right (Renaming.insertion cutoff)

@[simp] theorem Expr.weakenAt_wordLeFlag
    (left right : Expr) (cutoff : Nat) :
    (left.wordLeFlag right).weakenAt cutoff =
      (left.weakenAt cutoff).wordLeFlag (right.weakenAt cutoff) := by
  simpa [← Expr.rename_insertion] using
    Expr.rename_wordLeFlag left right (Renaming.insertion cutoff)

@[simp] theorem Expr.weakenAt_wordGeFlag
    (left right : Expr) (cutoff : Nat) :
    (left.wordGeFlag right).weakenAt cutoff =
      (left.weakenAt cutoff).wordGeFlag (right.weakenAt cutoff) := by
  simpa [← Expr.rename_insertion] using
    Expr.rename_wordGeFlag left right (Renaming.insertion cutoff)

end Solcore.Core

/-!
## Signed comparison flags
-/

namespace Solcore.Core

/-! Static proof interface for word-valued signed comparison flags. -/

@[simp] theorem Expr.wordSgtFlag_expansion (left right : Expr) :
    left.wordSgtFlag right =
      (Expr.binary .wordSgt left right).boolToWord :=
  rfl

@[simp] theorem Expr.wordSltFlag_expansion (left right : Expr) :
    left.wordSltFlag right = (left.wordSlt right).boolToWord :=
  rfl

namespace HasType

theorem wordSgtFlag
    {context : Context} {definitions : DataEnvironment} {left right : Expr}
    (leftTyping : HasType context left .word definitions)
    (rightTyping : HasType context right .word definitions) :
    HasType context (left.wordSgtFlag right) .word definitions :=
  HasType.boolToWord (HasType.binary leftTyping rightTyping)

theorem wordSltFlag
    {context : Context} {definitions : DataEnvironment} {left right : Expr}
    (leftTyping : HasType context left .word definitions)
    (rightTyping : HasType context right .word definitions) :
    HasType context (left.wordSltFlag right) .word definitions :=
  HasType.boolToWord (leftTyping.wordSlt rightTyping)

end HasType

theorem infer_wordSgtFlag
    {context : Context} {definitions : DataEnvironment} {left right : Expr}
    (leftInferred : infer? context left definitions = some .word)
    (rightInferred : infer? context right definitions = some .word) :
    infer? context (left.wordSgtFlag right) definitions = some .word :=
  infer_complete
    ((infer_sound leftInferred).wordSgtFlag (infer_sound rightInferred))

theorem infer_wordSltFlag
    {context : Context} {definitions : DataEnvironment} {left right : Expr}
    (leftInferred : infer? context left definitions = some .word)
    (rightInferred : infer? context right definitions = some .word) :
    infer? context (left.wordSltFlag right) definitions = some .word :=
  infer_complete
    ((infer_sound leftInferred).wordSltFlag (infer_sound rightInferred))

@[simp] theorem Expr.rename_wordSgtFlag
    (left right : Expr) (mapping : Renaming) :
    (left.wordSgtFlag right).rename mapping =
      (left.rename mapping).wordSgtFlag (right.rename mapping) := by
  rw [Expr.wordSgtFlag_expansion, Expr.rename_boolToWord]
  simp [Expr.rename, Expr.wordSgtFlag_expansion]

@[simp] theorem Expr.rename_wordSltFlag
    (left right : Expr) (mapping : Renaming) :
    (left.wordSltFlag right).rename mapping =
      (left.rename mapping).wordSltFlag (right.rename mapping) := by
  rw [Expr.wordSltFlag_expansion, Expr.rename_boolToWord,
    Expr.rename_wordSlt, Expr.wordSltFlag_expansion]

@[simp] theorem Expr.weakenAt_wordSgtFlag
    (left right : Expr) (cutoff : Nat) :
    (left.wordSgtFlag right).weakenAt cutoff =
      (left.weakenAt cutoff).wordSgtFlag (right.weakenAt cutoff) := by
  simpa [← Expr.rename_insertion] using
    Expr.rename_wordSgtFlag left right (Renaming.insertion cutoff)

@[simp] theorem Expr.weakenAt_wordSltFlag
    (left right : Expr) (cutoff : Nat) :
    (left.wordSltFlag right).weakenAt cutoff =
      (left.weakenAt cutoff).wordSltFlag (right.weakenAt cutoff) := by
  simpa [← Expr.rename_insertion] using
    Expr.rename_wordSltFlag left right (Renaming.insertion cutoff)

end Solcore.Core

/-!
## Signed non-strict comparison flags
-/

namespace Solcore.Core

/-! Static proof interface for word-valued signed non-strict comparisons. -/

@[simp] theorem Expr.wordSleFlag_expansion (left right : Expr) :
    left.wordSleFlag right = (left.wordSle right).boolToWord :=
  rfl

@[simp] theorem Expr.wordSgeFlag_expansion (left right : Expr) :
    left.wordSgeFlag right = (left.wordSge right).boolToWord :=
  rfl

namespace HasType

theorem wordSleFlag
    {context : Context} {definitions : DataEnvironment} {left right : Expr}
    (leftTyping : HasType context left .word definitions)
    (rightTyping : HasType context right .word definitions) :
    HasType context (left.wordSleFlag right) .word definitions :=
  HasType.boolToWord (leftTyping.wordSle rightTyping)

theorem wordSgeFlag
    {context : Context} {definitions : DataEnvironment} {left right : Expr}
    (leftTyping : HasType context left .word definitions)
    (rightTyping : HasType context right .word definitions) :
    HasType context (left.wordSgeFlag right) .word definitions :=
  HasType.boolToWord (leftTyping.wordSge rightTyping)

end HasType

theorem infer_wordSleFlag
    {context : Context} {definitions : DataEnvironment} {left right : Expr}
    (leftInferred : infer? context left definitions = some .word)
    (rightInferred : infer? context right definitions = some .word) :
    infer? context (left.wordSleFlag right) definitions = some .word :=
  infer_complete
    ((infer_sound leftInferred).wordSleFlag (infer_sound rightInferred))

theorem infer_wordSgeFlag
    {context : Context} {definitions : DataEnvironment} {left right : Expr}
    (leftInferred : infer? context left definitions = some .word)
    (rightInferred : infer? context right definitions = some .word) :
    infer? context (left.wordSgeFlag right) definitions = some .word :=
  infer_complete
    ((infer_sound leftInferred).wordSgeFlag (infer_sound rightInferred))

@[simp] theorem Expr.rename_wordSleFlag
    (left right : Expr) (mapping : Renaming) :
    (left.wordSleFlag right).rename mapping =
      (left.rename mapping).wordSleFlag (right.rename mapping) := by
  rw [Expr.wordSleFlag_expansion, Expr.rename_boolToWord,
    Expr.rename_wordSle, Expr.wordSleFlag_expansion]

@[simp] theorem Expr.rename_wordSgeFlag
    (left right : Expr) (mapping : Renaming) :
    (left.wordSgeFlag right).rename mapping =
      (left.rename mapping).wordSgeFlag (right.rename mapping) := by
  rw [Expr.wordSgeFlag_expansion, Expr.rename_boolToWord,
    Expr.rename_wordSge, Expr.wordSgeFlag_expansion]

@[simp] theorem Expr.weakenAt_wordSleFlag
    (left right : Expr) (cutoff : Nat) :
    (left.wordSleFlag right).weakenAt cutoff =
      (left.weakenAt cutoff).wordSleFlag (right.weakenAt cutoff) := by
  simpa [← Expr.rename_insertion] using
    Expr.rename_wordSleFlag left right (Renaming.insertion cutoff)

@[simp] theorem Expr.weakenAt_wordSgeFlag
    (left right : Expr) (cutoff : Nat) :
    (left.wordSgeFlag right).weakenAt cutoff =
      (left.weakenAt cutoff).wordSgeFlag (right.weakenAt cutoff) := by
  simpa [← Expr.rename_insertion] using
    Expr.rename_wordSgeFlag left right (Renaming.insertion cutoff)

end Solcore.Core

/-!
## Unsigned comparison evaluation
-/

namespace Solcore.Core

/-! Store-threaded evaluation interface for the non-swapping comparisons. -/

namespace Evaluates

theorem wordNe
    {environment : Environment} {initialStore intermediateStore finalStore : Store}
    {left right : Expr} {leftValue rightValue : Word}
    (leftEvaluation :
      Evaluates environment initialStore left (.word leftValue) intermediateStore)
    (rightEvaluation :
      Evaluates environment intermediateStore right (.word rightValue) finalStore) :
    Evaluates environment initialStore (left.wordNe right)
      (.bool (!(leftValue == rightValue))) finalStore :=
  .unary (leftEvaluation.wordEq rightEvaluation) rfl

theorem wordNe_eq
    {environment : Environment} {initialStore intermediateStore finalStore : Store}
    {left right : Expr} {leftValue rightValue : Word}
    (valuesEqual : leftValue = rightValue)
    (leftEvaluation :
      Evaluates environment initialStore left (.word leftValue) intermediateStore)
    (rightEvaluation :
      Evaluates environment intermediateStore right (.word rightValue) finalStore) :
    Evaluates environment initialStore (left.wordNe right)
      (.bool false) finalStore := by
  subst rightValue
  simpa using leftEvaluation.wordNe rightEvaluation

theorem wordNe_ne
    {environment : Environment} {initialStore intermediateStore finalStore : Store}
    {left right : Expr} {leftValue rightValue : Word}
    (valuesNotEqual : leftValue ≠ rightValue)
    (leftEvaluation :
      Evaluates environment initialStore left (.word leftValue) intermediateStore)
    (rightEvaluation :
      Evaluates environment intermediateStore right (.word rightValue) finalStore) :
    Evaluates environment initialStore (left.wordNe right)
      (.bool true) finalStore := by
  have valuesBeq : (leftValue == rightValue) = false :=
    beq_eq_false_iff_ne.mpr valuesNotEqual
  simpa [valuesBeq] using leftEvaluation.wordNe rightEvaluation

theorem wordLe
    {environment : Environment} {initialStore intermediateStore finalStore : Store}
    {left right : Expr} {leftValue rightValue : Word}
    (leftEvaluation :
      Evaluates environment initialStore left (.word leftValue) intermediateStore)
    (rightEvaluation :
      Evaluates environment intermediateStore right (.word rightValue) finalStore) :
    Evaluates environment initialStore (left.wordLe right)
      (.bool (!(decide (leftValue > rightValue)))) finalStore :=
  .unary (leftEvaluation.wordGt rightEvaluation) rfl

theorem wordLe_gt
    {environment : Environment} {initialStore intermediateStore finalStore : Store}
    {left right : Expr} {leftValue rightValue : Word}
    (greater : leftValue > rightValue)
    (leftEvaluation :
      Evaluates environment initialStore left (.word leftValue) intermediateStore)
    (rightEvaluation :
      Evaluates environment intermediateStore right (.word rightValue) finalStore) :
    Evaluates environment initialStore (left.wordLe right)
      (.bool false) finalStore := by
  simpa [greater] using leftEvaluation.wordLe rightEvaluation

theorem wordLe_not_gt
    {environment : Environment} {initialStore intermediateStore finalStore : Store}
    {left right : Expr} {leftValue rightValue : Word}
    (notGreater : ¬ leftValue > rightValue)
    (leftEvaluation :
      Evaluates environment initialStore left (.word leftValue) intermediateStore)
    (rightEvaluation :
      Evaluates environment intermediateStore right (.word rightValue) finalStore) :
    Evaluates environment initialStore (left.wordLe right)
      (.bool true) finalStore := by
  simpa [notGreater] using leftEvaluation.wordLe rightEvaluation

theorem wordLt
    {definitions : DataEnvironment}
    {environment : Environment} {context : Context}
    {initialStore intermediateStore finalStore : Store}
    {world : StoreTyping} {left right : Expr} {leftValue rightValue : Word}
    (leftEvaluation :
      Evaluates environment initialStore left (.word leftValue) intermediateStore)
    (rightEvaluation :
      Evaluates environment intermediateStore right (.word rightValue) finalStore)
    (leftTyping : HasType context left .word definitions)
    (rightTyping : HasType context right .word definitions)
    (environmentTyping :
      RuntimeEnvironmentHasTypes world environment context definitions)
    (storeTyping : StoreHasTypes world initialStore) :
    Evaluates environment initialStore (left.wordLt right)
      (.bool (decide (rightValue > leftValue))) finalStore := by
  obtain ⟨intermediateWorld, extension, intermediateStoreTyping, _⟩ :=
    evaluation_preserves_type leftEvaluation leftTyping
      environmentTyping storeTyping
  have shiftedRightEvaluation :=
    rightEvaluation.weakenAt_zero_word rightTyping
      (environmentTyping.weaken extension) intermediateStoreTyping
      (.word leftValue)
  rw [Expr.wordLt_expansion]
  apply Evaluates.letE leftEvaluation
  apply Evaluates.letE shiftedRightEvaluation
  have rightVariable :
      Evaluates (.word rightValue :: .word leftValue :: environment)
        finalStore (.var 0) (.word rightValue) finalStore :=
    .var (by simp)
  have leftVariable :
      Evaluates (.word rightValue :: .word leftValue :: environment)
        finalStore (.var 1) (.word leftValue) finalStore :=
    .var (by simp)
  exact rightVariable.wordGt leftVariable

theorem wordGe
    {definitions : DataEnvironment}
    {environment : Environment} {context : Context}
    {initialStore intermediateStore finalStore : Store}
    {world : StoreTyping} {left right : Expr} {leftValue rightValue : Word}
    (leftEvaluation :
      Evaluates environment initialStore left (.word leftValue) intermediateStore)
    (rightEvaluation :
      Evaluates environment intermediateStore right (.word rightValue) finalStore)
    (leftTyping : HasType context left .word definitions)
    (rightTyping : HasType context right .word definitions)
    (environmentTyping :
      RuntimeEnvironmentHasTypes world environment context definitions)
    (storeTyping : StoreHasTypes world initialStore) :
    Evaluates environment initialStore (left.wordGe right)
      (.bool (!(decide (rightValue > leftValue)))) finalStore := by
  change Evaluates environment initialStore
    (.unary .boolNot (left.wordLt right)) _ finalStore
  exact .unary
    (leftEvaluation.wordLt rightEvaluation leftTyping rightTyping
      environmentTyping storeTyping) rfl

theorem wordLt_lt
    {definitions : DataEnvironment}
    {environment : Environment} {context : Context}
    {initialStore intermediateStore finalStore : Store}
    {world : StoreTyping} {left right : Expr} {leftValue rightValue : Word}
    (less : leftValue < rightValue)
    (leftEvaluation :
      Evaluates environment initialStore left (.word leftValue) intermediateStore)
    (rightEvaluation :
      Evaluates environment intermediateStore right (.word rightValue) finalStore)
    (leftTyping : HasType context left .word definitions)
    (rightTyping : HasType context right .word definitions)
    (environmentTyping :
      RuntimeEnvironmentHasTypes world environment context definitions)
    (storeTyping : StoreHasTypes world initialStore) :
    Evaluates environment initialStore (left.wordLt right)
      (.bool true) finalStore := by
  simpa [less] using leftEvaluation.wordLt rightEvaluation
    leftTyping rightTyping environmentTyping storeTyping

theorem wordLt_not_lt
    {definitions : DataEnvironment}
    {environment : Environment} {context : Context}
    {initialStore intermediateStore finalStore : Store}
    {world : StoreTyping} {left right : Expr} {leftValue rightValue : Word}
    (notLess : ¬ leftValue < rightValue)
    (leftEvaluation :
      Evaluates environment initialStore left (.word leftValue) intermediateStore)
    (rightEvaluation :
      Evaluates environment intermediateStore right (.word rightValue) finalStore)
    (leftTyping : HasType context left .word definitions)
    (rightTyping : HasType context right .word definitions)
    (environmentTyping :
      RuntimeEnvironmentHasTypes world environment context definitions)
    (storeTyping : StoreHasTypes world initialStore) :
    Evaluates environment initialStore (left.wordLt right)
      (.bool false) finalStore := by
  simpa [notLess] using leftEvaluation.wordLt rightEvaluation
    leftTyping rightTyping environmentTyping storeTyping

theorem wordGe_lt
    {definitions : DataEnvironment}
    {environment : Environment} {context : Context}
    {initialStore intermediateStore finalStore : Store}
    {world : StoreTyping} {left right : Expr} {leftValue rightValue : Word}
    (less : leftValue < rightValue)
    (leftEvaluation :
      Evaluates environment initialStore left (.word leftValue) intermediateStore)
    (rightEvaluation :
      Evaluates environment intermediateStore right (.word rightValue) finalStore)
    (leftTyping : HasType context left .word definitions)
    (rightTyping : HasType context right .word definitions)
    (environmentTyping :
      RuntimeEnvironmentHasTypes world environment context definitions)
    (storeTyping : StoreHasTypes world initialStore) :
    Evaluates environment initialStore (left.wordGe right)
      (.bool false) finalStore := by
  simpa [less] using leftEvaluation.wordGe rightEvaluation
    leftTyping rightTyping environmentTyping storeTyping

theorem wordGe_not_lt
    {definitions : DataEnvironment}
    {environment : Environment} {context : Context}
    {initialStore intermediateStore finalStore : Store}
    {world : StoreTyping} {left right : Expr} {leftValue rightValue : Word}
    (notLess : ¬ leftValue < rightValue)
    (leftEvaluation :
      Evaluates environment initialStore left (.word leftValue) intermediateStore)
    (rightEvaluation :
      Evaluates environment intermediateStore right (.word rightValue) finalStore)
    (leftTyping : HasType context left .word definitions)
    (rightTyping : HasType context right .word definitions)
    (environmentTyping :
      RuntimeEnvironmentHasTypes world environment context definitions)
    (storeTyping : StoreHasTypes world initialStore) :
    Evaluates environment initialStore (left.wordGe right)
      (.bool true) finalStore := by
  simpa [notLess] using leftEvaluation.wordGe rightEvaluation
    leftTyping rightTyping environmentTyping storeTyping

end Evaluates

end Solcore.Core

/-!
## Signed strict comparison evaluation
-/

namespace Solcore.Core

/-! Store-threaded evaluation interface for derived signed word less-than. -/

namespace Evaluates

theorem wordSlt
    {definitions : DataEnvironment}
    {environment : Environment} {context : Context}
    {initialStore intermediateStore finalStore : Store}
    {world : StoreTyping} {left right : Expr} {leftValue rightValue : Word}
    (leftEvaluation :
      Evaluates environment initialStore left (.word leftValue) intermediateStore)
    (rightEvaluation :
      Evaluates environment intermediateStore right (.word rightValue) finalStore)
    (leftTyping : HasType context left .word definitions)
    (rightTyping : HasType context right .word definitions)
    (environmentTyping :
      RuntimeEnvironmentHasTypes world environment context definitions)
    (storeTyping : StoreHasTypes world initialStore) :
    Evaluates environment initialStore (left.wordSlt right)
      (.bool (rightValue.signedGt leftValue)) finalStore := by
  obtain ⟨intermediateWorld, extension, intermediateStoreTyping, _⟩ :=
    evaluation_preserves_type leftEvaluation leftTyping
      environmentTyping storeTyping
  have shiftedRightEvaluation :=
    rightEvaluation.weakenAt_zero_word rightTyping
      (environmentTyping.weaken extension) intermediateStoreTyping
      (.word leftValue)
  rw [Expr.wordSlt_expansion]
  apply Evaluates.letE leftEvaluation
  apply Evaluates.letE shiftedRightEvaluation
  have rightVariable :
      Evaluates (.word rightValue :: .word leftValue :: environment)
        finalStore (.var 0) (.word rightValue) finalStore :=
    .var (by simp)
  have leftVariable :
      Evaluates (.word rightValue :: .word leftValue :: environment)
        finalStore (.var 1) (.word leftValue) finalStore :=
    .var (by simp)
  exact rightVariable.wordSgt leftVariable

theorem wordSlt_both_nonnegative
    {definitions : DataEnvironment}
    {environment : Environment} {context : Context}
    {initialStore intermediateStore finalStore : Store}
    {world : StoreTyping} {left right : Expr} {leftValue rightValue : Word}
    (leftNonnegative : leftValue.val < 2 ^ 255)
    (rightNonnegative : rightValue.val < 2 ^ 255)
    (leftEvaluation :
      Evaluates environment initialStore left (.word leftValue) intermediateStore)
    (rightEvaluation :
      Evaluates environment intermediateStore right (.word rightValue) finalStore)
    (leftTyping : HasType context left .word definitions)
    (rightTyping : HasType context right .word definitions)
    (environmentTyping :
      RuntimeEnvironmentHasTypes world environment context definitions)
    (storeTyping : StoreHasTypes world initialStore) :
    Evaluates environment initialStore (left.wordSlt right)
      (.bool (decide (rightValue > leftValue))) finalStore := by
  simpa only [Word.signedGt_both_nonnegative
    rightValue leftValue rightNonnegative leftNonnegative] using
    leftEvaluation.wordSlt rightEvaluation leftTyping rightTyping
      environmentTyping storeTyping

theorem wordSlt_both_negative
    {definitions : DataEnvironment}
    {environment : Environment} {context : Context}
    {initialStore intermediateStore finalStore : Store}
    {world : StoreTyping} {left right : Expr} {leftValue rightValue : Word}
    (leftNegative : 2 ^ 255 ≤ leftValue.val)
    (rightNegative : 2 ^ 255 ≤ rightValue.val)
    (leftEvaluation :
      Evaluates environment initialStore left (.word leftValue) intermediateStore)
    (rightEvaluation :
      Evaluates environment intermediateStore right (.word rightValue) finalStore)
    (leftTyping : HasType context left .word definitions)
    (rightTyping : HasType context right .word definitions)
    (environmentTyping :
      RuntimeEnvironmentHasTypes world environment context definitions)
    (storeTyping : StoreHasTypes world initialStore) :
    Evaluates environment initialStore (left.wordSlt right)
      (.bool (decide (rightValue > leftValue))) finalStore := by
  simpa only [Word.signedGt_both_negative
    rightValue leftValue rightNegative leftNegative] using
    leftEvaluation.wordSlt rightEvaluation leftTyping rightTyping
      environmentTyping storeTyping

theorem wordSlt_nonnegative_negative
    {definitions : DataEnvironment}
    {environment : Environment} {context : Context}
    {initialStore intermediateStore finalStore : Store}
    {world : StoreTyping} {left right : Expr} {leftValue rightValue : Word}
    (leftNonnegative : leftValue.val < 2 ^ 255)
    (rightNegative : 2 ^ 255 ≤ rightValue.val)
    (leftEvaluation :
      Evaluates environment initialStore left (.word leftValue) intermediateStore)
    (rightEvaluation :
      Evaluates environment intermediateStore right (.word rightValue) finalStore)
    (leftTyping : HasType context left .word definitions)
    (rightTyping : HasType context right .word definitions)
    (environmentTyping :
      RuntimeEnvironmentHasTypes world environment context definitions)
    (storeTyping : StoreHasTypes world initialStore) :
    Evaluates environment initialStore (left.wordSlt right)
      (.bool false) finalStore := by
  simpa only [Word.signedGt_negative_nonnegative
    rightValue leftValue rightNegative leftNonnegative] using
    leftEvaluation.wordSlt rightEvaluation leftTyping rightTyping
      environmentTyping storeTyping

theorem wordSlt_negative_nonnegative
    {definitions : DataEnvironment}
    {environment : Environment} {context : Context}
    {initialStore intermediateStore finalStore : Store}
    {world : StoreTyping} {left right : Expr} {leftValue rightValue : Word}
    (leftNegative : 2 ^ 255 ≤ leftValue.val)
    (rightNonnegative : rightValue.val < 2 ^ 255)
    (leftEvaluation :
      Evaluates environment initialStore left (.word leftValue) intermediateStore)
    (rightEvaluation :
      Evaluates environment intermediateStore right (.word rightValue) finalStore)
    (leftTyping : HasType context left .word definitions)
    (rightTyping : HasType context right .word definitions)
    (environmentTyping :
      RuntimeEnvironmentHasTypes world environment context definitions)
    (storeTyping : StoreHasTypes world initialStore) :
    Evaluates environment initialStore (left.wordSlt right)
      (.bool true) finalStore := by
  simpa only [Word.signedGt_nonnegative_negative
    rightValue leftValue rightNonnegative leftNegative] using
    leftEvaluation.wordSlt rightEvaluation leftTyping rightTyping
      environmentTyping storeTyping

end Evaluates

end Solcore.Core

/-!
## Signed non-strict comparison evaluation
-/

namespace Solcore.Core
namespace Evaluates

/-! Store-threaded evaluation interface for signed non-strict comparisons. -/

theorem wordSle
    {environment : Environment} {initialStore intermediateStore finalStore : Store}
    {left right : Expr} {leftValue rightValue : Word}
    (leftEvaluation :
      Evaluates environment initialStore left (.word leftValue) intermediateStore)
    (rightEvaluation :
      Evaluates environment intermediateStore right (.word rightValue) finalStore) :
    Evaluates environment initialStore (left.wordSle right)
      (.bool (!(leftValue.signedGt rightValue))) finalStore :=
  .unary (leftEvaluation.wordSgt rightEvaluation) rfl

theorem wordSle_both_nonnegative
    {environment : Environment} {initialStore intermediateStore finalStore : Store}
    {left right : Expr} {leftValue rightValue : Word}
    (leftNonnegative : leftValue.val < 2 ^ 255)
    (rightNonnegative : rightValue.val < 2 ^ 255)
    (leftEvaluation :
      Evaluates environment initialStore left (.word leftValue) intermediateStore)
    (rightEvaluation :
      Evaluates environment intermediateStore right (.word rightValue) finalStore) :
    Evaluates environment initialStore (left.wordSle right)
      (.bool (!(decide (leftValue > rightValue)))) finalStore :=
  .unary (Evaluates.wordSgt_both_nonnegative
    leftNonnegative rightNonnegative leftEvaluation rightEvaluation) rfl

theorem wordSle_both_negative
    {environment : Environment} {initialStore intermediateStore finalStore : Store}
    {left right : Expr} {leftValue rightValue : Word}
    (leftNegative : 2 ^ 255 ≤ leftValue.val)
    (rightNegative : 2 ^ 255 ≤ rightValue.val)
    (leftEvaluation :
      Evaluates environment initialStore left (.word leftValue) intermediateStore)
    (rightEvaluation :
      Evaluates environment intermediateStore right (.word rightValue) finalStore) :
    Evaluates environment initialStore (left.wordSle right)
      (.bool (!(decide (leftValue > rightValue)))) finalStore :=
  .unary (Evaluates.wordSgt_both_negative
    leftNegative rightNegative leftEvaluation rightEvaluation) rfl

theorem wordSle_nonnegative_negative
    {environment : Environment} {initialStore intermediateStore finalStore : Store}
    {left right : Expr} {leftValue rightValue : Word}
    (leftNonnegative : leftValue.val < 2 ^ 255)
    (rightNegative : 2 ^ 255 ≤ rightValue.val)
    (leftEvaluation :
      Evaluates environment initialStore left (.word leftValue) intermediateStore)
    (rightEvaluation :
      Evaluates environment intermediateStore right (.word rightValue) finalStore) :
    Evaluates environment initialStore (left.wordSle right)
      (.bool false) finalStore :=
  .unary (Evaluates.wordSgt_nonnegative_negative
    leftNonnegative rightNegative leftEvaluation rightEvaluation) rfl

theorem wordSle_negative_nonnegative
    {environment : Environment} {initialStore intermediateStore finalStore : Store}
    {left right : Expr} {leftValue rightValue : Word}
    (leftNegative : 2 ^ 255 ≤ leftValue.val)
    (rightNonnegative : rightValue.val < 2 ^ 255)
    (leftEvaluation :
      Evaluates environment initialStore left (.word leftValue) intermediateStore)
    (rightEvaluation :
      Evaluates environment intermediateStore right (.word rightValue) finalStore) :
    Evaluates environment initialStore (left.wordSle right)
      (.bool true) finalStore :=
  .unary (Evaluates.wordSgt_negative_nonnegative
    leftNegative rightNonnegative leftEvaluation rightEvaluation) rfl

theorem wordSge
    {definitions : DataEnvironment} {environment : Environment} {context : Context}
    {initialStore intermediateStore finalStore : Store} {world : StoreTyping}
    {left right : Expr} {leftValue rightValue : Word}
    (leftEvaluation :
      Evaluates environment initialStore left (.word leftValue) intermediateStore)
    (rightEvaluation :
      Evaluates environment intermediateStore right (.word rightValue) finalStore)
    (leftTyping : HasType context left .word definitions)
    (rightTyping : HasType context right .word definitions)
    (environmentTyping :
      RuntimeEnvironmentHasTypes world environment context definitions)
    (storeTyping : StoreHasTypes world initialStore) :
    Evaluates environment initialStore (left.wordSge right)
      (.bool (!(rightValue.signedGt leftValue))) finalStore :=
  .unary (leftEvaluation.wordSlt rightEvaluation leftTyping rightTyping
    environmentTyping storeTyping) rfl

theorem wordSge_both_nonnegative
    {definitions : DataEnvironment} {environment : Environment} {context : Context}
    {initialStore intermediateStore finalStore : Store} {world : StoreTyping}
    {left right : Expr} {leftValue rightValue : Word}
    (leftNonnegative : leftValue.val < 2 ^ 255)
    (rightNonnegative : rightValue.val < 2 ^ 255)
    (leftEvaluation :
      Evaluates environment initialStore left (.word leftValue) intermediateStore)
    (rightEvaluation :
      Evaluates environment intermediateStore right (.word rightValue) finalStore)
    (leftTyping : HasType context left .word definitions)
    (rightTyping : HasType context right .word definitions)
    (environmentTyping :
      RuntimeEnvironmentHasTypes world environment context definitions)
    (storeTyping : StoreHasTypes world initialStore) :
    Evaluates environment initialStore (left.wordSge right)
      (.bool (!(decide (rightValue > leftValue)))) finalStore :=
  .unary (Evaluates.wordSlt_both_nonnegative
    leftNonnegative rightNonnegative leftEvaluation rightEvaluation
    leftTyping rightTyping environmentTyping storeTyping) rfl

theorem wordSge_both_negative
    {definitions : DataEnvironment} {environment : Environment} {context : Context}
    {initialStore intermediateStore finalStore : Store} {world : StoreTyping}
    {left right : Expr} {leftValue rightValue : Word}
    (leftNegative : 2 ^ 255 ≤ leftValue.val)
    (rightNegative : 2 ^ 255 ≤ rightValue.val)
    (leftEvaluation :
      Evaluates environment initialStore left (.word leftValue) intermediateStore)
    (rightEvaluation :
      Evaluates environment intermediateStore right (.word rightValue) finalStore)
    (leftTyping : HasType context left .word definitions)
    (rightTyping : HasType context right .word definitions)
    (environmentTyping :
      RuntimeEnvironmentHasTypes world environment context definitions)
    (storeTyping : StoreHasTypes world initialStore) :
    Evaluates environment initialStore (left.wordSge right)
      (.bool (!(decide (rightValue > leftValue)))) finalStore :=
  .unary (Evaluates.wordSlt_both_negative
    leftNegative rightNegative leftEvaluation rightEvaluation
    leftTyping rightTyping environmentTyping storeTyping) rfl

theorem wordSge_nonnegative_negative
    {definitions : DataEnvironment} {environment : Environment} {context : Context}
    {initialStore intermediateStore finalStore : Store} {world : StoreTyping}
    {left right : Expr} {leftValue rightValue : Word}
    (leftNonnegative : leftValue.val < 2 ^ 255)
    (rightNegative : 2 ^ 255 ≤ rightValue.val)
    (leftEvaluation :
      Evaluates environment initialStore left (.word leftValue) intermediateStore)
    (rightEvaluation :
      Evaluates environment intermediateStore right (.word rightValue) finalStore)
    (leftTyping : HasType context left .word definitions)
    (rightTyping : HasType context right .word definitions)
    (environmentTyping :
      RuntimeEnvironmentHasTypes world environment context definitions)
    (storeTyping : StoreHasTypes world initialStore) :
    Evaluates environment initialStore (left.wordSge right)
      (.bool true) finalStore :=
  .unary (Evaluates.wordSlt_nonnegative_negative
    leftNonnegative rightNegative leftEvaluation rightEvaluation
    leftTyping rightTyping environmentTyping storeTyping) rfl

theorem wordSge_negative_nonnegative
    {definitions : DataEnvironment} {environment : Environment} {context : Context}
    {initialStore intermediateStore finalStore : Store} {world : StoreTyping}
    {left right : Expr} {leftValue rightValue : Word}
    (leftNegative : 2 ^ 255 ≤ leftValue.val)
    (rightNonnegative : rightValue.val < 2 ^ 255)
    (leftEvaluation :
      Evaluates environment initialStore left (.word leftValue) intermediateStore)
    (rightEvaluation :
      Evaluates environment intermediateStore right (.word rightValue) finalStore)
    (leftTyping : HasType context left .word definitions)
    (rightTyping : HasType context right .word definitions)
    (environmentTyping :
      RuntimeEnvironmentHasTypes world environment context definitions)
    (storeTyping : StoreHasTypes world initialStore) :
    Evaluates environment initialStore (left.wordSge right)
      (.bool false) finalStore :=
  .unary (Evaluates.wordSlt_negative_nonnegative
    leftNegative rightNonnegative leftEvaluation rightEvaluation
    leftTyping rightTyping environmentTyping storeTyping) rfl

end Evaluates
end Solcore.Core

/-!
## Signed comparison flag evaluation
-/

namespace Solcore.Core
namespace Evaluates

/-! Store-threaded evaluation interface for signed word comparison flags. -/

theorem wordSgtFlag
    {environment : Environment} {initialStore intermediateStore finalStore : Store}
    {left right : Expr} {leftValue rightValue : Word}
    (leftEvaluation :
      Evaluates environment initialStore left (.word leftValue) intermediateStore)
    (rightEvaluation :
      Evaluates environment intermediateStore right (.word rightValue) finalStore) :
    Evaluates environment initialStore (left.wordSgtFlag right)
      (.word (if leftValue.signedGt rightValue then
        Word.ofNatModulo 1 else Word.zero)) finalStore :=
  (leftEvaluation.wordSgt rightEvaluation).boolToWord

theorem wordSgtFlag_both_nonnegative
    {environment : Environment} {initialStore intermediateStore finalStore : Store}
    {left right : Expr} {leftValue rightValue : Word}
    (leftNonnegative : leftValue.val < 2 ^ 255)
    (rightNonnegative : rightValue.val < 2 ^ 255)
    (leftEvaluation :
      Evaluates environment initialStore left (.word leftValue) intermediateStore)
    (rightEvaluation :
      Evaluates environment intermediateStore right (.word rightValue) finalStore) :
    Evaluates environment initialStore (left.wordSgtFlag right)
      (.word (if decide (leftValue > rightValue) then
        Word.ofNatModulo 1 else Word.zero)) finalStore :=
  (Evaluates.wordSgt_both_nonnegative leftNonnegative rightNonnegative
    leftEvaluation rightEvaluation).boolToWord

theorem wordSgtFlag_both_negative
    {environment : Environment} {initialStore intermediateStore finalStore : Store}
    {left right : Expr} {leftValue rightValue : Word}
    (leftNegative : 2 ^ 255 ≤ leftValue.val)
    (rightNegative : 2 ^ 255 ≤ rightValue.val)
    (leftEvaluation :
      Evaluates environment initialStore left (.word leftValue) intermediateStore)
    (rightEvaluation :
      Evaluates environment intermediateStore right (.word rightValue) finalStore) :
    Evaluates environment initialStore (left.wordSgtFlag right)
      (.word (if decide (leftValue > rightValue) then
        Word.ofNatModulo 1 else Word.zero)) finalStore :=
  (Evaluates.wordSgt_both_negative leftNegative rightNegative
    leftEvaluation rightEvaluation).boolToWord

theorem wordSgtFlag_nonnegative_negative
    {environment : Environment} {initialStore intermediateStore finalStore : Store}
    {left right : Expr} {leftValue rightValue : Word}
    (leftNonnegative : leftValue.val < 2 ^ 255)
    (rightNegative : 2 ^ 255 ≤ rightValue.val)
    (leftEvaluation :
      Evaluates environment initialStore left (.word leftValue) intermediateStore)
    (rightEvaluation :
      Evaluates environment intermediateStore right (.word rightValue) finalStore) :
    Evaluates environment initialStore (left.wordSgtFlag right)
      (.word (Word.ofNatModulo 1)) finalStore :=
  (Evaluates.wordSgt_nonnegative_negative leftNonnegative rightNegative
    leftEvaluation rightEvaluation).boolToWord_true

theorem wordSgtFlag_negative_nonnegative
    {environment : Environment} {initialStore intermediateStore finalStore : Store}
    {left right : Expr} {leftValue rightValue : Word}
    (leftNegative : 2 ^ 255 ≤ leftValue.val)
    (rightNonnegative : rightValue.val < 2 ^ 255)
    (leftEvaluation :
      Evaluates environment initialStore left (.word leftValue) intermediateStore)
    (rightEvaluation :
      Evaluates environment intermediateStore right (.word rightValue) finalStore) :
    Evaluates environment initialStore (left.wordSgtFlag right)
      (.word Word.zero) finalStore :=
  (Evaluates.wordSgt_negative_nonnegative leftNegative rightNonnegative
    leftEvaluation rightEvaluation).boolToWord_false

theorem wordSltFlag
    {definitions : DataEnvironment} {environment : Environment} {context : Context}
    {initialStore intermediateStore finalStore : Store} {world : StoreTyping}
    {left right : Expr} {leftValue rightValue : Word}
    (leftEvaluation :
      Evaluates environment initialStore left (.word leftValue) intermediateStore)
    (rightEvaluation :
      Evaluates environment intermediateStore right (.word rightValue) finalStore)
    (leftTyping : HasType context left .word definitions)
    (rightTyping : HasType context right .word definitions)
    (environmentTyping :
      RuntimeEnvironmentHasTypes world environment context definitions)
    (storeTyping : StoreHasTypes world initialStore) :
    Evaluates environment initialStore (left.wordSltFlag right)
      (.word (if rightValue.signedGt leftValue then
        Word.ofNatModulo 1 else Word.zero)) finalStore :=
  (leftEvaluation.wordSlt rightEvaluation leftTyping rightTyping
    environmentTyping storeTyping).boolToWord

theorem wordSltFlag_both_nonnegative
    {definitions : DataEnvironment} {environment : Environment} {context : Context}
    {initialStore intermediateStore finalStore : Store} {world : StoreTyping}
    {left right : Expr} {leftValue rightValue : Word}
    (leftNonnegative : leftValue.val < 2 ^ 255)
    (rightNonnegative : rightValue.val < 2 ^ 255)
    (leftEvaluation :
      Evaluates environment initialStore left (.word leftValue) intermediateStore)
    (rightEvaluation :
      Evaluates environment intermediateStore right (.word rightValue) finalStore)
    (leftTyping : HasType context left .word definitions)
    (rightTyping : HasType context right .word definitions)
    (environmentTyping :
      RuntimeEnvironmentHasTypes world environment context definitions)
    (storeTyping : StoreHasTypes world initialStore) :
    Evaluates environment initialStore (left.wordSltFlag right)
      (.word (if decide (rightValue > leftValue) then
        Word.ofNatModulo 1 else Word.zero)) finalStore :=
  (Evaluates.wordSlt_both_nonnegative leftNonnegative rightNonnegative
    leftEvaluation rightEvaluation leftTyping rightTyping
    environmentTyping storeTyping).boolToWord

theorem wordSltFlag_both_negative
    {definitions : DataEnvironment} {environment : Environment} {context : Context}
    {initialStore intermediateStore finalStore : Store} {world : StoreTyping}
    {left right : Expr} {leftValue rightValue : Word}
    (leftNegative : 2 ^ 255 ≤ leftValue.val)
    (rightNegative : 2 ^ 255 ≤ rightValue.val)
    (leftEvaluation :
      Evaluates environment initialStore left (.word leftValue) intermediateStore)
    (rightEvaluation :
      Evaluates environment intermediateStore right (.word rightValue) finalStore)
    (leftTyping : HasType context left .word definitions)
    (rightTyping : HasType context right .word definitions)
    (environmentTyping :
      RuntimeEnvironmentHasTypes world environment context definitions)
    (storeTyping : StoreHasTypes world initialStore) :
    Evaluates environment initialStore (left.wordSltFlag right)
      (.word (if decide (rightValue > leftValue) then
        Word.ofNatModulo 1 else Word.zero)) finalStore :=
  (Evaluates.wordSlt_both_negative leftNegative rightNegative
    leftEvaluation rightEvaluation leftTyping rightTyping
    environmentTyping storeTyping).boolToWord

theorem wordSltFlag_nonnegative_negative
    {definitions : DataEnvironment} {environment : Environment} {context : Context}
    {initialStore intermediateStore finalStore : Store} {world : StoreTyping}
    {left right : Expr} {leftValue rightValue : Word}
    (leftNonnegative : leftValue.val < 2 ^ 255)
    (rightNegative : 2 ^ 255 ≤ rightValue.val)
    (leftEvaluation :
      Evaluates environment initialStore left (.word leftValue) intermediateStore)
    (rightEvaluation :
      Evaluates environment intermediateStore right (.word rightValue) finalStore)
    (leftTyping : HasType context left .word definitions)
    (rightTyping : HasType context right .word definitions)
    (environmentTyping :
      RuntimeEnvironmentHasTypes world environment context definitions)
    (storeTyping : StoreHasTypes world initialStore) :
    Evaluates environment initialStore (left.wordSltFlag right)
      (.word Word.zero) finalStore :=
  (Evaluates.wordSlt_nonnegative_negative leftNonnegative rightNegative
    leftEvaluation rightEvaluation leftTyping rightTyping
    environmentTyping storeTyping).boolToWord_false

theorem wordSltFlag_negative_nonnegative
    {definitions : DataEnvironment} {environment : Environment} {context : Context}
    {initialStore intermediateStore finalStore : Store} {world : StoreTyping}
    {left right : Expr} {leftValue rightValue : Word}
    (leftNegative : 2 ^ 255 ≤ leftValue.val)
    (rightNonnegative : rightValue.val < 2 ^ 255)
    (leftEvaluation :
      Evaluates environment initialStore left (.word leftValue) intermediateStore)
    (rightEvaluation :
      Evaluates environment intermediateStore right (.word rightValue) finalStore)
    (leftTyping : HasType context left .word definitions)
    (rightTyping : HasType context right .word definitions)
    (environmentTyping :
      RuntimeEnvironmentHasTypes world environment context definitions)
    (storeTyping : StoreHasTypes world initialStore) :
    Evaluates environment initialStore (left.wordSltFlag right)
      (.word (Word.ofNatModulo 1)) finalStore :=
  (Evaluates.wordSlt_negative_nonnegative leftNegative rightNonnegative
    leftEvaluation rightEvaluation leftTyping rightTyping
    environmentTyping storeTyping).boolToWord_true

end Evaluates
end Solcore.Core

/-!
## Derived unsigned comparison flag evaluation
-/

namespace Solcore.Core
namespace Evaluates

/-! Store-threaded evaluation interface for derived word comparison flags. -/

theorem wordNeFlag
    {environment : Environment} {initialStore intermediateStore finalStore : Store}
    {left right : Expr} {leftValue rightValue : Word}
    (leftEvaluation :
      Evaluates environment initialStore left (.word leftValue) intermediateStore)
    (rightEvaluation :
      Evaluates environment intermediateStore right (.word rightValue) finalStore) :
    Evaluates environment initialStore (left.wordNeFlag right)
      (.word (if !(leftValue == rightValue) then
        Word.ofNatModulo 1 else Word.zero)) finalStore :=
  (leftEvaluation.wordNe rightEvaluation).boolToWord

theorem wordNeFlag_eq
    {environment : Environment} {initialStore intermediateStore finalStore : Store}
    {left right : Expr} {leftValue rightValue : Word}
    (equal : leftValue = rightValue)
    (leftEvaluation :
      Evaluates environment initialStore left (.word leftValue) intermediateStore)
    (rightEvaluation :
      Evaluates environment intermediateStore right (.word rightValue) finalStore) :
    Evaluates environment initialStore (left.wordNeFlag right)
      (.word Word.zero) finalStore :=
  (Evaluates.wordNe_eq equal leftEvaluation rightEvaluation).boolToWord_false

theorem wordNeFlag_ne
    {environment : Environment} {initialStore intermediateStore finalStore : Store}
    {left right : Expr} {leftValue rightValue : Word}
    (notEqual : leftValue ≠ rightValue)
    (leftEvaluation :
      Evaluates environment initialStore left (.word leftValue) intermediateStore)
    (rightEvaluation :
      Evaluates environment intermediateStore right (.word rightValue) finalStore) :
    Evaluates environment initialStore (left.wordNeFlag right)
      (.word (Word.ofNatModulo 1)) finalStore :=
  (Evaluates.wordNe_ne notEqual leftEvaluation rightEvaluation).boolToWord_true

theorem wordLeFlag
    {environment : Environment} {initialStore intermediateStore finalStore : Store}
    {left right : Expr} {leftValue rightValue : Word}
    (leftEvaluation :
      Evaluates environment initialStore left (.word leftValue) intermediateStore)
    (rightEvaluation :
      Evaluates environment intermediateStore right (.word rightValue) finalStore) :
    Evaluates environment initialStore (left.wordLeFlag right)
      (.word (if !(decide (leftValue > rightValue)) then
        Word.ofNatModulo 1 else Word.zero)) finalStore :=
  (leftEvaluation.wordLe rightEvaluation).boolToWord

theorem wordLeFlag_gt
    {environment : Environment} {initialStore intermediateStore finalStore : Store}
    {left right : Expr} {leftValue rightValue : Word}
    (greater : leftValue > rightValue)
    (leftEvaluation :
      Evaluates environment initialStore left (.word leftValue) intermediateStore)
    (rightEvaluation :
      Evaluates environment intermediateStore right (.word rightValue) finalStore) :
    Evaluates environment initialStore (left.wordLeFlag right)
      (.word Word.zero) finalStore :=
  (Evaluates.wordLe_gt greater leftEvaluation rightEvaluation).boolToWord_false

theorem wordLeFlag_not_gt
    {environment : Environment} {initialStore intermediateStore finalStore : Store}
    {left right : Expr} {leftValue rightValue : Word}
    (notGreater : ¬ leftValue > rightValue)
    (leftEvaluation :
      Evaluates environment initialStore left (.word leftValue) intermediateStore)
    (rightEvaluation :
      Evaluates environment intermediateStore right (.word rightValue) finalStore) :
    Evaluates environment initialStore (left.wordLeFlag right)
      (.word (Word.ofNatModulo 1)) finalStore :=
  (Evaluates.wordLe_not_gt notGreater leftEvaluation rightEvaluation).boolToWord_true

theorem wordLtFlag
    {definitions : DataEnvironment} {environment : Environment} {context : Context}
    {initialStore intermediateStore finalStore : Store} {world : StoreTyping}
    {left right : Expr} {leftValue rightValue : Word}
    (leftEvaluation :
      Evaluates environment initialStore left (.word leftValue) intermediateStore)
    (rightEvaluation :
      Evaluates environment intermediateStore right (.word rightValue) finalStore)
    (leftTyping : HasType context left .word definitions)
    (rightTyping : HasType context right .word definitions)
    (environmentTyping :
      RuntimeEnvironmentHasTypes world environment context definitions)
    (storeTyping : StoreHasTypes world initialStore) :
    Evaluates environment initialStore (left.wordLtFlag right)
      (.word (if decide (rightValue > leftValue) then
        Word.ofNatModulo 1 else Word.zero)) finalStore :=
  (leftEvaluation.wordLt rightEvaluation leftTyping rightTyping
    environmentTyping storeTyping).boolToWord

theorem wordLtFlag_lt
    {definitions : DataEnvironment} {environment : Environment} {context : Context}
    {initialStore intermediateStore finalStore : Store} {world : StoreTyping}
    {left right : Expr} {leftValue rightValue : Word}
    (less : leftValue < rightValue)
    (leftEvaluation :
      Evaluates environment initialStore left (.word leftValue) intermediateStore)
    (rightEvaluation :
      Evaluates environment intermediateStore right (.word rightValue) finalStore)
    (leftTyping : HasType context left .word definitions)
    (rightTyping : HasType context right .word definitions)
    (environmentTyping :
      RuntimeEnvironmentHasTypes world environment context definitions)
    (storeTyping : StoreHasTypes world initialStore) :
    Evaluates environment initialStore (left.wordLtFlag right)
      (.word (Word.ofNatModulo 1)) finalStore :=
  (Evaluates.wordLt_lt less leftEvaluation rightEvaluation leftTyping rightTyping
    environmentTyping storeTyping).boolToWord_true

theorem wordLtFlag_not_lt
    {definitions : DataEnvironment} {environment : Environment} {context : Context}
    {initialStore intermediateStore finalStore : Store} {world : StoreTyping}
    {left right : Expr} {leftValue rightValue : Word}
    (notLess : ¬ leftValue < rightValue)
    (leftEvaluation :
      Evaluates environment initialStore left (.word leftValue) intermediateStore)
    (rightEvaluation :
      Evaluates environment intermediateStore right (.word rightValue) finalStore)
    (leftTyping : HasType context left .word definitions)
    (rightTyping : HasType context right .word definitions)
    (environmentTyping :
      RuntimeEnvironmentHasTypes world environment context definitions)
    (storeTyping : StoreHasTypes world initialStore) :
    Evaluates environment initialStore (left.wordLtFlag right)
      (.word Word.zero) finalStore :=
  (Evaluates.wordLt_not_lt notLess leftEvaluation rightEvaluation
    leftTyping rightTyping environmentTyping storeTyping).boolToWord_false

theorem wordGeFlag
    {definitions : DataEnvironment} {environment : Environment} {context : Context}
    {initialStore intermediateStore finalStore : Store} {world : StoreTyping}
    {left right : Expr} {leftValue rightValue : Word}
    (leftEvaluation :
      Evaluates environment initialStore left (.word leftValue) intermediateStore)
    (rightEvaluation :
      Evaluates environment intermediateStore right (.word rightValue) finalStore)
    (leftTyping : HasType context left .word definitions)
    (rightTyping : HasType context right .word definitions)
    (environmentTyping :
      RuntimeEnvironmentHasTypes world environment context definitions)
    (storeTyping : StoreHasTypes world initialStore) :
    Evaluates environment initialStore (left.wordGeFlag right)
      (.word (if !(decide (rightValue > leftValue)) then
        Word.ofNatModulo 1 else Word.zero)) finalStore :=
  (leftEvaluation.wordGe rightEvaluation leftTyping rightTyping
    environmentTyping storeTyping).boolToWord

theorem wordGeFlag_lt
    {definitions : DataEnvironment} {environment : Environment} {context : Context}
    {initialStore intermediateStore finalStore : Store} {world : StoreTyping}
    {left right : Expr} {leftValue rightValue : Word}
    (less : leftValue < rightValue)
    (leftEvaluation :
      Evaluates environment initialStore left (.word leftValue) intermediateStore)
    (rightEvaluation :
      Evaluates environment intermediateStore right (.word rightValue) finalStore)
    (leftTyping : HasType context left .word definitions)
    (rightTyping : HasType context right .word definitions)
    (environmentTyping :
      RuntimeEnvironmentHasTypes world environment context definitions)
    (storeTyping : StoreHasTypes world initialStore) :
    Evaluates environment initialStore (left.wordGeFlag right)
      (.word Word.zero) finalStore :=
  (Evaluates.wordGe_lt less leftEvaluation rightEvaluation leftTyping rightTyping
    environmentTyping storeTyping).boolToWord_false

theorem wordGeFlag_not_lt
    {definitions : DataEnvironment} {environment : Environment} {context : Context}
    {initialStore intermediateStore finalStore : Store} {world : StoreTyping}
    {left right : Expr} {leftValue rightValue : Word}
    (notLess : ¬ leftValue < rightValue)
    (leftEvaluation :
      Evaluates environment initialStore left (.word leftValue) intermediateStore)
    (rightEvaluation :
      Evaluates environment intermediateStore right (.word rightValue) finalStore)
    (leftTyping : HasType context left .word definitions)
    (rightTyping : HasType context right .word definitions)
    (environmentTyping :
      RuntimeEnvironmentHasTypes world environment context definitions)
    (storeTyping : StoreHasTypes world initialStore) :
    Evaluates environment initialStore (left.wordGeFlag right)
      (.word (Word.ofNatModulo 1)) finalStore :=
  (Evaluates.wordGe_not_lt notLess leftEvaluation rightEvaluation
    leftTyping rightTyping environmentTyping storeTyping).boolToWord_true

end Evaluates
end Solcore.Core

/-!
## Signed non-strict comparison flag evaluation
-/

namespace Solcore.Core
namespace Evaluates

/-! Store-threaded evaluation interface for signed non-strict word flags. -/

theorem wordSleFlag
    {environment : Environment} {initialStore intermediateStore finalStore : Store}
    {left right : Expr} {leftValue rightValue : Word}
    (leftEvaluation :
      Evaluates environment initialStore left (.word leftValue) intermediateStore)
    (rightEvaluation :
      Evaluates environment intermediateStore right (.word rightValue) finalStore) :
    Evaluates environment initialStore (left.wordSleFlag right)
      (.word (if !(leftValue.signedGt rightValue) then
        Word.ofNatModulo 1 else Word.zero)) finalStore :=
  (leftEvaluation.wordSle rightEvaluation).boolToWord

theorem wordSleFlag_both_nonnegative
    {environment : Environment} {initialStore intermediateStore finalStore : Store}
    {left right : Expr} {leftValue rightValue : Word}
    (leftNonnegative : leftValue.val < 2 ^ 255)
    (rightNonnegative : rightValue.val < 2 ^ 255)
    (leftEvaluation :
      Evaluates environment initialStore left (.word leftValue) intermediateStore)
    (rightEvaluation :
      Evaluates environment intermediateStore right (.word rightValue) finalStore) :
    Evaluates environment initialStore (left.wordSleFlag right)
      (.word (if !(decide (leftValue > rightValue)) then
        Word.ofNatModulo 1 else Word.zero)) finalStore :=
  (Evaluates.wordSle_both_nonnegative leftNonnegative rightNonnegative
    leftEvaluation rightEvaluation).boolToWord

theorem wordSleFlag_both_negative
    {environment : Environment} {initialStore intermediateStore finalStore : Store}
    {left right : Expr} {leftValue rightValue : Word}
    (leftNegative : 2 ^ 255 ≤ leftValue.val)
    (rightNegative : 2 ^ 255 ≤ rightValue.val)
    (leftEvaluation :
      Evaluates environment initialStore left (.word leftValue) intermediateStore)
    (rightEvaluation :
      Evaluates environment intermediateStore right (.word rightValue) finalStore) :
    Evaluates environment initialStore (left.wordSleFlag right)
      (.word (if !(decide (leftValue > rightValue)) then
        Word.ofNatModulo 1 else Word.zero)) finalStore :=
  (Evaluates.wordSle_both_negative leftNegative rightNegative
    leftEvaluation rightEvaluation).boolToWord

theorem wordSleFlag_nonnegative_negative
    {environment : Environment} {initialStore intermediateStore finalStore : Store}
    {left right : Expr} {leftValue rightValue : Word}
    (leftNonnegative : leftValue.val < 2 ^ 255)
    (rightNegative : 2 ^ 255 ≤ rightValue.val)
    (leftEvaluation :
      Evaluates environment initialStore left (.word leftValue) intermediateStore)
    (rightEvaluation :
      Evaluates environment intermediateStore right (.word rightValue) finalStore) :
    Evaluates environment initialStore (left.wordSleFlag right)
      (.word Word.zero) finalStore :=
  (Evaluates.wordSle_nonnegative_negative leftNonnegative rightNegative
    leftEvaluation rightEvaluation).boolToWord_false

theorem wordSleFlag_negative_nonnegative
    {environment : Environment} {initialStore intermediateStore finalStore : Store}
    {left right : Expr} {leftValue rightValue : Word}
    (leftNegative : 2 ^ 255 ≤ leftValue.val)
    (rightNonnegative : rightValue.val < 2 ^ 255)
    (leftEvaluation :
      Evaluates environment initialStore left (.word leftValue) intermediateStore)
    (rightEvaluation :
      Evaluates environment intermediateStore right (.word rightValue) finalStore) :
    Evaluates environment initialStore (left.wordSleFlag right)
      (.word (Word.ofNatModulo 1)) finalStore :=
  (Evaluates.wordSle_negative_nonnegative leftNegative rightNonnegative
    leftEvaluation rightEvaluation).boolToWord_true

theorem wordSgeFlag
    {definitions : DataEnvironment} {environment : Environment} {context : Context}
    {initialStore intermediateStore finalStore : Store} {world : StoreTyping}
    {left right : Expr} {leftValue rightValue : Word}
    (leftEvaluation :
      Evaluates environment initialStore left (.word leftValue) intermediateStore)
    (rightEvaluation :
      Evaluates environment intermediateStore right (.word rightValue) finalStore)
    (leftTyping : HasType context left .word definitions)
    (rightTyping : HasType context right .word definitions)
    (environmentTyping :
      RuntimeEnvironmentHasTypes world environment context definitions)
    (storeTyping : StoreHasTypes world initialStore) :
    Evaluates environment initialStore (left.wordSgeFlag right)
      (.word (if !(rightValue.signedGt leftValue) then
        Word.ofNatModulo 1 else Word.zero)) finalStore :=
  (leftEvaluation.wordSge rightEvaluation leftTyping rightTyping
    environmentTyping storeTyping).boolToWord

theorem wordSgeFlag_both_nonnegative
    {definitions : DataEnvironment} {environment : Environment} {context : Context}
    {initialStore intermediateStore finalStore : Store} {world : StoreTyping}
    {left right : Expr} {leftValue rightValue : Word}
    (leftNonnegative : leftValue.val < 2 ^ 255)
    (rightNonnegative : rightValue.val < 2 ^ 255)
    (leftEvaluation :
      Evaluates environment initialStore left (.word leftValue) intermediateStore)
    (rightEvaluation :
      Evaluates environment intermediateStore right (.word rightValue) finalStore)
    (leftTyping : HasType context left .word definitions)
    (rightTyping : HasType context right .word definitions)
    (environmentTyping :
      RuntimeEnvironmentHasTypes world environment context definitions)
    (storeTyping : StoreHasTypes world initialStore) :
    Evaluates environment initialStore (left.wordSgeFlag right)
      (.word (if !(decide (rightValue > leftValue)) then
        Word.ofNatModulo 1 else Word.zero)) finalStore :=
  (Evaluates.wordSge_both_nonnegative leftNonnegative rightNonnegative
    leftEvaluation rightEvaluation leftTyping rightTyping
    environmentTyping storeTyping).boolToWord

theorem wordSgeFlag_both_negative
    {definitions : DataEnvironment} {environment : Environment} {context : Context}
    {initialStore intermediateStore finalStore : Store} {world : StoreTyping}
    {left right : Expr} {leftValue rightValue : Word}
    (leftNegative : 2 ^ 255 ≤ leftValue.val)
    (rightNegative : 2 ^ 255 ≤ rightValue.val)
    (leftEvaluation :
      Evaluates environment initialStore left (.word leftValue) intermediateStore)
    (rightEvaluation :
      Evaluates environment intermediateStore right (.word rightValue) finalStore)
    (leftTyping : HasType context left .word definitions)
    (rightTyping : HasType context right .word definitions)
    (environmentTyping :
      RuntimeEnvironmentHasTypes world environment context definitions)
    (storeTyping : StoreHasTypes world initialStore) :
    Evaluates environment initialStore (left.wordSgeFlag right)
      (.word (if !(decide (rightValue > leftValue)) then
        Word.ofNatModulo 1 else Word.zero)) finalStore :=
  (Evaluates.wordSge_both_negative leftNegative rightNegative
    leftEvaluation rightEvaluation leftTyping rightTyping
    environmentTyping storeTyping).boolToWord

theorem wordSgeFlag_nonnegative_negative
    {definitions : DataEnvironment} {environment : Environment} {context : Context}
    {initialStore intermediateStore finalStore : Store} {world : StoreTyping}
    {left right : Expr} {leftValue rightValue : Word}
    (leftNonnegative : leftValue.val < 2 ^ 255)
    (rightNegative : 2 ^ 255 ≤ rightValue.val)
    (leftEvaluation :
      Evaluates environment initialStore left (.word leftValue) intermediateStore)
    (rightEvaluation :
      Evaluates environment intermediateStore right (.word rightValue) finalStore)
    (leftTyping : HasType context left .word definitions)
    (rightTyping : HasType context right .word definitions)
    (environmentTyping :
      RuntimeEnvironmentHasTypes world environment context definitions)
    (storeTyping : StoreHasTypes world initialStore) :
    Evaluates environment initialStore (left.wordSgeFlag right)
      (.word (Word.ofNatModulo 1)) finalStore :=
  (Evaluates.wordSge_nonnegative_negative leftNonnegative rightNegative
    leftEvaluation rightEvaluation leftTyping rightTyping
    environmentTyping storeTyping).boolToWord_true

theorem wordSgeFlag_negative_nonnegative
    {definitions : DataEnvironment} {environment : Environment} {context : Context}
    {initialStore intermediateStore finalStore : Store} {world : StoreTyping}
    {left right : Expr} {leftValue rightValue : Word}
    (leftNegative : 2 ^ 255 ≤ leftValue.val)
    (rightNonnegative : rightValue.val < 2 ^ 255)
    (leftEvaluation :
      Evaluates environment initialStore left (.word leftValue) intermediateStore)
    (rightEvaluation :
      Evaluates environment intermediateStore right (.word rightValue) finalStore)
    (leftTyping : HasType context left .word definitions)
    (rightTyping : HasType context right .word definitions)
    (environmentTyping :
      RuntimeEnvironmentHasTypes world environment context definitions)
    (storeTyping : StoreHasTypes world initialStore) :
    Evaluates environment initialStore (left.wordSgeFlag right)
      (.word Word.zero) finalStore :=
  (Evaluates.wordSge_negative_nonnegative leftNegative rightNonnegative
    leftEvaluation rightEvaluation leftTyping rightTyping
    environmentTyping storeTyping).boolToWord_false

end Evaluates
end Solcore.Core
