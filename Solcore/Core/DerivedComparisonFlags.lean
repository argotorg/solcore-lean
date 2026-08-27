import Solcore.Core.Conversions
import Solcore.Core.DerivedComparisons

set_option autoImplicit false

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
