import Solcore.Core.Conversions
import Solcore.Core.DerivedSignedNonStrictComparisons

set_option autoImplicit false

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
