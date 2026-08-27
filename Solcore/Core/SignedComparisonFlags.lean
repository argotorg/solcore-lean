import Solcore.Core.Conversions
import Solcore.Core.DerivedSignedComparisons

set_option autoImplicit false

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
