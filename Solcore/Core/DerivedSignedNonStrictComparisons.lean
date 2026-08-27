import Solcore.Core.DerivedSignedComparisons

set_option autoImplicit false

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
