import Solcore.Core.DerivedComparisons

set_option autoImplicit false

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
