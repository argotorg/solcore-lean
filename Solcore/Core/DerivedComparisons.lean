import Solcore.Core.Renaming

set_option autoImplicit false

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
