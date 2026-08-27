import Solcore.Core.Eval
import Solcore.Core.RenamingSyntax

set_option autoImplicit false

namespace Solcore.Core

/-! Focused proof interface for the two direct unary primitives. -/

namespace Word

@[simp] theorem bitNot_zero : Word.zero.bitNot = Word.maximum := by
  rfl

@[simp] theorem bitNot_maximum : Word.maximum.bitNot = Word.zero := by
  rfl

@[simp] theorem bitNot_involutive (value : Word) :
    value.bitNot.bitNot = value := by
  apply Fin.ext
  unfold bitNot
  have valueLe : value ≤ maximum := Fin.le_last value
  have innerLe : maximum - value ≤ maximum := Fin.le_last (maximum - value)
  rw [Fin.sub_val_of_le innerLe]
  rw [Fin.sub_val_of_le valueLe]
  simp only [maximum]
  omega

end Word

namespace HasType

theorem boolNot
    {context : Context} {definitions : DataEnvironment} {operand : Expr}
    (typing : HasType context operand .bool definitions) :
    HasType context (.unary .boolNot operand) .bool definitions :=
  .unary typing

theorem wordNot
    {context : Context} {definitions : DataEnvironment} {operand : Expr}
    (typing : HasType context operand .word definitions) :
    HasType context (.unary .wordNot operand) .word definitions :=
  .unary typing

end HasType

theorem infer_boolNot
    {context : Context} {definitions : DataEnvironment} {operand : Expr}
    (inferred : infer? context operand definitions = some .bool) :
    infer? context (.unary .boolNot operand) definitions = some .bool :=
  infer_complete ((infer_sound inferred).boolNot)

theorem infer_wordNot
    {context : Context} {definitions : DataEnvironment} {operand : Expr}
    (inferred : infer? context operand definitions = some .word) :
    infer? context (.unary .wordNot operand) definitions = some .word :=
  infer_complete ((infer_sound inferred).wordNot)

namespace Evaluates

theorem boolNot
    {environment : Environment} {initialStore finalStore : Store}
    {operand : Expr} {value : Bool}
    (evaluation :
      Evaluates environment initialStore operand (.bool value) finalStore) :
    Evaluates environment initialStore (.unary .boolNot operand)
      (.bool (!value)) finalStore :=
  .unary evaluation rfl

theorem boolNot_true
    {environment : Environment} {initialStore finalStore : Store}
    {operand : Expr}
    (evaluation :
      Evaluates environment initialStore operand (.bool true) finalStore) :
    Evaluates environment initialStore (.unary .boolNot operand)
      (.bool false) finalStore := by
  simpa using evaluation.boolNot

theorem boolNot_false
    {environment : Environment} {initialStore finalStore : Store}
    {operand : Expr}
    (evaluation :
      Evaluates environment initialStore operand (.bool false) finalStore) :
    Evaluates environment initialStore (.unary .boolNot operand)
      (.bool true) finalStore := by
  simpa using evaluation.boolNot

theorem wordNot
    {environment : Environment} {initialStore finalStore : Store}
    {operand : Expr} {value : Word}
    (evaluation :
      Evaluates environment initialStore operand (.word value) finalStore) :
    Evaluates environment initialStore (.unary .wordNot operand)
      (.word value.bitNot) finalStore :=
  .unary evaluation rfl

theorem wordNot_zero
    {environment : Environment} {initialStore finalStore : Store}
    {operand : Expr}
    (evaluation :
      Evaluates environment initialStore operand (.word Word.zero) finalStore) :
    Evaluates environment initialStore (.unary .wordNot operand)
      (.word Word.maximum) finalStore := by
  simpa using evaluation.wordNot

theorem wordNot_maximum
    {environment : Environment} {initialStore finalStore : Store}
    {operand : Expr}
    (evaluation :
      Evaluates environment initialStore operand (.word Word.maximum) finalStore) :
    Evaluates environment initialStore (.unary .wordNot operand)
      (.word Word.zero) finalStore := by
  simpa using evaluation.wordNot

end Evaluates

@[simp] theorem Expr.rename_boolNot
    (operand : Expr) (mapping : Renaming) :
    (Expr.unary .boolNot operand).rename mapping =
      .unary .boolNot (operand.rename mapping) := by
  rfl

@[simp] theorem Expr.rename_wordNot
    (operand : Expr) (mapping : Renaming) :
    (Expr.unary .wordNot operand).rename mapping =
      .unary .wordNot (operand.rename mapping) := by
  rfl

@[simp] theorem Expr.weakenAt_boolNot
    (operand : Expr) (cutoff : Nat) :
    (Expr.unary .boolNot operand).weakenAt cutoff =
      .unary .boolNot (operand.weakenAt cutoff) := by
  simp [Expr.weakenAt]

@[simp] theorem Expr.weakenAt_wordNot
    (operand : Expr) (cutoff : Nat) :
    (Expr.unary .wordNot operand).weakenAt cutoff =
      .unary .wordNot (operand.weakenAt cutoff) := by
  simp [Expr.weakenAt]

end Solcore.Core
