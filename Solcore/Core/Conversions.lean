import Solcore.Core.Eval

set_option autoImplicit false

namespace Solcore.Core

/-! Proof interface for the derived boolean/word conversion expressions. -/

@[simp] theorem Expr.boolToWord_expansion (value : Expr) :
    value.boolToWord =
      .ifE value (.word (Word.ofNatModulo 1)) (.word Word.zero) :=
  rfl

@[simp] theorem Expr.wordToBool_expansion (value : Expr) :
    value.wordToBool =
      .unary .boolNot (.binary .wordEq value (.word Word.zero)) :=
  rfl

namespace HasType

theorem boolToWord
    {context : Context} {definitions : DataEnvironment} {value : Expr}
    (typing : HasType context value .bool definitions) :
    HasType context value.boolToWord .word definitions :=
  .ifE typing .word .word

theorem wordToBool
    {context : Context} {definitions : DataEnvironment} {value : Expr}
    (typing : HasType context value .word definitions) :
    HasType context value.wordToBool .bool definitions :=
  .unary (.binary typing .word)

theorem wordIsZero
    {context : Context} {definitions : DataEnvironment} {value : Expr}
    (typing : HasType context value .word definitions) :
    HasType context value.wordIsZero .word definitions :=
  HasType.boolToWord (HasType.binary typing .word)

end HasType

theorem infer_boolToWord
    {context : Context} {definitions : DataEnvironment} {value : Expr}
    (inferred : infer? context value definitions = some .bool) :
    infer? context value.boolToWord definitions = some .word :=
  infer_complete ((infer_sound inferred).boolToWord)

theorem infer_wordToBool
    {context : Context} {definitions : DataEnvironment} {value : Expr}
    (inferred : infer? context value definitions = some .word) :
    infer? context value.wordToBool definitions = some .bool :=
  infer_complete ((infer_sound inferred).wordToBool)

theorem infer_wordIsZero
    {context : Context} {definitions : DataEnvironment} {value : Expr}
    (inferred : infer? context value definitions = some .word) :
    infer? context value.wordIsZero definitions = some .word :=
  infer_complete ((infer_sound inferred).wordIsZero)

namespace Evaluates

theorem boolToWord_false
    {environment : Environment} {initialStore finalStore : Store}
    {operand : Expr}
    (evaluation :
      Evaluates environment initialStore operand (.bool false) finalStore) :
    Evaluates environment initialStore operand.boolToWord
      (.word Word.zero) finalStore :=
  .ifFalse evaluation .word

theorem boolToWord_true
    {environment : Environment} {initialStore finalStore : Store}
    {operand : Expr}
    (evaluation :
      Evaluates environment initialStore operand (.bool true) finalStore) :
    Evaluates environment initialStore operand.boolToWord
      (.word (Word.ofNatModulo 1)) finalStore :=
  .ifTrue evaluation .word

theorem boolToWord
    {environment : Environment} {initialStore finalStore : Store}
    {operand : Expr} {value : Bool}
    (evaluation :
      Evaluates environment initialStore operand (.bool value) finalStore) :
    Evaluates environment initialStore operand.boolToWord
      (.word (if value then Word.ofNatModulo 1 else Word.zero)) finalStore := by
  cases value with
  | false => exact evaluation.boolToWord_false
  | true => exact evaluation.boolToWord_true

theorem wordToBool
    {environment : Environment} {initialStore finalStore : Store}
    {operand : Expr} {value : Word}
    (evaluation :
      Evaluates environment initialStore operand (.word value) finalStore) :
    Evaluates environment initialStore operand.wordToBool
      (.bool (!(value == Word.zero))) finalStore :=
  .unary (.binary evaluation .word rfl) rfl

theorem wordToBool_zero
    {environment : Environment} {initialStore finalStore : Store}
    {operand : Expr}
    (evaluation :
      Evaluates environment initialStore operand (.word Word.zero) finalStore) :
    Evaluates environment initialStore operand.wordToBool
      (.bool false) finalStore := by
  simpa using evaluation.wordToBool

theorem wordToBool_nonzero
    {environment : Environment} {initialStore finalStore : Store}
    {operand : Expr} {value : Word}
    (valueNotZero : value ≠ Word.zero)
    (evaluation :
      Evaluates environment initialStore operand (.word value) finalStore) :
    Evaluates environment initialStore operand.wordToBool
      (.bool true) finalStore := by
  have valueBeqZero : (value == Word.zero) = false :=
    beq_eq_false_iff_ne.mpr valueNotZero
  simpa [valueBeqZero] using evaluation.wordToBool

theorem wordIsZero
    {environment : Environment} {initialStore finalStore : Store}
    {operand : Expr} {value : Word}
    (evaluation :
      Evaluates environment initialStore operand (.word value) finalStore) :
    Evaluates environment initialStore operand.wordIsZero
      (.word (if value == Word.zero then Word.ofNatModulo 1 else Word.zero))
      finalStore :=
  (Evaluates.binary evaluation .word rfl).boolToWord

theorem wordIsZero_zero
    {environment : Environment} {initialStore finalStore : Store}
    {operand : Expr}
    (evaluation :
      Evaluates environment initialStore operand (.word Word.zero) finalStore) :
    Evaluates environment initialStore operand.wordIsZero
      (.word (Word.ofNatModulo 1)) finalStore := by
  simpa using evaluation.wordIsZero

theorem wordIsZero_nonzero
    {environment : Environment} {initialStore finalStore : Store}
    {operand : Expr} {value : Word}
    (valueNotZero : value ≠ Word.zero)
    (evaluation :
      Evaluates environment initialStore operand (.word value) finalStore) :
    Evaluates environment initialStore operand.wordIsZero
      (.word Word.zero) finalStore := by
  have valueBeqZero : (value == Word.zero) = false :=
    beq_eq_false_iff_ne.mpr valueNotZero
  simpa [valueBeqZero] using evaluation.wordIsZero

end Evaluates

@[simp] theorem Expr.wordIsZero_expansion (value : Expr) :
    value.wordIsZero =
      (Expr.binary .wordEq value (.word Word.zero)).boolToWord :=
  rfl

@[simp] theorem Expr.weakenAt_boolToWord
    (value : Expr) (cutoff : Nat) :
    value.boolToWord.weakenAt cutoff = (value.weakenAt cutoff).boolToWord :=
  by simp [Expr.boolToWord, Expr.weakenAt]

@[simp] theorem Expr.weakenAt_wordToBool
    (value : Expr) (cutoff : Nat) :
    value.wordToBool.weakenAt cutoff = (value.weakenAt cutoff).wordToBool :=
  by simp [Expr.wordToBool, Expr.wordNe, Expr.weakenAt]

@[simp] theorem Expr.weakenAt_wordIsZero
    (value : Expr) (cutoff : Nat) :
    value.wordIsZero.weakenAt cutoff = (value.weakenAt cutoff).wordIsZero :=
  by simp [Expr.wordIsZero, Expr.boolToWord, Expr.weakenAt]

end Solcore.Core
