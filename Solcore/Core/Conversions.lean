import Solcore.Core.DirectWordComparisons
import Solcore.Core.RenamingSyntax

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

@[simp] theorem Expr.wordIsNonzero_expansion (value : Expr) :
    value.wordIsNonzero = value.wordToBool.boolToWord :=
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

theorem wordIsNonzero
    {context : Context} {definitions : DataEnvironment} {value : Expr}
    (typing : HasType context value .word definitions) :
    HasType context value.wordIsNonzero .word definitions :=
  HasType.boolToWord (HasType.wordToBool typing)

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

theorem infer_wordIsNonzero
    {context : Context} {definitions : DataEnvironment} {value : Expr}
    (inferred : infer? context value definitions = some .word) :
    infer? context value.wordIsNonzero definitions = some .word :=
  infer_complete ((infer_sound inferred).wordIsNonzero)

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
  .unary (evaluation.wordEq .word) rfl

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
  (evaluation.wordEq .word).boolToWord

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

theorem wordIsNonzero
    {environment : Environment} {initialStore finalStore : Store}
    {operand : Expr} {value : Word}
    (evaluation :
      Evaluates environment initialStore operand (.word value) finalStore) :
    Evaluates environment initialStore operand.wordIsNonzero
      (.word (if value == Word.zero then Word.zero else Word.ofNatModulo 1))
      finalStore := by
  have converted := evaluation.wordToBool.boolToWord
  by_cases valueZero : value == Word.zero
  · simpa [valueZero] using converted
  · simpa [valueZero] using converted

theorem wordIsNonzero_zero
    {environment : Environment} {initialStore finalStore : Store}
    {operand : Expr}
    (evaluation :
      Evaluates environment initialStore operand (.word Word.zero) finalStore) :
    Evaluates environment initialStore operand.wordIsNonzero
      (.word Word.zero) finalStore := by
  simpa using evaluation.wordIsNonzero

theorem wordIsNonzero_nonzero
    {environment : Environment} {initialStore finalStore : Store}
    {operand : Expr} {value : Word}
    (valueNotZero : value ≠ Word.zero)
    (evaluation :
      Evaluates environment initialStore operand (.word value) finalStore) :
    Evaluates environment initialStore operand.wordIsNonzero
      (.word (Word.ofNatModulo 1)) finalStore := by
  have valueBeqZero : (value == Word.zero) = false :=
    beq_eq_false_iff_ne.mpr valueNotZero
  simpa [valueBeqZero] using evaluation.wordIsNonzero

end Evaluates

@[simp] theorem Expr.wordIsZero_expansion (value : Expr) :
    value.wordIsZero =
      (Expr.binary .wordEq value (.word Word.zero)).boolToWord :=
  rfl

@[simp] theorem Expr.rename_boolToWord
    (value : Expr) (mapping : Renaming) :
    value.boolToWord.rename mapping = (value.rename mapping).boolToWord := by
  simp [Expr.boolToWord, Expr.rename]

@[simp] theorem Expr.rename_wordToBool
    (value : Expr) (mapping : Renaming) :
    value.wordToBool.rename mapping = (value.rename mapping).wordToBool := by
  simp [Expr.wordToBool, Expr.wordNe, Expr.rename]

@[simp] theorem Expr.rename_wordIsZero
    (value : Expr) (mapping : Renaming) :
    value.wordIsZero.rename mapping = (value.rename mapping).wordIsZero := by
  rw [Expr.wordIsZero_expansion, Expr.rename_boolToWord]
  simp [Expr.rename, Expr.wordIsZero_expansion]

@[simp] theorem Expr.rename_wordIsNonzero
    (value : Expr) (mapping : Renaming) :
    value.wordIsNonzero.rename mapping =
      (value.rename mapping).wordIsNonzero := by
  rw [Expr.wordIsNonzero_expansion, Expr.rename_boolToWord,
    Expr.rename_wordToBool, Expr.wordIsNonzero_expansion]

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

@[simp] theorem Expr.weakenAt_wordIsNonzero
    (value : Expr) (cutoff : Nat) :
    value.wordIsNonzero.weakenAt cutoff =
      (value.weakenAt cutoff).wordIsNonzero :=
  by
    simp [Expr.wordIsNonzero, Expr.boolToWord, Expr.wordToBool, Expr.wordNe,
      Expr.weakenAt]

end Solcore.Core
