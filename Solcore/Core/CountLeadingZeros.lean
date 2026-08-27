import Solcore.Core.Eval

set_option autoImplicit false

namespace Solcore.Core

/-! Focused value and evaluation interface for word count-leading-zeros. -/

namespace Word

@[simp] theorem clz_zero :
    Word.zero.clz = Word.ofNatModulo 256 := by
  rfl

theorem clz_nonzero (value : Word) (nonzero : value.val ≠ 0) :
    value.clz = Word.ofNatModulo (255 - Nat.log2 value.val) := by
  simp [clz, nonzero]

@[simp] theorem clz_one :
    (Word.ofNatModulo 1).clz = Word.ofNatModulo 255 := by
  rfl

@[simp] theorem clz_highBit :
    (Word.ofNatModulo (2 ^ 255)).clz = Word.zero := by
  rfl

@[simp] theorem clz_maximum :
    Word.maximum.clz = Word.zero := by
  rfl

end Word

namespace UnaryOp

@[simp] theorem apply_wordClz (value : Word) :
    UnaryOp.wordClz.apply (.word value) = some (.word value.clz) := by
  rfl

end UnaryOp

namespace Evaluates

theorem wordClz
    {environment : Environment} {initialStore finalStore : Store}
    {operand : Expr} {value : Word}
    (evaluation :
      Evaluates environment initialStore operand (.word value) finalStore) :
    Evaluates environment initialStore (.unary .wordClz operand)
      (.word value.clz) finalStore :=
  .unary evaluation rfl

theorem wordClz_zero
    {environment : Environment} {initialStore finalStore : Store}
    {operand : Expr}
    (evaluation :
      Evaluates environment initialStore operand (.word Word.zero) finalStore) :
    Evaluates environment initialStore (.unary .wordClz operand)
      (.word (Word.ofNatModulo 256)) finalStore := by
  simpa using evaluation.wordClz

theorem wordClz_one
    {environment : Environment} {initialStore finalStore : Store}
    {operand : Expr}
    (evaluation :
      Evaluates environment initialStore operand
        (.word (Word.ofNatModulo 1)) finalStore) :
    Evaluates environment initialStore (.unary .wordClz operand)
      (.word (Word.ofNatModulo 255)) finalStore := by
  simpa using evaluation.wordClz

theorem wordClz_highBit
    {environment : Environment} {initialStore finalStore : Store}
    {operand : Expr}
    (evaluation :
      Evaluates environment initialStore operand
        (.word (Word.ofNatModulo (2 ^ 255))) finalStore) :
    Evaluates environment initialStore (.unary .wordClz operand)
      (.word Word.zero) finalStore := by
  simpa only [Word.clz_highBit] using evaluation.wordClz

theorem wordClz_maximum
    {environment : Environment} {initialStore finalStore : Store}
    {operand : Expr}
    (evaluation :
      Evaluates environment initialStore operand (.word Word.maximum) finalStore) :
    Evaluates environment initialStore (.unary .wordClz operand)
      (.word Word.zero) finalStore := by
  simpa using evaluation.wordClz

end Evaluates

end Solcore.Core
