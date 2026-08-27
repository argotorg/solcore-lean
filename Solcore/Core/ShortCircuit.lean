import Solcore.Core.Eval

set_option autoImplicit false

namespace Solcore.Core

/-! Derived short-circuit boolean expressions and their proof interface. -/

namespace Expr

def boolAnd (left right : Expr) : Expr :=
  .ifE left right (.bool false)

def boolOr (left right : Expr) : Expr :=
  .ifE left (.bool true) right

end Expr

@[simp] theorem Expr.boolAnd_expansion (left right : Expr) :
    left.boolAnd right = .ifE left right (.bool false) :=
  rfl

@[simp] theorem Expr.boolOr_expansion (left right : Expr) :
    left.boolOr right = .ifE left (.bool true) right :=
  rfl

namespace HasType

theorem boolAnd
    {context : Context} {definitions : DataEnvironment} {left right : Expr}
    (leftTyping : HasType context left .bool definitions)
    (rightTyping : HasType context right .bool definitions) :
    HasType context (left.boolAnd right) .bool definitions :=
  .ifE leftTyping rightTyping .bool

theorem boolOr
    {context : Context} {definitions : DataEnvironment} {left right : Expr}
    (leftTyping : HasType context left .bool definitions)
    (rightTyping : HasType context right .bool definitions) :
    HasType context (left.boolOr right) .bool definitions :=
  .ifE leftTyping .bool rightTyping

end HasType

theorem infer_boolAnd
    {context : Context} {definitions : DataEnvironment} {left right : Expr}
    (leftInferred : infer? context left definitions = some .bool)
    (rightInferred : infer? context right definitions = some .bool) :
    infer? context (left.boolAnd right) definitions = some .bool :=
  infer_complete ((infer_sound leftInferred).boolAnd (infer_sound rightInferred))

theorem infer_boolOr
    {context : Context} {definitions : DataEnvironment} {left right : Expr}
    (leftInferred : infer? context left definitions = some .bool)
    (rightInferred : infer? context right definitions = some .bool) :
    infer? context (left.boolOr right) definitions = some .bool :=
  infer_complete ((infer_sound leftInferred).boolOr (infer_sound rightInferred))

namespace Evaluates

theorem boolAnd_false
    {environment : Environment} {initialStore finalStore : Store}
    {left right : Expr}
    (leftEvaluation :
      Evaluates environment initialStore left (.bool false) finalStore) :
    Evaluates environment initialStore (left.boolAnd right)
      (.bool false) finalStore :=
  .ifFalse leftEvaluation .bool

theorem boolAnd_true
    {environment : Environment} {initialStore branchStore finalStore : Store}
    {left right : Expr} {result : Bool}
    (leftEvaluation :
      Evaluates environment initialStore left (.bool true) branchStore)
    (rightEvaluation :
      Evaluates environment branchStore right (.bool result) finalStore) :
    Evaluates environment initialStore (left.boolAnd right)
      (.bool result) finalStore :=
  .ifTrue leftEvaluation rightEvaluation

theorem boolOr_true
    {environment : Environment} {initialStore finalStore : Store}
    {left right : Expr}
    (leftEvaluation :
      Evaluates environment initialStore left (.bool true) finalStore) :
    Evaluates environment initialStore (left.boolOr right)
      (.bool true) finalStore :=
  .ifTrue leftEvaluation .bool

theorem boolOr_false
    {environment : Environment} {initialStore branchStore finalStore : Store}
    {left right : Expr} {result : Bool}
    (leftEvaluation :
      Evaluates environment initialStore left (.bool false) branchStore)
    (rightEvaluation :
      Evaluates environment branchStore right (.bool result) finalStore) :
    Evaluates environment initialStore (left.boolOr right)
      (.bool result) finalStore :=
  .ifFalse leftEvaluation rightEvaluation

end Evaluates

@[simp] theorem Expr.weakenAt_boolAnd
    (left right : Expr) (cutoff : Nat) :
    (left.boolAnd right).weakenAt cutoff =
      (left.weakenAt cutoff).boolAnd (right.weakenAt cutoff) := by
  simp [Expr.boolAnd, Expr.weakenAt]

@[simp] theorem Expr.weakenAt_boolOr
    (left right : Expr) (cutoff : Nat) :
    (left.boolOr right).weakenAt cutoff =
      (left.weakenAt cutoff).boolOr (right.weakenAt cutoff) := by
  simp [Expr.boolOr, Expr.weakenAt]

end Solcore.Core
