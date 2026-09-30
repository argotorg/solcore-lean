import Solcore.Core.LocalControl

/-! Primitive computations over ordinary language-result sums. Strict operands
run from left to right; a failure skips subsequent work. The Boolean helpers
evaluate their right operand only when the left value requires it. -/

set_option autoImplicit false

namespace Solcore.Core.LocalPrimitiveResults

def unary (operator : UnaryOp) (operand : Expr) : Expr :=
  LanguageResult.bind operator.resultType operand
    (LanguageResult.success (.unary operator (.var 0)))

/-- `body` returns a raw value under right payload, left payload, outer scope.
This also supports comparisons built from existing Core primitives. -/
def binaryWith (resultType : Ty) (left right body : Expr) : Expr :=
  LanguageResult.bind resultType left
    (LanguageResult.bind resultType (right.weakenAt 0) (LanguageResult.success body))

def binary (operator : BinaryOp) (left right : Expr) : Expr :=
  binaryWith operator.resultType left right (.binary operator (.var 1) (.var 0))

def logicalAnd (left right : Expr) : Expr :=
  LocalControl.choose .bool left right (LanguageResult.success (.bool false))

def logicalOr (left right : Expr) : Expr :=
  LocalControl.choose .bool left (LanguageResult.success (.bool true)) right

theorem unary_hasType
    {definitions : DataEnvironment} {context : Context} {operator : UnaryOp} {operand : Expr}
    (typed : HasType context operand (LanguageResult.resultType operator.operandType) definitions) :
    HasType context (unary operator operand) (LanguageResult.resultType operator.resultType) definitions := by
  apply LanguageResult.bind_hasType (by cases operator <;> constructor) typed
  exact LanguageResult.success_hasType (.unary (.var rfl))

theorem binaryWith_hasType
    {definitions : DataEnvironment} {context : Context} {leftType rightType resultType : Ty}
    {left right body : Expr}
    (wellFormed : Ty.WellFormed definitions resultType)
    (leftTyped : HasType context left (LanguageResult.resultType leftType) definitions)
    (rightTyped : HasType context right (LanguageResult.resultType rightType) definitions)
    (bodyTyped : HasType (rightType :: leftType :: context) body resultType definitions) :
    HasType context (binaryWith resultType left right body) (LanguageResult.resultType resultType) definitions := by
  apply LanguageResult.bind_hasType wellFormed leftTyped
  apply LanguageResult.bind_hasType wellFormed
  · simpa [Context.insertAt] using rightTyped.weakenAt (inserted := leftType) 0
  · exact LanguageResult.success_hasType bodyTyped

theorem binary_hasType
    {definitions : DataEnvironment} {context : Context} {operator : BinaryOp} {left right : Expr}
    (leftTyped : HasType context left (LanguageResult.resultType operator.leftType) definitions)
    (rightTyped : HasType context right (LanguageResult.resultType operator.rightType) definitions) :
    HasType context (binary operator left right) (LanguageResult.resultType operator.resultType) definitions :=
  binaryWith_hasType (by cases operator <;> constructor) leftTyped rightTyped (.binary (.var rfl) (.var rfl))

theorem logicalAnd_hasType
    {definitions : DataEnvironment} {context : Context} {left right : Expr}
    (leftTyped : HasType context left (LanguageResult.resultType .bool) definitions)
    (rightTyped : HasType context right (LanguageResult.resultType .bool) definitions) :
    HasType context (logicalAnd left right) (LanguageResult.resultType .bool) definitions :=
  LocalControl.choose_hasType .bool leftTyped rightTyped (LanguageResult.success_hasType .bool)

theorem logicalOr_hasType
    {definitions : DataEnvironment} {context : Context} {left right : Expr}
    (leftTyped : HasType context left (LanguageResult.resultType .bool) definitions)
    (rightTyped : HasType context right (LanguageResult.resultType .bool) definitions) :
    HasType context (logicalOr left right) (LanguageResult.resultType .bool) definitions :=
  LocalControl.choose_hasType .bool leftTyped (LanguageResult.success_hasType .bool) rightTyped

theorem unary_failure
    {environment : Environment} {before after : Store} {operator : UnaryOp} {operand : Expr} {reason : Word}
    (evaluation : Evaluates environment before operand (.inLeft operator.operandType (.word reason)) after) :
    Evaluates environment before (unary operator operand) (.inLeft operator.resultType (.word reason)) after :=
  LanguageResult.bind_failure _ evaluation

theorem unary_success
    {environment : Environment} {before after : Store} {operator : UnaryOp} {operand : Expr}
    {value result : Value}
    (evaluation : Evaluates environment before operand (.inRight .word value) after)
    (applied : operator.apply value = some result) :
    Evaluates environment before (unary operator operand) (.inRight .word result) after :=
  LanguageResult.bind_success _ evaluation (.inRight (.unary (.var rfl) applied))

theorem binaryWith_left_failure
    {environment : Environment} {before after : Store} {leftType resultType : Ty}
    {left right body : Expr} {reason : Word}
    (evaluation : Evaluates environment before left (.inLeft leftType (.word reason)) after) :
    Evaluates environment before (binaryWith resultType left right body)
      (.inLeft resultType (.word reason)) after :=
  LanguageResult.bind_failure _ evaluation

theorem binaryWith_right_failure
    {environment : Environment} {before middle after : Store} {rightType resultType : Ty}
    {left right body : Expr} {leftValue : Value} {reason : Word}
    (leftEvaluation : Evaluates environment before left (.inRight .word leftValue) middle)
    (rightEvaluation : Evaluates (leftValue :: environment) middle (right.weakenAt 0)
      (.inLeft rightType (.word reason)) after) :
    Evaluates environment before (binaryWith resultType left right body)
      (.inLeft resultType (.word reason)) after :=
  LanguageResult.bind_success _ leftEvaluation (LanguageResult.bind_failure _ rightEvaluation)

theorem binaryWith_success
    {environment : Environment} {before middle operated after : Store} {resultType : Ty}
    {left right body : Expr} {leftValue rightValue result : Value}
    (leftEvaluation : Evaluates environment before left (.inRight .word leftValue) middle)
    (rightEvaluation : Evaluates (leftValue :: environment) middle (right.weakenAt 0)
      (.inRight .word rightValue) operated)
    (bodyEvaluation : Evaluates (rightValue :: leftValue :: environment) operated body result after) :
    Evaluates environment before (binaryWith resultType left right body) (.inRight .word result) after :=
  LanguageResult.bind_success _ leftEvaluation
    (LanguageResult.bind_success _ rightEvaluation (.inRight bodyEvaluation))

theorem binary_left_failure
    {environment : Environment} {before after : Store} {operator : BinaryOp}
    {left right : Expr} {reason : Word}
    (evaluation : Evaluates environment before left (.inLeft operator.leftType (.word reason)) after) :
    Evaluates environment before (binary operator left right) (.inLeft operator.resultType (.word reason)) after :=
  binaryWith_left_failure evaluation

theorem binary_right_failure
    {environment : Environment} {before middle after : Store} {operator : BinaryOp}
    {left right : Expr} {leftValue : Value} {reason : Word}
    (leftEvaluation : Evaluates environment before left (.inRight .word leftValue) middle)
    (rightEvaluation : Evaluates (leftValue :: environment) middle (right.weakenAt 0)
      (.inLeft operator.rightType (.word reason)) after) :
    Evaluates environment before (binary operator left right) (.inLeft operator.resultType (.word reason)) after :=
  binaryWith_right_failure leftEvaluation rightEvaluation

theorem binary_success
    {environment : Environment} {before middle after : Store} {operator : BinaryOp}
    {left right : Expr} {leftValue rightValue result : Value}
    (leftEvaluation : Evaluates environment before left (.inRight .word leftValue) middle)
    (rightEvaluation : Evaluates (leftValue :: environment) middle (right.weakenAt 0)
      (.inRight .word rightValue) after)
    (applied : operator.apply leftValue rightValue = some result) :
    Evaluates environment before (binary operator left right) (.inRight .word result) after :=
  binaryWith_success leftEvaluation rightEvaluation (.binary (.var rfl) (.var rfl) applied)

theorem logicalAnd_failure
    {environment : Environment} {before after : Store} {left right : Expr} {reason : Word}
    (evaluation : Evaluates environment before left (.inLeft .bool (.word reason)) after) :
    Evaluates environment before (logicalAnd left right) (.inLeft .bool (.word reason)) after :=
  LocalControl.choose_failure _ evaluation

theorem logicalOr_failure
    {environment : Environment} {before after : Store} {left right : Expr} {reason : Word}
    (evaluation : Evaluates environment before left (.inLeft .bool (.word reason)) after) :
    Evaluates environment before (logicalOr left right) (.inLeft .bool (.word reason)) after :=
  LocalControl.choose_failure _ evaluation

theorem logicalAnd_shortCircuit
    {environment : Environment} {before after : Store} {left right : Expr}
    (evaluation : Evaluates environment before left (.inRight .word (.bool false)) after) :
    Evaluates environment before (logicalAnd left right) (.inRight .word (.bool false)) after :=
  LocalControl.choose_false _ evaluation (by
    simp only [LanguageResult.success, Expr.weakenAt]
    exact .inRight .bool)

theorem logicalOr_shortCircuit
    {environment : Environment} {before after : Store} {left right : Expr}
    (evaluation : Evaluates environment before left (.inRight .word (.bool true)) after) :
    Evaluates environment before (logicalOr left right) (.inRight .word (.bool true)) after :=
  LocalControl.choose_true _ evaluation (by
    simp only [LanguageResult.success, Expr.weakenAt]
    exact .inRight .bool)

theorem logicalAnd_right
    {environment : Environment} {before middle after : Store} {left right : Expr} {result : Value}
    (leftEvaluation : Evaluates environment before left (.inRight .word (.bool true)) middle)
    (rightEvaluation : Evaluates (.bool true :: environment) middle (right.weakenAt 0) result after) :
    Evaluates environment before (logicalAnd left right) result after :=
  LocalControl.choose_true _ leftEvaluation rightEvaluation

theorem logicalOr_right
    {environment : Environment} {before middle after : Store} {left right : Expr} {result : Value}
    (leftEvaluation : Evaluates environment before left (.inRight .word (.bool false)) middle)
    (rightEvaluation : Evaluates (.bool false :: environment) middle (right.weakenAt 0) result after) :
    Evaluates environment before (logicalOr left right) result after :=
  LocalControl.choose_false _ leftEvaluation rightEvaluation

end Solcore.Core.LocalPrimitiveResults
