import Solcore.Frontend.LocalExpressionEvaluation

/-! Exact canonical-to-resolved evaluation correspondence. Whole structural
resolution is explicit: a skipped branch can otherwise prevent elaboration. -/

set_option autoImplicit false

namespace Solcore.Frontend

theorem ResolvesLocalExpression.preserves_evaluation {table : LocalNameTable}
    {source : Syntax.Expr} {resolved : Resolved.Expr}
    (resolution : ResolvesLocalExpression table source resolved)
    {environment : Resolved.Environment} {initialStore finalStore : Core.Store}
    {value : Core.Value}
    (evaluation : LocalExpressionEvaluates table environment initialStore source value finalStore) :
    Resolved.Evaluates environment initialStore resolved value finalStore := by
  induction resolution generalizing initialStore finalStore value with
  | identifier named =>
      cases evaluation with
      | identifier otherNamed found =>
          cases named.id_unique otherNamed
          exact .var found
  | wordLiteral meaning =>
      cases evaluation with
      | wordLiteral otherMeaning =>
          cases meaning.value_unique otherMeaning
          exact .word
  | group _ ih =>
      cases evaluation with
      | group child => exact ih child
  | logicalNot _ ih =>
      cases evaluation with
      | logicalNot child => exact .unary (ih child) rfl
  | bitNot _ ih =>
      cases evaluation with
      | bitNot child => exact .unary (ih child) rfl
  | logicalAnd _ _ leftIH rightIH =>
      cases evaluation with
      | andTrue leftChild rightChild => exact .ifTrue (leftIH leftChild) (rightIH rightChild)
      | andFalse leftChild => exact .ifFalse (leftIH leftChild) .bool
  | logicalOr _ _ leftIH rightIH =>
      cases evaluation with
      | orTrue leftChild => exact .ifTrue (leftIH leftChild) .bool
      | orFalse leftChild rightChild => exact .ifFalse (leftIH leftChild) (rightIH rightChild)
  | conditional _ _ _ conditionIH thenIH elseIH =>
      cases evaluation with
      | ifTrue condition branch => exact .ifTrue (conditionIH condition) (thenIH branch)
      | ifFalse condition branch => exact .ifFalse (conditionIH condition) (elseIH branch)

theorem ResolvesLocalExpression.reflects_evaluation {table : LocalNameTable}
    {source : Syntax.Expr} {resolved : Resolved.Expr}
    (resolution : ResolvesLocalExpression table source resolved)
    {environment : Resolved.Environment} {initialStore finalStore : Core.Store}
    {value : Core.Value}
    (evaluation : Resolved.Evaluates environment initialStore resolved value finalStore) :
    LocalExpressionEvaluates table environment initialStore source value finalStore := by
  induction resolution generalizing initialStore finalStore value with
  | identifier named =>
      cases evaluation with
      | var found => exact .identifier named found
  | wordLiteral meaning =>
      cases evaluation with
      | word => exact .wordLiteral meaning
  | group _ ih => exact .group (ih evaluation)
  | logicalNot _ ih =>
      cases evaluation with
      | @unary _ _ _ _ _ operandValue _ child applied =>
          cases operandValue <;> simp only [Core.UnaryOp.apply, reduceCtorEq] at applied
          case bool decision =>
            cases applied
            exact .logicalNot (ih child)
  | bitNot _ ih =>
      cases evaluation with
      | @unary _ _ _ _ _ operandValue _ child applied =>
          cases operandValue <;> simp only [Core.UnaryOp.apply, reduceCtorEq] at applied
          case word value =>
            cases applied
            exact .bitNot (ih child)
  | logicalAnd _ _ leftIH rightIH =>
      cases evaluation with
      | ifTrue leftChild rightChild => exact .andTrue (leftIH leftChild) (rightIH rightChild)
      | ifFalse leftChild constant =>
          cases constant
          exact .andFalse (leftIH leftChild)
  | logicalOr _ _ leftIH rightIH =>
      cases evaluation with
      | ifTrue leftChild constant =>
          cases constant
          exact .orTrue (leftIH leftChild)
      | ifFalse leftChild rightChild => exact .orFalse (leftIH leftChild) (rightIH rightChild)
  | conditional _ _ _ conditionIH thenIH elseIH =>
      cases evaluation with
      | ifTrue condition branch => exact .ifTrue (conditionIH condition) (thenIH branch)
      | ifFalse condition branch => exact .ifFalse (conditionIH condition) (elseIH branch)

theorem ResolvesLocalExpression.evaluates_iff {table : LocalNameTable}
    {source : Syntax.Expr} {resolved : Resolved.Expr}
    (resolution : ResolvesLocalExpression table source resolved)
    {environment : Resolved.Environment} {initialStore finalStore : Core.Store} {value : Core.Value} :
    LocalExpressionEvaluates table environment initialStore source value finalStore ↔
      Resolved.Evaluates environment initialStore resolved value finalStore :=
  ⟨resolution.preserves_evaluation, resolution.reflects_evaluation⟩

/-- Exact Core correspondence for an explicitly resolved and lowered expression.
The lowering scope is the runtime identity order, not merely its length. -/
theorem ResolvesLocalExpression.core_evaluates_iff {table : LocalNameTable}
    {source : Syntax.Expr} {resolved : Resolved.Expr}
    (resolution : ResolvesLocalExpression table source resolved)
    {environment : Resolved.Environment} {core : Core.Expr}
    (lowered : Resolved.Lowers (Resolved.LocalScope.ids environment) resolved core)
    {initialStore finalStore : Core.Store} {value : Core.Value} :
    LocalExpressionEvaluates table environment initialStore source value finalStore ↔
      Core.Evaluates (Resolved.LocalScope.values environment) initialStore core value finalStore :=
  resolution.evaluates_iff.trans lowered.evaluates_iff

end Solcore.Frontend
