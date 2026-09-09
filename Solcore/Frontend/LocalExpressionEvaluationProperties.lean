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
  | unit => cases evaluation; exact .unit
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
  | pair _ _ leftIH rightIH =>
      cases evaluation with
      | pair leftChild rightChild => exact .pair (leftIH leftChild) (rightIH rightChild)
  | many _ _ headIH tailIH =>
      cases evaluation with
      | many headChild tailChild => exact .pair (headIH headChild) (tailIH tailChild)
  | logicalNot _ ih =>
      cases evaluation with
      | logicalNot child => exact .unary (ih child) rfl
  | bitNot _ ih =>
      cases evaluation with
      | bitNot child => exact .unary (ih child) rfl
  | add _ _ leftIH rightIH =>
      cases evaluation with
      | add leftChild rightChild => exact .binary (leftIH leftChild) (rightIH rightChild) rfl
  | subtract _ _ leftIH rightIH =>
      cases evaluation with
      | subtract leftChild rightChild => exact .binary (leftIH leftChild) (rightIH rightChild) rfl
  | multiply _ _ leftIH rightIH =>
      cases evaluation with
      | multiply leftChild rightChild => exact .binary (leftIH leftChild) (rightIH rightChild) rfl
  | divide _ _ leftIH rightIH =>
      cases evaluation with
      | divide leftChild rightChild => exact .binary (leftIH leftChild) (rightIH rightChild) rfl
  | modulo _ _ leftIH rightIH =>
      cases evaluation with
      | modulo leftChild rightChild => exact .binary (leftIH leftChild) (rightIH rightChild) rfl
  | bitAnd _ _ leftIH rightIH =>
      cases evaluation with
      | bitAnd leftChild rightChild => exact .binary (leftIH leftChild) (rightIH rightChild) rfl
  | bitOr _ _ leftIH rightIH =>
      cases evaluation with
      | bitOr leftChild rightChild => exact .binary (leftIH leftChild) (rightIH rightChild) rfl
  | bitXor _ _ leftIH rightIH =>
      cases evaluation with
      | bitXor leftChild rightChild => exact .binary (leftIH leftChild) (rightIH rightChild) rfl
  | greater _ _ leftIH rightIH =>
      cases evaluation with
      | greater leftChild rightChild => exact .binary (leftIH leftChild) (rightIH rightChild) rfl
  | less _ _ leftIH rightIH =>
      cases evaluation with
      | less leftChild rightChild => exact .wordLt (leftIH leftChild) (rightIH rightChild)
  | equal _ _ leftIH rightIH =>
      cases evaluation with
      | equal leftChild rightChild => exact .binary (leftIH leftChild) (rightIH rightChild) rfl
  | notEqual _ _ leftIH rightIH =>
      cases evaluation with
      | notEqual leftChild rightChild => exact .unary (.binary (leftIH leftChild) (rightIH rightChild) rfl) rfl
  | lessEqual _ _ leftIH rightIH =>
      cases evaluation with
      | lessEqual leftChild rightChild => exact .unary (.binary (leftIH leftChild) (rightIH rightChild) rfl) rfl
  | greaterEqual _ _ leftIH rightIH =>
      cases evaluation with
      | greaterEqual leftChild rightChild => exact .unary (.wordLt (leftIH leftChild) (rightIH rightChild)) rfl
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
  | unit => cases evaluation; exact .unit
  | identifier named =>
      cases evaluation with
      | var found => exact .identifier named found
  | wordLiteral meaning =>
      cases evaluation with
      | word => exact .wordLiteral meaning
  | group _ ih => exact .group (ih evaluation)
  | pair _ _ leftIH rightIH =>
      cases evaluation with
      | pair leftChild rightChild => exact .pair (leftIH leftChild) (rightIH rightChild)
  | many _ _ headIH tailIH =>
      cases evaluation with
      | pair headChild tailChild => exact .many (headIH headChild) (tailIH tailChild)
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
  | add _ _ leftIH rightIH =>
      cases evaluation with
      | @binary _ _ _ _ _ _ _ leftValue rightValue _ leftChild rightChild applied =>
          cases leftValue <;> cases rightValue <;>
            simp only [Core.BinaryOp.apply, reduceCtorEq] at applied
          case word.word leftWord rightWord =>
            cases applied
            exact .add (leftIH leftChild) (rightIH rightChild)
  | subtract _ _ leftIH rightIH =>
      cases evaluation with
      | @binary _ _ _ _ _ _ _ leftValue rightValue _ leftChild rightChild applied =>
          cases leftValue <;> cases rightValue <;>
            simp only [Core.BinaryOp.apply, reduceCtorEq] at applied
          case word.word leftWord rightWord =>
            cases applied
            exact .subtract (leftIH leftChild) (rightIH rightChild)
  | multiply _ _ leftIH rightIH =>
      cases evaluation with
      | @binary _ _ _ _ _ _ _ leftValue rightValue _ leftChild rightChild applied =>
          cases leftValue <;> cases rightValue <;>
            simp only [Core.BinaryOp.apply, reduceCtorEq] at applied
          case word.word leftWord rightWord =>
            cases applied
            exact .multiply (leftIH leftChild) (rightIH rightChild)
  | divide _ _ leftIH rightIH =>
      cases evaluation with
      | @binary _ _ _ _ _ _ _ leftValue rightValue _ leftChild rightChild applied =>
          cases leftValue <;> cases rightValue <;>
            simp only [Core.BinaryOp.apply, reduceCtorEq] at applied
          case word.word leftWord rightWord =>
            cases applied
            exact .divide (leftIH leftChild) (rightIH rightChild)
  | modulo _ _ leftIH rightIH =>
      cases evaluation with
      | @binary _ _ _ _ _ _ _ leftValue rightValue _ leftChild rightChild applied =>
          cases leftValue <;> cases rightValue <;>
            simp only [Core.BinaryOp.apply, reduceCtorEq] at applied
          case word.word leftWord rightWord =>
            cases applied
            exact .modulo (leftIH leftChild) (rightIH rightChild)
  | bitAnd _ _ leftIH rightIH =>
      cases evaluation with
      | @binary _ _ _ _ _ _ _ leftValue rightValue _ leftChild rightChild applied =>
          cases leftValue <;> cases rightValue <;>
            simp only [Core.BinaryOp.apply, reduceCtorEq] at applied
          case word.word leftWord rightWord =>
            cases applied
            exact .bitAnd (leftIH leftChild) (rightIH rightChild)
  | bitOr _ _ leftIH rightIH =>
      cases evaluation with
      | @binary _ _ _ _ _ _ _ leftValue rightValue _ leftChild rightChild applied =>
          cases leftValue <;> cases rightValue <;>
            simp only [Core.BinaryOp.apply, reduceCtorEq] at applied
          case word.word leftWord rightWord =>
            cases applied
            exact .bitOr (leftIH leftChild) (rightIH rightChild)
  | bitXor _ _ leftIH rightIH =>
      cases evaluation with
      | @binary _ _ _ _ _ _ _ leftValue rightValue _ leftChild rightChild applied =>
          cases leftValue <;> cases rightValue <;>
            simp only [Core.BinaryOp.apply, reduceCtorEq] at applied
          case word.word leftWord rightWord =>
            cases applied
            exact .bitXor (leftIH leftChild) (rightIH rightChild)
  | greater _ _ leftIH rightIH =>
      cases evaluation with
      | @binary _ _ _ _ _ _ _ leftValue rightValue _ leftChild rightChild applied =>
          cases leftValue <;> cases rightValue <;>
            simp only [Core.BinaryOp.apply, reduceCtorEq] at applied
          case word.word leftWord rightWord =>
            cases applied
            exact .greater (leftIH leftChild) (rightIH rightChild)
  | less _ _ leftIH rightIH =>
      cases evaluation with
      | wordLt leftChild rightChild => exact .less (leftIH leftChild) (rightIH rightChild)
  | equal _ _ leftIH rightIH =>
      cases evaluation with
      | @binary _ _ _ _ _ _ _ leftValue rightValue _ leftChild rightChild applied =>
          cases leftValue <;> cases rightValue <;>
            simp only [Core.BinaryOp.apply, reduceCtorEq] at applied
          case word.word leftWord rightWord =>
            cases applied
            exact .equal (leftIH leftChild) (rightIH rightChild)
  | notEqual _ _ leftIH rightIH =>
      cases evaluation with
      | unary equality negated =>
          cases equality with
          | @binary _ _ _ _ _ _ _ leftValue rightValue _ leftChild rightChild applied =>
              cases leftValue <;> cases rightValue <;>
                simp only [Core.BinaryOp.apply, reduceCtorEq] at applied
              case word.word leftWord rightWord =>
                cases applied
                cases negated
                exact .notEqual (leftIH leftChild) (rightIH rightChild)
  | lessEqual _ _ leftIH rightIH =>
      cases evaluation with
      | unary comparison negated =>
          cases comparison with
          | @binary _ _ _ _ _ _ _ leftValue rightValue _ leftChild rightChild applied =>
              cases leftValue <;> cases rightValue <;>
                simp only [Core.BinaryOp.apply, reduceCtorEq] at applied
              case word.word leftWord rightWord =>
                cases applied
                cases negated
                exact .lessEqual (leftIH leftChild) (rightIH rightChild)
  | greaterEqual _ _ leftIH rightIH =>
      cases evaluation with
      | unary comparison negated =>
          cases comparison with
          | wordLt leftChild rightChild =>
              cases negated
              exact .greaterEqual (leftIH leftChild) (rightIH rightChild)
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
