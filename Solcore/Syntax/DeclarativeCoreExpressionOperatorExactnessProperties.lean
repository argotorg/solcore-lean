import Solcore.Syntax.DeclarativeCoreExpressionUnaryLeftOutcomeProperties
import Solcore.Syntax.DeclarativePrimitiveExactnessProperties

/-! Exact operator tokens, prefix sequences, and unary expression outcomes. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Unary spelling fixes its operator, token span, and complete remainder. -/
theorem UnaryOperatorParses.result_unique
    {input afterLeft afterRight : Remainder}
    {left right : Located UnaryOp}
    (leftParsed : UnaryOperatorParses input left afterLeft)
    (rightParsed : UnaryOperatorParses input right afterRight) :
    left = right ∧ afterLeft = afterRight := by
  have outputEq := leftParsed.2.trans rightParsed.2.symm
  have tokenEq := leftParsed.1.token_unique rightParsed.1
  rcases left with ⟨leftSpan, leftValue⟩
  rcases right with ⟨rightSpan, rightValue⟩
  cases leftValue <;> cases rightValue <;> simp_all [UnaryOp.symbol]

/-- An absent unary operator excludes every positive unary-token judgment. -/
theorem UnaryOperatorAbsentAt.not_parses
    {input output : Remainder} {operator : Located UnaryOp}
    (absent : UnaryOperatorAbsentAt input)
    (parsed : UnaryOperatorParses input operator output) : False := by
  rcases operator with ⟨span, value⟩
  cases value with
  | logicalNot => exact absent.1 ⟨span, parsed.1⟩
  | bitNot => exact absent.2 ⟨span, parsed.1⟩

/-- A precedence-filtered binary token fixes its operator, span, and remainder. -/
theorem BinaryOperatorAtPrecedenceParses.result_unique
    {precedence : Nat} {input afterLeft afterRight : Remainder}
    {left right : Located BinaryOp}
    (leftParsed : BinaryOperatorAtPrecedenceParses precedence input left afterLeft)
    (rightParsed : BinaryOperatorAtPrecedenceParses precedence input right afterRight) :
    left = right ∧ afterLeft = afterRight := by
  have outputEq := leftParsed.2.2.trans rightParsed.2.2.symm
  have tokenEq := leftParsed.2.1.token_unique rightParsed.2.1
  rcases left with ⟨leftSpan, leftValue⟩
  rcases right with ⟨rightSpan, rightValue⟩
  cases leftValue <;> cases rightValue <;> simp_all [BinaryOp.symbol]

/-- Absence at one precedence excludes every positive token at that precedence. -/
theorem BinaryOperatorAtPrecedenceAbsentAt.not_parses
    {precedence : Nat} {input output : Remainder} {operator : Located BinaryOp}
    (absent : BinaryOperatorAtPrecedenceAbsentAt precedence input)
    (parsed : BinaryOperatorAtPrecedenceParses precedence input operator output) :
    False :=
  absent ⟨operator.span, operator.value, parsed.1, parsed.2.1⟩

/-- A maximal prefix sequence fixes all operators in source order and its end. -/
theorem UnaryOperatorsParses.result_unique
    {input : Remainder} {left right : List (Located UnaryOp)}
    {afterLeft afterRight : Remainder}
    (leftParsed : UnaryOperatorsParses input left afterLeft)
    (rightParsed : UnaryOperatorsParses input right afterRight) :
    left = right ∧ afterLeft = afterRight := by
  induction leftParsed generalizing right afterRight with
  | done leftAbsent =>
      cases rightParsed with
      | done => exact ⟨rfl, rfl⟩
      | next rightOperator _ => exact False.elim (leftAbsent.not_parses rightOperator)
  | next leftOperator leftTail ih =>
      cases rightParsed with
      | done rightAbsent => exact False.elim (rightAbsent.not_parses leftOperator)
      | next rightOperator rightTail =>
          rcases leftOperator.result_unique rightOperator with ⟨operatorEq, outputEq⟩
          subst operatorEq
          subst outputEq
          rcases ih rightTail with ⟨tailEq, finalEq⟩
          subst tailEq
          exact ⟨rfl, finalEq⟩

/-- Exact postfix values fix the complete source-preserving unary AST. -/
theorem ExpressionUnaryOrdinaryParses.value_unique
    {postfixOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {postfixRejects : Remainder → Remainder → Prop}
    (outcomes : ExactDeterministicOutcomeSpec postfixOrdinary postfixRejects)
    {input : Remainder} {left right : Syntax.Expr}
    {afterLeft afterRight : Remainder}
    (leftParsed : ExpressionUnaryOrdinaryParses postfixOrdinary input left afterLeft)
    (rightParsed : ExpressionUnaryOrdinaryParses postfixOrdinary input right afterRight) :
    left = right := by
  rcases leftParsed with ⟨leftOperators, leftAfter, leftBase, leftPrefix, leftPostfix, leftEq⟩
  rcases rightParsed with
    ⟨rightOperators, rightAfter, rightBase, rightPrefix, rightPostfix, rightEq⟩
  rcases leftPrefix.result_unique rightPrefix with ⟨prefixEq, outputEq⟩
  subst prefixEq
  subst outputEq
  have baseEq := outcomes.successValueUnique leftPostfix rightPostfix
  subst baseEq
  exact leftEq.trans rightEq.symm

/-- Exact postfix rejection fixes the endpoint after the maximal unary prefix. -/
theorem ExpressionUnaryRejects.output_unique
    {postfixOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {postfixRejects : Remainder → Remainder → Prop}
    (outcomes : ExactDeterministicOutcomeSpec postfixOrdinary postfixRejects)
    {input left right : Remainder}
    (leftRejected : ExpressionUnaryRejects postfixRejects input left)
    (rightRejected : ExpressionUnaryRejects postfixRejects input right) : left = right := by
  cases leftRejected with
  | postfixRejected leftPrefix leftPostfix =>
      cases rightRejected with
      | postfixRejected rightPrefix rightPostfix =>
          have outputEq := leftPrefix.output_unique rightPrefix
          subst outputEq
          exact outcomes.rejectOutputUnique leftPostfix rightPostfix

/-- Exact postfix outcomes lift through maximal unary-prefix parsing. -/
theorem expressionUnaryExactOutcomeSpec
    {postfixOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {postfixRejects : Remainder → Remainder → Prop}
    (outcomes : ExactDeterministicOutcomeSpec postfixOrdinary postfixRejects) :
    ExactDeterministicOutcomeSpec (ExpressionUnaryOrdinaryParses postfixOrdinary)
      (ExpressionUnaryRejects postfixRejects) where
  toDeterministicOutcomeSpec := expressionUnaryDeterministicOutcomeSpec
    outcomes.toDeterministicOutcomeSpec
  successValueUnique := ExpressionUnaryOrdinaryParses.value_unique outcomes
  rejectOutputUnique := ExpressionUnaryRejects.output_unique outcomes

end Solcore.Syntax.DeclarativeGrammar
