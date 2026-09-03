import Solcore.Syntax.DeclarativeCoreExpressionNonAssociativeOutcomeProperties
import Solcore.Syntax.DeclarativeCoreExpressionOperatorExactnessProperties

/-! Exact ASTs and rejecting endpoints of non-associative expression layers. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Operand and operator exactness fixes both plain and binary ASTs. -/
theorem NonAssociativeOrdinaryParses.value_unique
    {operandOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {operandRejects : Remainder → Remainder → Prop}
    (outcomes : ExactDeterministicOutcomeSpec operandOrdinary operandRejects)
    {precedence : Nat} {input : Remainder} {left right : Syntax.Expr}
    {afterLeft afterRight : Remainder}
    (leftParsed : NonAssociativeOrdinaryParses operandOrdinary precedence input left afterLeft)
    (rightParsed : NonAssociativeOrdinaryParses operandOrdinary precedence input right afterRight) :
    left = right := by
  cases leftParsed with
  | plain leftOperand leftAbsent =>
      cases rightParsed with
      | plain rightOperand _ => exact outcomes.successValueUnique leftOperand rightOperand
      | binary rightOperand rightOperator _ =>
          have outputEq := outcomes.successOutputUnique leftOperand rightOperand
          subst outputEq
          exact False.elim (leftAbsent.not_parses rightOperator)
  | binary leftOperand leftOperator leftRight =>
      cases rightParsed with
      | plain rightOperand rightAbsent =>
          have outputEq := outcomes.successOutputUnique leftOperand rightOperand
          subst outputEq
          exact False.elim (rightAbsent.not_parses leftOperator)
      | binary rightOperand rightOperator rightRight =>
          rcases outcomes.successResultUnique leftOperand rightOperand with ⟨leftEq, leftEndEq⟩
          subst leftEq
          subst leftEndEq
          rcases leftOperator.result_unique rightOperator with ⟨operatorEq, operatorEndEq⟩
          subst operatorEq
          subst operatorEndEq
          have rightEq := outcomes.successValueUnique leftRight rightRight
          subst rightEq
          rfl

/-- Rejection fixes either the initial or committed right-operand endpoint. -/
theorem NonAssociativeRejects.output_unique
    {operandOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {operandRejects : Remainder → Remainder → Prop}
    (outcomes : ExactDeterministicOutcomeSpec operandOrdinary operandRejects)
    {precedence : Nat} {input left right : Remainder}
    (leftRejected : NonAssociativeRejects operandOrdinary operandRejects precedence input left)
    (rightRejected : NonAssociativeRejects operandOrdinary operandRejects precedence input right) :
    left = right := by
  cases leftRejected with
  | firstRejected leftOperand =>
      cases rightRejected with
      | firstRejected rightOperand => exact outcomes.rejectOutputUnique leftOperand rightOperand
      | rightRejected rightOperand _ _ =>
          exact False.elim (outcomes.successRejectDisjoint leftOperand ⟨_, _, rightOperand⟩)
  | rightRejected leftOperand leftOperator leftRight =>
      cases rightRejected with
      | firstRejected rightOperand =>
          exact False.elim (outcomes.successRejectDisjoint rightOperand ⟨_, _, leftOperand⟩)
      | rightRejected rightOperand rightOperator rightRight =>
          have leftEndEq := outcomes.successOutputUnique leftOperand rightOperand
          subst leftEndEq
          have operatorEndEq := (leftOperator.result_unique rightOperator).2
          subst operatorEndEq
          exact outcomes.rejectOutputUnique leftRight rightRight

/-- Exact operands lift through any single non-associative precedence layer. -/
theorem nonAssociativeExactOutcomeSpec
    {operandOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {operandRejects : Remainder → Remainder → Prop}
    (outcomes : ExactDeterministicOutcomeSpec operandOrdinary operandRejects)
    (precedence : Nat) :
    ExactDeterministicOutcomeSpec
      (NonAssociativeOrdinaryParses operandOrdinary precedence)
      (NonAssociativeRejects operandOrdinary operandRejects precedence) where
  toDeterministicOutcomeSpec := nonAssociativeDeterministicOutcomeSpec
    outcomes.toDeterministicOutcomeSpec precedence
  successValueUnique := NonAssociativeOrdinaryParses.value_unique outcomes
  rejectOutputUnique := NonAssociativeRejects.output_unique outcomes

end Solcore.Syntax.DeclarativeGrammar
