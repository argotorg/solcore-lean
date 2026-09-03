import Solcore.Syntax.DeclarativeCoreExpressionOperatorExactnessProperties

/-! Exact left-associated expression ASTs and first-rejecting endpoints. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- A maximal tail fixes the complete result when both parses share their base. -/
theorem LeftAssociativeTailParses.result_unique
    {operandOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {operandRejects : Remainder → Remainder → Prop}
    (outcomes : ExactDeterministicOutcomeSpec operandOrdinary operandRejects)
    {precedence : Nat} {input : Remainder} {base left right : Syntax.Expr}
    {afterLeft afterRight : Remainder}
    (leftParsed : LeftAssociativeTailParses operandOrdinary precedence input
      base left afterLeft)
    (rightParsed : LeftAssociativeTailParses operandOrdinary precedence input
      base right afterRight) : left = right ∧ afterLeft = afterRight := by
  induction leftParsed generalizing right afterRight with
  | done leftAbsent =>
      cases rightParsed with
      | done => exact ⟨rfl, rfl⟩
      | next rightOperator _ _ => exact False.elim (leftAbsent.not_parses rightOperator)
  | next leftOperator leftOperand leftTail ih =>
      cases rightParsed with
      | done rightAbsent => exact False.elim (rightAbsent.not_parses leftOperator)
      | next rightOperator rightOperand rightTail =>
          rcases leftOperator.result_unique rightOperator with ⟨operatorEq, operatorEndEq⟩
          subst operatorEq
          subst operatorEndEq
          rcases outcomes.successResultUnique leftOperand rightOperand with
            ⟨operandEq, operandEndEq⟩
          subst operandEq
          subst operandEndEq
          exact ih rightTail

/-- Exact operand values fix the entire left-associated AST and retained spans. -/
theorem LeftAssociativeOrdinaryParses.value_unique
    {operandOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {operandRejects : Remainder → Remainder → Prop}
    (outcomes : ExactDeterministicOutcomeSpec operandOrdinary operandRejects)
    {precedence : Nat} {input : Remainder} {left right : Syntax.Expr}
    {afterLeft afterRight : Remainder}
    (leftParsed : LeftAssociativeOrdinaryParses operandOrdinary precedence
      input left afterLeft)
    (rightParsed : LeftAssociativeOrdinaryParses operandOrdinary precedence
      input right afterRight) : left = right := by
  rcases leftParsed with ⟨leftBase, leftAfterBase, leftOperand, leftTail⟩
  rcases rightParsed with ⟨rightBase, rightAfterBase, rightOperand, rightTail⟩
  rcases outcomes.successResultUnique leftOperand rightOperand with ⟨baseEq, outputEq⟩
  subst baseEq
  subst outputEq
  exact (leftTail.result_unique outcomes rightTail).1

/-- At a fixed accumulator, a rejected tail fixes its first failing endpoint. -/
theorem LeftAssociativeTailRejects.output_unique
    {operandOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {operandRejects : Remainder → Remainder → Prop}
    (outcomes : ExactDeterministicOutcomeSpec operandOrdinary operandRejects)
    {precedence : Nat} {input left right : Remainder} {base : Syntax.Expr}
    (leftRejected : LeftAssociativeTailRejects operandOrdinary operandRejects
      precedence input base left)
    (rightRejected : LeftAssociativeTailRejects operandOrdinary operandRejects
      precedence input base right) : left = right := by
  induction leftRejected generalizing right with
  | rightRejected leftOperator leftOperand =>
      cases rightRejected with
      | rightRejected rightOperator rightOperand =>
          have outputEq := (leftOperator.result_unique rightOperator).2
          subst outputEq
          exact outcomes.rejectOutputUnique leftOperand rightOperand
      | laterRejected rightOperator rightOperand _ =>
          have outputEq := (leftOperator.result_unique rightOperator).2
          subst outputEq
          exact False.elim (outcomes.successRejectDisjoint leftOperand ⟨_, _, rightOperand⟩)
  | laterRejected leftOperator leftOperand leftTail ih =>
      cases rightRejected with
      | rightRejected rightOperator rightOperand =>
          have outputEq := (leftOperator.result_unique rightOperator).2
          subst outputEq
          exact False.elim (outcomes.successRejectDisjoint rightOperand ⟨_, _, leftOperand⟩)
      | laterRejected rightOperator rightOperand rightTail =>
          rcases leftOperator.result_unique rightOperator with ⟨operatorEq, operatorEndEq⟩
          subst operatorEq
          subst operatorEndEq
          rcases outcomes.successResultUnique leftOperand rightOperand with
            ⟨operandEq, operandEndEq⟩
          subst operandEq
          subst operandEndEq
          exact ih rightTail

/-- Complete left-associative rejection fixes its first failing endpoint. -/
theorem LeftAssociativeRejects.output_unique
    {operandOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {operandRejects : Remainder → Remainder → Prop}
    (outcomes : ExactDeterministicOutcomeSpec operandOrdinary operandRejects)
    {precedence : Nat} {input left right : Remainder}
    (leftRejected : LeftAssociativeRejects operandOrdinary operandRejects
      precedence input left)
    (rightRejected : LeftAssociativeRejects operandOrdinary operandRejects
      precedence input right) : left = right := by
  cases leftRejected with
  | firstRejected leftOperand =>
      cases rightRejected with
      | firstRejected rightOperand => exact outcomes.rejectOutputUnique leftOperand rightOperand
      | tailRejected rightOperand _ =>
          exact False.elim (outcomes.successRejectDisjoint leftOperand ⟨_, _, rightOperand⟩)
  | tailRejected leftOperand leftTail =>
      cases rightRejected with
      | firstRejected rightOperand =>
          exact False.elim (outcomes.successRejectDisjoint rightOperand ⟨_, _, leftOperand⟩)
      | tailRejected rightOperand rightTail =>
          rcases outcomes.successResultUnique leftOperand rightOperand with ⟨baseEq, outputEq⟩
          subst baseEq
          subst outputEq
          exact leftTail.output_unique outcomes rightTail

/-- Exact operands yield exact outcomes at any left-associated precedence. -/
theorem leftAssociativeExactOutcomeSpec
    {operandOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {operandRejects : Remainder → Remainder → Prop}
    (outcomes : ExactDeterministicOutcomeSpec operandOrdinary operandRejects)
    (precedence : Nat) :
    ExactDeterministicOutcomeSpec
      (LeftAssociativeOrdinaryParses operandOrdinary precedence)
      (LeftAssociativeRejects operandOrdinary operandRejects precedence) where
  toDeterministicOutcomeSpec := leftAssociativeDeterministicOutcomeSpec
    outcomes.toDeterministicOutcomeSpec precedence
  successValueUnique := LeftAssociativeOrdinaryParses.value_unique outcomes
  rejectOutputUnique := LeftAssociativeRejects.output_unique outcomes

end Solcore.Syntax.DeclarativeGrammar
