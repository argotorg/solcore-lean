import Solcore.Syntax.DeclarativeCoreExpressionLayerOutcomeGrammar

/-! Deterministic ordinary outcomes for Core non-associative expressions. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

private theorem binaryAbsent_conflicts_parsed
    {precedence : Nat} {input output : Remainder}
    {operator : Located BinaryOp}
    (absent : BinaryOperatorAtPrecedenceAbsentAt precedence input)
    (parsed : BinaryOperatorAtPrecedenceParses precedence input operator
      output) : False :=
  absent ⟨operator.span, operator.value, parsed.1, parsed.2.1⟩

private theorem binaryOperator_output_unique
    {precedence : Nat} {input leftOutput rightOutput : Remainder}
    {leftOperator rightOperator : Located BinaryOp}
    (leftParsed : BinaryOperatorAtPrecedenceParses precedence input
      leftOperator leftOutput)
    (rightParsed : BinaryOperatorAtPrecedenceParses precedence input
      rightOperator rightOutput) : leftOutput = rightOutput := by
  rw [leftParsed.2.2, rightParsed.2.2]

/-- Ordinary non-associative success has a unique output remainder. -/
theorem NonAssociativeOrdinaryParses.output_unique
    {operandOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {operandRejects : Remainder → Remainder → Prop}
    (outcomes : DeterministicOutcomeSpec operandOrdinary operandRejects)
    {precedence : Nat} {input : Remainder}
    {left right : Syntax.Expr} {afterLeft afterRight : Remainder}
    (leftParsed : NonAssociativeOrdinaryParses operandOrdinary precedence
      input left afterLeft)
    (rightParsed : NonAssociativeOrdinaryParses operandOrdinary precedence
      input right afterRight) : afterLeft = afterRight := by
  cases leftParsed with
  | plain leftOperand leftAbsent =>
      cases rightParsed with
      | plain rightOperand rightAbsent =>
          exact outcomes.successOutputUnique leftOperand rightOperand
      | binary rightOperand rightOperator rightRight =>
          have afterOperandEq := outcomes.successOutputUnique leftOperand
            rightOperand
          subst afterOperandEq
          exact False.elim
            (binaryAbsent_conflicts_parsed leftAbsent rightOperator)
  | binary leftOperand leftOperator leftRight =>
      cases rightParsed with
      | plain rightOperand rightAbsent =>
          have afterOperandEq := outcomes.successOutputUnique leftOperand
            rightOperand
          subst afterOperandEq
          exact False.elim
            (binaryAbsent_conflicts_parsed rightAbsent leftOperator)
      | binary rightOperand rightOperator rightRight =>
          have afterOperandEq := outcomes.successOutputUnique leftOperand
            rightOperand
          subst afterOperandEq
          have afterOperatorEq := binaryOperator_output_unique leftOperator
            rightOperator
          subst afterOperatorEq
          exact outcomes.successOutputUnique leftRight rightRight

/-- Non-associative rejection excludes ordinary success. -/
theorem NonAssociativeRejects.disjointOrdinary
    {operandOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {operandRejects : Remainder → Remainder → Prop}
    (outcomes : DeterministicOutcomeSpec operandOrdinary operandRejects)
    {precedence : Nat} {input rejected : Remainder}
    (rejection : NonAssociativeRejects operandOrdinary operandRejects
      precedence input rejected) :
    ¬ ∃ expression output,
      NonAssociativeOrdinaryParses operandOrdinary precedence input expression
        output := by
  rintro ⟨expression, output, parsed⟩
  cases rejection with
  | firstRejected firstRejected =>
      cases parsed with
      | plain operand absent =>
          exact outcomes.successRejectDisjoint firstRejected
            ⟨_, _, operand⟩
      | binary operand operator right =>
          exact outcomes.successRejectDisjoint firstRejected
            ⟨_, _, operand⟩
  | rightRejected rejectedLeft rejectedOperator rejectedRight =>
      cases parsed with
      | plain successfulLeft absent =>
          have afterLeftEq := outcomes.successOutputUnique rejectedLeft
            successfulLeft
          subst afterLeftEq
          exact binaryAbsent_conflicts_parsed absent rejectedOperator
      | binary successfulLeft successfulOperator successfulRight =>
          have afterLeftEq := outcomes.successOutputUnique rejectedLeft
            successfulLeft
          subst afterLeftEq
          have afterOperatorEq := binaryOperator_output_unique
            rejectedOperator successfulOperator
          subst afterOperatorEq
          exact outcomes.successRejectDisjoint rejectedRight
            ⟨_, _, successfulRight⟩

/-- Construct the deterministic outcome contract for a non-associative
precedence layer. -/
theorem nonAssociativeDeterministicOutcomeSpec
    {operandOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {operandRejects : Remainder → Remainder → Prop}
    (outcomes : DeterministicOutcomeSpec operandOrdinary operandRejects)
    (precedence : Nat) :
    DeterministicOutcomeSpec
      (NonAssociativeOrdinaryParses operandOrdinary precedence)
      (NonAssociativeRejects operandOrdinary operandRejects precedence) where
  successOutputUnique := NonAssociativeOrdinaryParses.output_unique outcomes
  successRejectDisjoint := NonAssociativeRejects.disjointOrdinary outcomes

end Solcore.Syntax.DeclarativeGrammar
