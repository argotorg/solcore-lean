import Solcore.Syntax.DeclarativeCoreExpressionLayerOutcomeGrammar

/-!
Deterministic ordinary outcomes for Core unary and left-associative expression
layers.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

private theorem unaryAbsent_conflicts_parsed
    {input output : Remainder} {operator : Located UnaryOp}
    (absent : UnaryOperatorAbsentAt input)
    (parsed : UnaryOperatorParses input operator output) : False := by
  rcases operator with ⟨span, operator⟩
  cases operator with
  | logicalNot =>
      exact absent.1 ⟨span, by
        simpa [UnaryOperatorParses, UnaryOp.symbol] using parsed.1⟩
  | bitNot =>
      exact absent.2 ⟨span, by
        simpa [UnaryOperatorParses, UnaryOp.symbol] using parsed.1⟩

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

/-- Maximal unary-prefix parsing has a unique output remainder. -/
theorem UnaryOperatorsParses.output_unique
    {input : Remainder} {left right : List (Located UnaryOp)}
    {afterLeft afterRight : Remainder}
    (leftParsed : UnaryOperatorsParses input left afterLeft)
    (rightParsed : UnaryOperatorsParses input right afterRight) :
    afterLeft = afterRight := by
  induction leftParsed generalizing right afterRight with
  | done leftAbsent =>
      cases rightParsed with
      | done => rfl
      | next rightOperator rightTail =>
          exact False.elim
            (unaryAbsent_conflicts_parsed leftAbsent rightOperator)
  | next leftOperator leftTail inductionHypothesis =>
      cases rightParsed with
      | done rightAbsent =>
          exact False.elim
            (unaryAbsent_conflicts_parsed rightAbsent leftOperator)
      | next rightOperator rightTail =>
          have afterOperatorEq := leftOperator.2.trans rightOperator.2.symm
          subst afterOperatorEq
          exact inductionHypothesis rightTail

/-- Ordinary unary-layer success has a unique output remainder. -/
theorem ExpressionUnaryOrdinaryParses.output_unique
    {postfixOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {postfixRejects : Remainder → Remainder → Prop}
    (outcomes : DeterministicOutcomeSpec postfixOrdinary postfixRejects)
    {input : Remainder} {left right : Syntax.Expr}
    {afterLeft afterRight : Remainder}
    (leftParsed : ExpressionUnaryOrdinaryParses postfixOrdinary input left
      afterLeft)
    (rightParsed : ExpressionUnaryOrdinaryParses postfixOrdinary input right
      afterRight) : afterLeft = afterRight := by
  rcases leftParsed with
    ⟨leftOperators, leftAfterOperators, leftBase, leftOperatorsParsed,
      leftBaseParsed, leftEq⟩
  rcases rightParsed with
    ⟨rightOperators, rightAfterOperators, rightBase, rightOperatorsParsed,
      rightBaseParsed, rightEq⟩
  have operatorsEq := leftOperatorsParsed.output_unique rightOperatorsParsed
  subst operatorsEq
  exact outcomes.successOutputUnique leftBaseParsed rightBaseParsed

/-- Unary rejection excludes ordinary unary success. -/
theorem ExpressionUnaryRejects.disjointOrdinary
    {postfixOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {postfixRejects : Remainder → Remainder → Prop}
    (outcomes : DeterministicOutcomeSpec postfixOrdinary postfixRejects)
    {input rejected : Remainder}
    (rejection : ExpressionUnaryRejects postfixRejects input rejected) :
    ¬ ∃ expression output,
      ExpressionUnaryOrdinaryParses postfixOrdinary input expression output :=
    by
  rintro ⟨expression, output, operators, afterOperators, base,
    operatorsParsed, baseParsed, expressionEq⟩
  cases rejection with
  | postfixRejected rejectedOperators rejectedPostfix =>
      have afterOperatorsEq :=
        rejectedOperators.output_unique operatorsParsed
      subst afterOperatorsEq
      exact outcomes.successRejectDisjoint rejectedPostfix
        ⟨base, output, baseParsed⟩

/-- Construct the deterministic outcome contract for the unary layer. -/
theorem expressionUnaryDeterministicOutcomeSpec
    {postfixOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {postfixRejects : Remainder → Remainder → Prop}
    (outcomes : DeterministicOutcomeSpec postfixOrdinary postfixRejects) :
    DeterministicOutcomeSpec
      (ExpressionUnaryOrdinaryParses postfixOrdinary)
      (ExpressionUnaryRejects postfixRejects) where
  successOutputUnique := ExpressionUnaryOrdinaryParses.output_unique outcomes
  successRejectDisjoint := ExpressionUnaryRejects.disjointOrdinary outcomes

/-- A maximal left-associative tail has a unique output remainder. -/
theorem LeftAssociativeTailParses.output_unique
    {operandOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {operandRejects : Remainder → Remainder → Prop}
    (outcomes : DeterministicOutcomeSpec operandOrdinary operandRejects)
    {precedence : Nat} {input : Remainder}
    {leftBase rightBase leftResult rightResult : Syntax.Expr}
    {afterLeft afterRight : Remainder}
    (leftParsed : LeftAssociativeTailParses operandOrdinary precedence input
      leftBase leftResult afterLeft)
    (rightParsed : LeftAssociativeTailParses operandOrdinary precedence input
      rightBase rightResult afterRight) : afterLeft = afterRight := by
  induction leftParsed generalizing rightBase rightResult afterRight with
  | done leftAbsent =>
      cases rightParsed with
      | done => rfl
      | next rightOperator rightOperand rightTail =>
          exact False.elim
            (binaryAbsent_conflicts_parsed leftAbsent rightOperator)
  | next leftOperator leftOperand leftTail inductionHypothesis =>
      cases rightParsed with
      | done rightAbsent =>
          exact False.elim
            (binaryAbsent_conflicts_parsed rightAbsent leftOperator)
      | next rightOperator rightOperand rightTail =>
          have afterOperatorEq := binaryOperator_output_unique leftOperator
            rightOperator
          subst afterOperatorEq
          have afterOperandEq := outcomes.successOutputUnique leftOperand
            rightOperand
          subst afterOperandEq
          exact inductionHypothesis rightTail

/-- A rejected left-associative tail excludes every ordinary tail success. -/
theorem LeftAssociativeTailRejects.disjointOrdinary
    {operandOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {operandRejects : Remainder → Remainder → Prop}
    (outcomes : DeterministicOutcomeSpec operandOrdinary operandRejects)
    {precedence : Nat} {input rejected : Remainder} {left : Syntax.Expr}
    (rejection : LeftAssociativeTailRejects operandOrdinary operandRejects
      precedence input left rejected) :
    ¬ ∃ successfulLeft result output,
      LeftAssociativeTailParses operandOrdinary precedence input successfulLeft
        result output := by
  induction rejection with
  | rightRejected rejectedOperator rejectedRight =>
      rintro ⟨successfulLeft, result, output, parsed⟩
      cases parsed with
      | done absent =>
          exact binaryAbsent_conflicts_parsed absent rejectedOperator
      | next successfulOperator successfulRight successfulTail =>
          have afterOperatorEq := binaryOperator_output_unique
            rejectedOperator successfulOperator
          subst afterOperatorEq
          exact outcomes.successRejectDisjoint rejectedRight
            ⟨_, _, successfulRight⟩
  | laterRejected rejectedOperator rejectedRight rejectedTail
        inductionHypothesis =>
      rintro ⟨successfulLeft, result, output, parsed⟩
      cases parsed with
      | done absent =>
          exact binaryAbsent_conflicts_parsed absent rejectedOperator
      | next successfulOperator successfulRight successfulTail =>
          have afterOperatorEq := binaryOperator_output_unique
            rejectedOperator successfulOperator
          subst afterOperatorEq
          have afterRightEq := outcomes.successOutputUnique rejectedRight
            successfulRight
          subst afterRightEq
          exact inductionHypothesis ⟨_, _, _, successfulTail⟩

/-- Ordinary left-associative success has a unique output remainder. -/
theorem LeftAssociativeOrdinaryParses.output_unique
    {operandOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {operandRejects : Remainder → Remainder → Prop}
    (outcomes : DeterministicOutcomeSpec operandOrdinary operandRejects)
    {precedence : Nat} {input : Remainder}
    {left right : Syntax.Expr} {afterLeft afterRight : Remainder}
    (leftParsed : LeftAssociativeOrdinaryParses operandOrdinary precedence
      input left afterLeft)
    (rightParsed : LeftAssociativeOrdinaryParses operandOrdinary precedence
      input right afterRight) : afterLeft = afterRight := by
  rcases leftParsed with ⟨leftBase, leftAfterBase, leftBaseParsed, leftTail⟩
  rcases rightParsed with
    ⟨rightBase, rightAfterBase, rightBaseParsed, rightTail⟩
  have afterBaseEq := outcomes.successOutputUnique leftBaseParsed
    rightBaseParsed
  subst afterBaseEq
  exact leftTail.output_unique outcomes rightTail

/-- Complete left-associative rejection excludes ordinary success. -/
theorem LeftAssociativeRejects.disjointOrdinary
    {operandOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {operandRejects : Remainder → Remainder → Prop}
    (outcomes : DeterministicOutcomeSpec operandOrdinary operandRejects)
    {precedence : Nat} {input rejected : Remainder}
    (rejection : LeftAssociativeRejects operandOrdinary operandRejects
      precedence input rejected) :
    ¬ ∃ expression output,
      LeftAssociativeOrdinaryParses operandOrdinary precedence input expression
        output := by
  rintro ⟨expression, output, left, afterLeft, leftParsed, tailParsed⟩
  cases rejection with
  | firstRejected firstRejected =>
      exact outcomes.successRejectDisjoint firstRejected
        ⟨left, afterLeft, leftParsed⟩
  | tailRejected rejectedLeft rejectedTail =>
      have afterLeftEq := outcomes.successOutputUnique rejectedLeft leftParsed
      subst afterLeftEq
      exact rejectedTail.disjointOrdinary outcomes
        ⟨left, expression, output, tailParsed⟩

/-- Construct the deterministic outcome contract for a left-associative
precedence layer. -/
theorem leftAssociativeDeterministicOutcomeSpec
    {operandOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {operandRejects : Remainder → Remainder → Prop}
    (outcomes : DeterministicOutcomeSpec operandOrdinary operandRejects)
    (precedence : Nat) :
    DeterministicOutcomeSpec
      (LeftAssociativeOrdinaryParses operandOrdinary precedence)
      (LeftAssociativeRejects operandOrdinary operandRejects precedence) where
  successOutputUnique :=
    LeftAssociativeOrdinaryParses.output_unique outcomes
  successRejectDisjoint :=
    LeftAssociativeRejects.disjointOrdinary outcomes

end Solcore.Syntax.DeclarativeGrammar
