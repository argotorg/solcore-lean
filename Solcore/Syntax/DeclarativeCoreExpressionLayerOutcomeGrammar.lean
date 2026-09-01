import Solcore.Syntax.DeclarativeCoreExpressionLayerGrammar
import Solcore.Syntax.DeclarativeDelimitedOutcomeGrammar

/-!
Parser-independent ordinary successes and exact rejection traces for the
generic Core expression operator layers above a supplied postfix outcome.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Ordinary unary-layer success is the existing maximal unary grammar. -/
abbrev ExpressionUnaryOrdinaryParses := ExpressionUnaryParses

/-- A unary layer rejects exactly when its postfix operand rejects after the
maximal prefix sequence. -/
inductive ExpressionUnaryRejects
    (postfixRejects : Remainder → Remainder → Prop) :
    Remainder → Remainder → Prop where
  | postfixRejected {input afterOperators rejected : Remainder}
      {operators : List (Located UnaryOp)}
      (operatorsParsed : UnaryOperatorsParses input operators afterOperators)
      (postfixRejected : postfixRejects afterOperators rejected) :
      ExpressionUnaryRejects postfixRejects input rejected

/-- Ordinary left-associative success is the existing maximal grammar. -/
abbrev LeftAssociativeOrdinaryParses := LeftAssociativeParses

/-- Exact rejection while extending one left-associated precedence tail. -/
inductive LeftAssociativeTailRejects
    (operandOrdinary : Remainder → Syntax.Expr → Remainder → Prop)
    (operandRejects : Remainder → Remainder → Prop)
    (precedence : Nat) :
    Remainder → Syntax.Expr → Remainder → Prop where
  | rightRejected {input afterOperator rejected : Remainder}
      {left : Syntax.Expr} {operator : Located BinaryOp}
      (operatorParsed : BinaryOperatorAtPrecedenceParses precedence input
        operator afterOperator)
      (rightRejected : operandRejects afterOperator rejected) :
      LeftAssociativeTailRejects operandOrdinary operandRejects precedence
        input left rejected
  | laterRejected
      {input afterOperator afterRight rejected : Remainder}
      {left right : Syntax.Expr} {operator : Located BinaryOp}
      (operatorParsed : BinaryOperatorAtPrecedenceParses precedence input
        operator afterOperator)
      (rightParsed : operandOrdinary afterOperator right afterRight)
      (tailRejected : LeftAssociativeTailRejects operandOrdinary
        operandRejects precedence afterRight (binaryNode left operator right)
          rejected) :
      LeftAssociativeTailRejects operandOrdinary operandRejects precedence
        input left rejected

/-- Exact rejection of one complete left-associative precedence layer. -/
inductive LeftAssociativeRejects
    (operandOrdinary : Remainder → Syntax.Expr → Remainder → Prop)
    (operandRejects : Remainder → Remainder → Prop)
    (precedence : Nat) : Remainder → Remainder → Prop where
  | firstRejected {input rejected : Remainder}
      (firstRejected : operandRejects input rejected) :
      LeftAssociativeRejects operandOrdinary operandRejects precedence input
        rejected
  | tailRejected {input afterLeft rejected : Remainder}
      {left : Syntax.Expr}
      (leftParsed : operandOrdinary input left afterLeft)
      (tailRejected : LeftAssociativeTailRejects operandOrdinary
        operandRejects precedence afterLeft left rejected) :
      LeftAssociativeRejects operandOrdinary operandRejects precedence input
        rejected

/-- Ordinary non-associative success is the existing maximal grammar. -/
abbrev NonAssociativeOrdinaryParses := NonAssociativeParses

/-- Exact rejection of one non-associative precedence layer. -/
inductive NonAssociativeRejects
    (operandOrdinary : Remainder → Syntax.Expr → Remainder → Prop)
    (operandRejects : Remainder → Remainder → Prop)
    (precedence : Nat) : Remainder → Remainder → Prop where
  | firstRejected {input rejected : Remainder}
      (firstRejected : operandRejects input rejected) :
      NonAssociativeRejects operandOrdinary operandRejects precedence input
        rejected
  | rightRejected
      {input afterLeft afterOperator rejected : Remainder}
      {left : Syntax.Expr} {operator : Located BinaryOp}
      (leftParsed : operandOrdinary input left afterLeft)
      (operatorParsed : BinaryOperatorAtPrecedenceParses precedence afterLeft
        operator afterOperator)
      (rightRejected : operandRejects afterOperator rejected) :
      NonAssociativeRejects operandOrdinary operandRejects precedence input
        rejected

/-- Ordinary conditional success is the existing right-associated grammar. -/
abbrev ConditionalOrdinaryParses := ConditionalParses

/-- Exact rejection while consuming a conditional suffix. -/
inductive ConditionalTailRejects
    (nestedOrdinary alternativeOrdinary :
      Remainder → Syntax.Expr → Remainder → Prop)
    (nestedRejects alternativeRejects : Remainder → Remainder → Prop) :
    Remainder → Syntax.Expr → Remainder → Prop where
  | thenRejected {input afterQuestion rejected : Remainder}
      {condition : Syntax.Expr} (questionSpan : SourceSpan)
      (questionParsed : ExactTokenParses (.symbol .question) input
        questionSpan afterQuestion)
      (thenRejected : nestedRejects afterQuestion rejected) :
      ConditionalTailRejects nestedOrdinary alternativeOrdinary nestedRejects
        alternativeRejects input condition rejected
  | colonMissing {input afterQuestion afterThen : Remainder}
      {condition thenBranch : Syntax.Expr} (questionSpan : SourceSpan)
      (questionParsed : ExactTokenParses (.symbol .question) input
        questionSpan afterQuestion)
      (thenParsed : nestedOrdinary afterQuestion thenBranch afterThen)
      (colonAbsent : TokenKindAbsentAt afterThen.tokens afterThen.endIndex
        afterThen.cursor (.symbol .colon)) :
      ConditionalTailRejects nestedOrdinary alternativeOrdinary nestedRejects
        alternativeRejects input condition afterThen
  | alternativeRejected
      {input afterQuestion afterThen afterColon rejected : Remainder}
      {condition thenBranch : Syntax.Expr}
      (questionSpan colonSpan : SourceSpan)
      (questionParsed : ExactTokenParses (.symbol .question) input
        questionSpan afterQuestion)
      (thenParsed : nestedOrdinary afterQuestion thenBranch afterThen)
      (colonParsed : ExactTokenParses (.symbol .colon) afterThen colonSpan
        afterColon)
      (alternativeRejected : alternativeRejects afterColon rejected) :
      ConditionalTailRejects nestedOrdinary alternativeOrdinary nestedRejects
        alternativeRejects input condition rejected
  | laterRejected
      {input afterQuestion afterThen afterColon afterAlternative rejected :
        Remainder}
      {condition thenBranch nextCondition : Syntax.Expr}
      (questionSpan colonSpan : SourceSpan)
      (questionParsed : ExactTokenParses (.symbol .question) input
        questionSpan afterQuestion)
      (thenParsed : nestedOrdinary afterQuestion thenBranch afterThen)
      (colonParsed : ExactTokenParses (.symbol .colon) afterThen colonSpan
        afterColon)
      (alternativeParsed : alternativeOrdinary afterColon nextCondition
        afterAlternative)
      (tailRejected : ConditionalTailRejects nestedOrdinary alternativeOrdinary
        nestedRejects alternativeRejects afterAlternative nextCondition
          rejected) :
      ConditionalTailRejects nestedOrdinary alternativeOrdinary nestedRejects
        alternativeRejects input condition rejected

/-- Exact rejection of one complete conditional layer. -/
inductive ConditionalRejects
    (nestedOrdinary alternativeOrdinary :
      Remainder → Syntax.Expr → Remainder → Prop)
    (nestedRejects alternativeRejects : Remainder → Remainder → Prop) :
    Remainder → Remainder → Prop where
  | conditionRejected {input rejected : Remainder}
      (conditionRejected : alternativeRejects input rejected) :
      ConditionalRejects nestedOrdinary alternativeOrdinary nestedRejects
        alternativeRejects input rejected
  | tailRejected {input afterCondition rejected : Remainder}
      {condition : Syntax.Expr}
      (conditionParsed : alternativeOrdinary input condition afterCondition)
      (tailRejected : ConditionalTailRejects nestedOrdinary alternativeOrdinary
        nestedRejects alternativeRejects afterCondition condition rejected) :
      ConditionalRejects nestedOrdinary alternativeOrdinary nestedRejects
        alternativeRejects input rejected

/-- Ordinary success of the complete operator stack. -/
abbrev ExpressionLayerOrdinaryParses := ExpressionLayerParses

/-- Exact rejection of the complete unary, binary, and conditional stack. -/
def ExpressionLayerRejects
    (nestedOrdinary : Remainder → Syntax.Expr → Remainder → Prop)
    (nestedRejects : Remainder → Remainder → Prop)
    (postfixOrdinary : Remainder → Syntax.Expr → Remainder → Prop)
    (postfixRejects : Remainder → Remainder → Prop) :
    Remainder → Remainder → Prop :=
  let unary := ExpressionUnaryOrdinaryParses postfixOrdinary
  let unaryRejects := ExpressionUnaryRejects postfixRejects
  let multiply := LeftAssociativeOrdinaryParses unary 8
  let multiplyRejects := LeftAssociativeRejects unary unaryRejects 8
  let add := LeftAssociativeOrdinaryParses multiply 7
  let addRejects := LeftAssociativeRejects multiply multiplyRejects 7
  let bitAnd := LeftAssociativeOrdinaryParses add 6
  let bitAndRejects := LeftAssociativeRejects add addRejects 6
  let bitXor := LeftAssociativeOrdinaryParses bitAnd 5
  let bitXorRejects := LeftAssociativeRejects bitAnd bitAndRejects 5
  let bitOr := LeftAssociativeOrdinaryParses bitXor 4
  let bitOrRejects := LeftAssociativeRejects bitXor bitXorRejects 4
  let relational := NonAssociativeOrdinaryParses bitOr 3
  let relationalRejects := NonAssociativeRejects bitOr bitOrRejects 3
  let equality := NonAssociativeOrdinaryParses relational 2
  let equalityRejects := NonAssociativeRejects relational relationalRejects 2
  let logicalAnd := LeftAssociativeOrdinaryParses equality 1
  let logicalAndRejects := LeftAssociativeRejects equality equalityRejects 1
  let logicalOr := LeftAssociativeOrdinaryParses logicalAnd 0
  let logicalOrRejects := LeftAssociativeRejects logicalAnd logicalAndRejects 0
  ConditionalRejects nestedOrdinary logicalOr nestedRejects logicalOrRejects

end Solcore.Syntax.DeclarativeGrammar
