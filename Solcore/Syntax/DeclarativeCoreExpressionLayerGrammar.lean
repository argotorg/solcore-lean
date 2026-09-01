import Solcore.Syntax.DeclarativeGrammar

/-!
Parser-independent grammar combinators for canonical Core expression layers.

The judgments in this module are parameterized by their recursive operand
grammar.  They expose maximal unary and binary consumption, exact precedence
and associativity, and right-associated conditional construction without
mentioning parser fuel.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Exact token spelling of one prefix unary operator. -/
def UnaryOperatorParses (input : Remainder)
    (operator : Located UnaryOp) (output : Remainder) : Prop :=
  ExactTokenParses (.symbol operator.value.symbol) input operator.span output

/-- Neither canonical prefix unary operator occurs at this cursor. -/
def UnaryOperatorAbsentAt (input : Remainder) : Prop :=
  TokenKindAbsentAt input.tokens input.endIndex input.cursor (.symbol .bang) ∧
    TokenKindAbsentAt input.tokens input.endIndex input.cursor (.symbol .tilde)

/-- Maximal source-order sequence of prefix unary operators. -/
inductive UnaryOperatorsParses :
    Remainder → List (Located UnaryOp) → Remainder → Prop where
  | done {input : Remainder} (absent : UnaryOperatorAbsentAt input) :
      UnaryOperatorsParses input [] input
  | next {input afterOperator output : Remainder}
      {operator : Located UnaryOp} {operators : List (Located UnaryOp)}
      (operatorParsed : UnaryOperatorParses input operator afterOperator)
      (tail : UnaryOperatorsParses afterOperator operators output) :
      UnaryOperatorsParses input (operator :: operators) output

/-- Pure source-preserving construction used by the unary layer. -/
def applyUnaryOperators
    (operators : List (Located UnaryOp)) (base : Expr) : Expr :=
  operators.foldr (fun operator operand => {
    span := SourceSpan.cover operator.span operand.span
    value := .unary operator operand
  }) base

/-- Prefix-unary grammar over an already complete postfix grammar. -/
def ExpressionUnaryParses
    (postfixParses : Remainder → Expr → Remainder → Prop)
    (input : Remainder) (expression : Expr) (output : Remainder) : Prop :=
  ∃ operators afterOperators base,
    UnaryOperatorsParses input operators afterOperators ∧
    postfixParses afterOperators base output ∧
    expression = applyUnaryOperators operators base

/-- Exact binary-operator token at one precedence. -/
def BinaryOperatorAtPrecedenceParses (precedence : Nat)
    (input : Remainder) (operator : Located BinaryOp)
    (output : Remainder) : Prop :=
  operator.value.precedence = precedence ∧
    ExactTokenParses (.symbol operator.value.symbol) input operator.span output

/-- No binary operator of one precedence occurs at the current cursor. -/
def BinaryOperatorAtPrecedenceAbsentAt
    (precedence : Nat) (input : Remainder) : Prop :=
  ¬ ∃ (span : SourceSpan) (operator : BinaryOp),
    operator.precedence = precedence ∧
    TokenAt input.tokens input.endIndex input.cursor {
      span
      value := .symbol operator.symbol
    }

/-- Pure source-preserving construction used by every binary layer. -/
def binaryNode (left : Expr) (operator : Located BinaryOp)
    (right : Expr) : Expr := {
  span := SourceSpan.cover left.span right.span
  value := .binary left operator right
}

/-- Maximal left-associated tail at one binary precedence. -/
inductive LeftAssociativeTailParses
    (operandParses : Remainder → Expr → Remainder → Prop)
    (precedence : Nat) :
    Remainder → Expr → Expr → Remainder → Prop where
  | done {input : Remainder} {left : Expr}
      (absent : BinaryOperatorAtPrecedenceAbsentAt precedence input) :
      LeftAssociativeTailParses operandParses precedence input left left input
  | next {input afterOperator afterRight output : Remainder}
      {left right expression : Expr} {operator : Located BinaryOp}
      (operatorParsed : BinaryOperatorAtPrecedenceParses precedence input
        operator afterOperator)
      (rightParsed : operandParses afterOperator right afterRight)
      (tail : LeftAssociativeTailParses operandParses precedence afterRight
        (binaryNode left operator right) expression output) :
      LeftAssociativeTailParses operandParses precedence input left expression
        output

/-- One complete maximal left-associated precedence layer. -/
def LeftAssociativeParses
    (operandParses : Remainder → Expr → Remainder → Prop)
    (precedence : Nat) (input : Remainder)
    (expression : Expr) (output : Remainder) : Prop :=
  ∃ left afterLeft,
    operandParses input left afterLeft ∧
    LeftAssociativeTailParses operandParses precedence afterLeft left
      expression output

/-- One complete non-associative binary precedence layer. -/
inductive NonAssociativeParses
    (operandParses : Remainder → Expr → Remainder → Prop)
    (precedence : Nat) : Remainder → Expr → Remainder → Prop where
  | plain {input output : Remainder} {left : Expr}
      (leftParsed : operandParses input left output)
      (absent : BinaryOperatorAtPrecedenceAbsentAt precedence output) :
      NonAssociativeParses operandParses precedence input left output
  | binary {input afterLeft afterOperator output : Remainder}
      {left right : Expr} {operator : Located BinaryOp}
      (leftParsed : operandParses input left afterLeft)
      (operatorParsed : BinaryOperatorAtPrecedenceParses precedence afterLeft
        operator afterOperator)
      (rightParsed : operandParses afterOperator right output) :
      NonAssociativeParses operandParses precedence input
        (binaryNode left operator right) output

/-- Maximal conditional suffix, constructed with right associativity. -/
inductive ConditionalTailParses
    (nestedParses alternativeParses :
      Remainder → Expr → Remainder → Prop) :
    Remainder → Expr → Expr → Remainder → Prop where
  | done {input : Remainder} {condition : Expr}
      (absent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.symbol .question)) :
      ConditionalTailParses nestedParses alternativeParses input condition
        condition input
  | next {input afterQuestion afterThen afterColon afterAlternative output :
        Remainder}
      {condition thenBranch nextCondition elseBranch : Expr}
      (questionSpan colonSpan : SourceSpan)
      (questionToken : ExactTokenParses (.symbol .question) input questionSpan
        afterQuestion)
      (thenParsed : nestedParses afterQuestion thenBranch afterThen)
      (colonToken : ExactTokenParses (.symbol .colon) afterThen colonSpan
        afterColon)
      (alternativeParsed : alternativeParses afterColon nextCondition
        afterAlternative)
      (tail : ConditionalTailParses nestedParses alternativeParses
        afterAlternative nextCondition elseBranch output) :
      ConditionalTailParses nestedParses alternativeParses input condition {
        span := SourceSpan.cover condition.span elseBranch.span
        value := .conditional condition questionSpan thenBranch colonSpan
          elseBranch
      } output

/-- One complete maximal right-associated conditional layer. -/
def ConditionalParses
    (nestedParses alternativeParses :
      Remainder → Expr → Remainder → Prop)
    (input : Remainder) (expression : Expr) (output : Remainder) : Prop :=
  ∃ condition afterCondition,
    alternativeParses input condition afterCondition ∧
    ConditionalTailParses nestedParses alternativeParses afterCondition
      condition expression output

/--
Exact composition of every Core expression precedence layer over a supplied
postfix grammar.  Recursive conditional branches use `nestedParses`.
-/
def ExpressionLayerParses
    (nestedParses postfixParses : Remainder → Expr → Remainder → Prop) :
    Remainder → Expr → Remainder → Prop :=
  let unary := ExpressionUnaryParses postfixParses
  let multiply := LeftAssociativeParses unary 8
  let add := LeftAssociativeParses multiply 7
  let bitAnd := LeftAssociativeParses add 6
  let bitXor := LeftAssociativeParses bitAnd 5
  let bitOr := LeftAssociativeParses bitXor 4
  let relational := NonAssociativeParses bitOr 3
  let equality := NonAssociativeParses relational 2
  let logicalAnd := LeftAssociativeParses equality 1
  let logicalOr := LeftAssociativeParses logicalAnd 0
  ConditionalParses nestedParses logicalOr

end Solcore.Syntax.DeclarativeGrammar
