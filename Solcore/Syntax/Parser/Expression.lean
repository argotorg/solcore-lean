import Solcore.Syntax.Parser.Expression.Atom

set_option autoImplicit false

namespace Solcore.Syntax.Parser

namespace ExpressionInternals

/-- Recognize one canonical prefix unary operator token. -/
def unaryOp? : TokenKind → Option UnaryOp
  | .symbol .bang => some .logicalNot
  | .symbol .tilde => some .bitNot
  | _ => none

end ExpressionInternals

private def binaryOp? : TokenKind → Option BinaryOp
  | .symbol .star => some .multiply
  | .symbol .slash => some .divide
  | .symbol .percent => some .modulo
  | .symbol .plus => some .add
  | .symbol .minus => some .subtract
  | .symbol .amp => some .bitAnd
  | .symbol .caret => some .bitXor
  | .symbol .pipe => some .bitOr
  | .symbol .less => some .less
  | .symbol .greater => some .greater
  | .symbol .lessEqual => some .lessEqual
  | .symbol .greaterEqual => some .greaterEqual
  | .symbol .equalEqual => some .equal
  | .symbol .notEqual => some .notEqual
  | .symbol .logicalAnd => some .logicalAnd
  | .symbol .logicalOr => some .logicalOr
  | _ => none

namespace ExpressionInternals

/-- Consume the maximal prefix sequence of canonical unary operators. -/
def unaryOperators :
    Nat → List (Located UnaryOp) → State → Reply (List (Located UnaryOp))
  | 0, _, state => .invariant (.fuelExhausted .expression state.currentSpan)
  | fuel + 1, operatorsRev, state =>
      match state.peek? with
      | some token =>
          match ExpressionInternals.unaryOp? token.value with
          | some operator => unaryOperators fuel
              ({ span := token.span, value := operator } :: operatorsRev)
              { state with cursor := state.cursor + 1 }
          | none => .ok operatorsRev.reverse state
      | none => .ok operatorsRev.reverse state

end ExpressionInternals

private def expressionUnary (nested : Parser Expr)
    (block : Parser Block) : Parser Expr := fun state =>
  match ExpressionInternals.unaryOperators
      (state.remainingCount + 1) [] state with
  | .ok operators afterOperators =>
      match expressionPostfix nested block afterOperators with
      | .ok base next =>
          let value := operators.foldr (fun operator operand => {
            span := SourceSpan.cover operator.span operand.span
            value := .unary operator operand
          }) base
          .ok value next
      | .reject failure next => .reject failure next
      | .invariant error => .invariant error
  | .reject failure next => .reject failure next
  | .invariant error => .invariant error

private def binaryAtPrecedence? (state : State)
    (precedence : Nat) : Option (Located BinaryOp) :=
  match state.peek? with
  | some token => match binaryOp? token.value with
    | some operator =>
        if operator.precedence == precedence then
          some { span := token.span, value := operator }
        else
          none
    | none => none
  | none => none

private def consumeBinary (_operator : Located BinaryOp) : Parser Unit :=
  modifyState fun state => { state with cursor := state.cursor + 1 }

private def binaryNode (left : Expr) (operator : Located BinaryOp)
    (right : Expr) : Expr := {
  span := SourceSpan.cover left.span right.span
  value := .binary left operator right
}

private def leftAssociativeTail (operand : Parser Expr)
    (precedence : Nat) : Nat → Expr → State → Reply Expr
  | 0, _, state => .invariant (.fuelExhausted .expression state.currentSpan)
  | fuel + 1, left, state =>
      match binaryAtPrecedence? state precedence with
      | none => .ok left state
      | some operator =>
          match consumeBinary operator state with
          | .ok _ afterOperator =>
              match operand afterOperator with
              | .ok right next =>
                  leftAssociativeTail operand precedence fuel
                    (binaryNode left operator right) next
              | .reject failure next => .reject failure next
              | .invariant error => .invariant error
          | .reject failure next => .reject failure next
          | .invariant error => .invariant error

private def leftAssociative (operand : Parser Expr)
    (precedence : Nat) : Parser Expr := fun state =>
  match operand state with
  | .ok left next =>
      leftAssociativeTail operand precedence (next.remainingCount + 1)
        left next
  | .reject failure next => .reject failure next
  | .invariant error => .invariant error

private def nonAssociative (operand : Parser Expr)
    (precedence : Nat) : Parser Expr := fun state =>
  match operand state with
  | .ok left next =>
      match binaryAtPrecedence? next precedence with
      | none => .ok left next
      | some operator =>
          match consumeBinary operator next with
          | .ok _ afterOperator =>
              match operand afterOperator with
              | .ok right final => .ok (binaryNode left operator right) final
              | .reject failure failed => .reject failure failed
              | .invariant error => .invariant error
          | .reject failure failed => .reject failure failed
          | .invariant error => .invariant error
  | .reject failure next => .reject failure next
  | .invariant error => .invariant error

private structure ConditionalHead where
  condition : Expr
  question : SourceSpan
  thenBranch : Expr
  colon : SourceSpan

private def foldConditionalHead (elseBranch : Expr)
    (head : ConditionalHead) : Expr := {
  span := SourceSpan.cover head.condition.span elseBranch.span
  value := .conditional head.condition head.question
    head.thenBranch head.colon elseBranch
}

private def conditionalTail (nested alternative : Parser Expr) :
    Nat → List ConditionalHead → Expr → State → Reply Expr
  | 0, _, _, state => .invariant (.fuelExhausted .expression state.currentSpan)
  | fuel + 1, headsRev, condition, state =>
      if isSymbol state .question then
        match symbol .question .expression state with
        | .ok question afterQuestion =>
            match nested afterQuestion with
            | .ok thenBranch afterThen =>
                match symbol .colon .expression afterThen with
                | .ok colon afterColon =>
                    match alternative afterColon with
                    | .ok nextCondition next =>
                        conditionalTail nested alternative fuel ({
                          condition
                          question := question.span
                          thenBranch
                          colon := colon.span
                        } :: headsRev) nextCondition next
                    | .reject failure failed => .reject failure failed
                    | .invariant error => .invariant error
                | .reject failure failed => .reject failure failed
                | .invariant error => .invariant error
            | .reject failure failed => .reject failure failed
            | .invariant error => .invariant error
        | .reject failure failed => .reject failure failed
        | .invariant error => .invariant error
      else
        .ok (headsRev.foldl foldConditionalHead condition) state

private def conditional (nested alternative : Parser Expr) : Parser Expr :=
    fun state =>
  match alternative state with
  | .ok condition next =>
      conditionalTail nested alternative (next.remainingCount + 1)
        [] condition next
  | .reject failure next => .reject failure next
  | .invariant error => .invariant error

/--
Build one expression recursion layer. Recursive expressions and lambda bodies
are supplied by the later statement/expression knot with strictly less fuel.
-/
def expressionLayer (nested : Parser Expr)
    (block : Parser Block) : Parser Expr :=
  let unary := expressionUnary nested block
  let multiply := leftAssociative unary 8
  let add := leftAssociative multiply 7
  let bitAnd := leftAssociative add 6
  let bitXor := leftAssociative bitAnd 5
  let bitOr := leftAssociative bitXor 4
  let relational := nonAssociative bitOr 3
  let equality := nonAssociative relational 2
  let logicalAnd := leftAssociative equality 1
  let logicalOr := leftAssociative logicalAnd 0
  conditional nested logicalOr

/-- Whether the current token may begin a canonical Core expression. -/
def startsExpression (state : State) : Bool :=
  isCoreLiteral state || isBooleanValue state || isIdentifier state ||
    isSymbol state .dot || isSymbol state .at ||
    isSymbol state .leftParen || isSymbol state .leftBracket ||
    isSymbol state .bang || isSymbol state .tilde ||
    isKeyword state .lamKw

end Solcore.Syntax.Parser
