import Solcore.Syntax.Term
import Solcore.Syntax.Parser.State
import Solcore.Syntax.Foundation
import Solcore.Syntax.Parser.Diagnostic
import Solcore.Syntax.Type
import Solcore.Syntax.Token
import Solcore.Syntax.Parser.Types
import Solcore.Syntax.Source
import Solcore.Syntax.Parser.Tokens
import Solcore.Syntax.Parser.Primitive
import Solcore.Syntax.Literal
import Solcore.Syntax.Operator
import Solcore.Syntax.Unicode.Lowercase
import Solcore.Syntax.Yul
import Solcore.Syntax.Parser.Blocks
import Solcore.Syntax.Parser.Yul

/-!
Parsers for expressions, patterns and statements.

These recurse through one another, so they are defined by fuel. Main declarations:
`coreExpressionWithFuel`, `corePatternWithFuel`, `coreStatementWithFuel`, and the
fuel-free `expression`, `pattern`, `statement` and `block`.
-/

section
-- leanmerge: from Solcore.Syntax.Parser.Front.ExpressionAtom
set_option autoImplicit false

namespace Solcore.Syntax.Parser

namespace ExpressionAtomInternals

/-- Parse an ordinary identifier or Boolean builtin as an expression name. -/
def expressionName : Parser Identifier := fun state =>
  if isBooleanValue state then booleanIdentifier state
  else identifier .expression state

/-- Parse one canonical literal expression leaf. -/
def literalExpression : Parser Expr := do
  let literal ← coreLiteral
  pure {
    span := literal.span
    value := .literal literal
  }

/-- Parse one canonical identifier expression leaf. -/
def identifierExpression : Parser Expr := do
  let name ← expressionName
  pure {
    span := name.span
    value := .identifier name
  }

/-- Parse a proxy expression whose outer range begins at its `@` marker. -/
def proxyExpression : Parser Expr := do
  let marker ← symbol .at .expression
  let type ← typeExpr
  pure {
    span := SourceSpan.cover marker.span type.span
    value := .proxy marker.span type
  }

/-- Parse the optional argument list of a leading-dot constructor. -/
def optionalDotConstructorArguments (nested : Parser Expr) :
    Parser (Option (DelimitedList Expr)) := do
  let state ← getState
  if isSymbol state .leftParen then
    pure (some (← delimitedNoTrailing .leftParen .rightParen true
      nested .expression .expression))
  else
    pure none

/-- Parse a leading-dot constructor expression. -/
def dotConstructor (nested : Parser Expr) : Parser Expr := do
  let dot ← symbol .dot .expression
  let name ← expressionName
  let arguments ← optionalDotConstructorArguments nested
  let endSpan := arguments.map (fun values => values.span) |>.getD name.span
  pure {
    span := SourceSpan.cover dot.span endSpan
    value := .dotConstructor dot.span name arguments
  }

end ExpressionAtomInternals

namespace ExpressionAtomInternals

/-- Close a parenthesized expression after its elements have been accumulated. -/
def closeTuple (opening : Token) (elementsRev : List Expr) :
    Parser Expr := do
  let closing ← symbol .rightParen .expression
  let span := SourceSpan.cover opening.span closing.span
  match elementsRev with
  | [only] => pure { span, value := .group only }
  | _ => pure {
      span
      value := .tuple { span, elements := elementsRev.reverse }
    }

end ExpressionAtomInternals

namespace ExpressionAtomInternals

/-- Continue a parenthesized expression after its first comma. -/
def tupleTail (nested : Parser Expr) (opening : Token) :
    Nat → List Expr → State → Reply Expr
  | 0, _, state => .invariant (.fuelExhausted .expression state.currentSpan)
  | fuel + 1, elementsRev, state =>
      match symbol .comma .expression state with
      | .ok _ afterComma =>
          if isSymbol afterComma .rightParen then
            ExpressionAtomInternals.closeTuple opening elementsRev afterComma
          else
            let before := afterComma.cursor
            match nested afterComma with
            | .ok value next =>
                if next.cursor > before then
                  if isSymbol next .comma then
                    ExpressionAtomInternals.tupleTail nested opening fuel
                      (value :: elementsRev) next
                  else
                    ExpressionAtomInternals.closeTuple opening
                      (value :: elementsRev) next
                else
                  .invariant (.noProgress .expression next.currentSpan)
            | .reject failure next => .reject failure next
            | .invariant error => .invariant error
      | .reject failure next => .reject failure next
      | .invariant error => .invariant error

end ExpressionAtomInternals

namespace ExpressionAtomInternals

/-- Parse a grouped expression or tuple after an opening parenthesis. -/
def parenthesized (nested : Parser Expr) : Parser Expr := fun state =>
  match symbol .leftParen .expression state with
  | .ok opening afterOpening =>
      if isSymbol afterOpening .rightParen then
        ExpressionAtomInternals.closeTuple opening [] afterOpening
      else
        let before := afterOpening.cursor
        match nested afterOpening with
        | .ok first next =>
            if next.cursor ≤ before then
              .invariant (.noProgress .expression next.currentSpan)
            else if isSymbol next .comma then
              ExpressionAtomInternals.tupleTail nested opening
                (next.remainingCount + 1) [first] next
            else
              ExpressionAtomInternals.closeTuple opening [first] next
        | .reject failure next => .reject failure next
        | .invariant error => .invariant error
  | .reject failure next => .reject failure next
  | .invariant error => .invariant error

end ExpressionAtomInternals

namespace ExpressionAtomInternals

/-- Parse a bracketed array literal. -/
def arrayLiteral (nested : Parser Expr) : Parser Expr := do
  let values ← delimitedNoTrailing .leftBracket .rightBracket true nested
    .expression .expression
  pure { span := values.span, value := .array values }

end ExpressionAtomInternals

namespace ExpressionAtomInternals

/-- Parse an optional lambda return type introduced by `->`. -/
def optionalLambdaReturnType : Parser (Option TypeExpr) := do
  let state ← getState
  if isSymbol state .arrow then
    let _ ← symbol .arrow .typeExpr
    pure (some (← typeExpr))
  else
    pure none

end ExpressionAtomInternals

namespace ExpressionAtomInternals

/-- Parse a lambda expression using the supplied recursive block parser. -/
def lambdaExpression (block : Parser Block) : Parser Expr := do
  let marker ← keyword .lamKw .expression
  let parameters ← delimited .leftParen .rightParen true
    lambdaParameter .parameter .expression
  let returnType ← ExpressionAtomInternals.optionalLambdaReturnType
  let body ← block
  pure {
    span := SourceSpan.cover marker.span body.span
    value := .lambda marker.span parameters returnType body
  }

end ExpressionAtomInternals

namespace ExpressionAtomInternals

def expressionAtomCore (nested : Parser Expr)
    (block : Parser Block) : Parser Expr := fun state =>
  if isCoreLiteral state then
    ExpressionAtomInternals.literalExpression state
  else if isBooleanValue state || isIdentifier state then
    ExpressionAtomInternals.identifierExpression state
  else if isSymbol state .dot then
    ExpressionAtomInternals.dotConstructor nested state
  else if isSymbol state .at then
    ExpressionAtomInternals.proxyExpression state
  else if isSymbol state .leftParen then
    ExpressionAtomInternals.parenthesized nested state
  else if isSymbol state .leftBracket then
    ExpressionAtomInternals.arrayLiteral nested state
  else if isKeyword state .lamKw then
    ExpressionAtomInternals.lambdaExpression block state
  else rejectAt state { head := .expression, tail := [] } .expression

def isAtomBoundary (state : State) : Bool :=
  state.atEnd ||
    [.semicolon, .comma, .rightParen, .rightBracket, .rightBrace,
      .question, .colon, .fatArrow, .pipe].any (isSymbol state) ||
    isKeyword state .elseKw

def finishRecoveredAtom (first last : SourceSpan)
    (state : State) : Reply Expr :=
  let span := SourceSpan.cover first last
  .ok { span, value := .error } (state.emit {
    span
    kind := .recovered .expressionAtom
  })

def recoverAtomAux (first last : SourceSpan) :
    Nat → State → Reply Expr
  | 0, state => .invariant (.fuelExhausted .expression state.currentSpan)
  | fuel + 1, state =>
      if isAtomBoundary state then
        finishRecoveredAtom first last state
      else
        match state.advance? with
        | some (token, next) => recoverAtomAux first token.span fuel next
        | none => finishRecoveredAtom first last state

def recoverAtom (state : State) : Reply Expr :=
  match state.advance? with
  | some (token, next) =>
      recoverAtomAux token.span token.span (next.remainingCount + 1) next
  | none => rejectAt state { head := .expression, tail := [] } .expression

end ExpressionAtomInternals

/-- Parse one recoverable expression atom. -/
def expressionAtom (nested : Parser Expr)
    (block : Parser Block) : Parser Expr := fun state =>
  match ExpressionAtomInternals.expressionAtomCore nested block state with
  | .ok value next => .ok value next
  | .reject failure failedState =>
      let rewound := { failedState with cursor := state.cursor }
      if ExpressionAtomInternals.isAtomBoundary rewound then
        .reject failure rewound
      else
        ExpressionAtomInternals.recoverAtom
          (rewound.emit failure.toDiagnostic)
  | .invariant error => .invariant error

namespace ExpressionAtomInternals

/-- Extend one atom through every following index, call, and field suffix. -/
def postfixTail (nested : Parser Expr) (block : Parser Block) :
    Nat → Expr → State → Reply Expr
  | 0, _, state => .invariant (.fuelExhausted .expression state.currentSpan)
  | fuel + 1, base, state =>
      if isSymbol state .leftBracket then
        match symbol .leftBracket .expression state with
        | .ok opening afterOpening =>
            match nested afterOpening with
            | .ok index next =>
                match symbol .rightBracket .expression next with
                | .ok closing afterClosing =>
                    let brackets := SourceSpan.cover opening.span closing.span
                    ExpressionAtomInternals.postfixTail nested block fuel {
                      span := SourceSpan.cover base.span closing.span
                      value := .index base brackets index
                    } afterClosing
                | .reject failure failed => .reject failure failed
                | .invariant error => .invariant error
            | .reject failure failed => .reject failure failed
            | .invariant error => .invariant error
        | .reject failure failed => .reject failure failed
        | .invariant error => .invariant error
      else if isSymbol state .leftParen then
        match delimitedNoTrailing .leftParen .rightParen true nested
            .expression .expression state with
        | .ok arguments next =>
            ExpressionAtomInternals.postfixTail nested block fuel {
              span := SourceSpan.cover base.span arguments.span
              value := .call base arguments
            } next
        | .reject failure failed => .reject failure failed
        | .invariant error => .invariant error
      else if isSymbol state .dot then
        match symbol .dot .expression state with
        | .ok dot afterDot =>
            match identifier .expression afterDot with
            | .ok name next =>
                ExpressionAtomInternals.postfixTail nested block fuel {
                  span := SourceSpan.cover base.span name.span
                  value := .field base dot.span name
                } next
            | .reject failure failed => .reject failure failed
            | .invariant error => .invariant error
        | .reject failure failed => .reject failure failed
        | .invariant error => .invariant error
      else
        .ok base state

end ExpressionAtomInternals

/-- Parse an atom followed by all canonical postfix operations. -/
def expressionPostfix (nested : Parser Expr)
    (block : Parser Block) : Parser Expr := fun state =>
  match expressionAtom nested block state with
  | .ok base next =>
      ExpressionAtomInternals.postfixTail nested block
        (next.remainingCount + 1) base next
  | .reject failure next => .reject failure next
  | .invariant error => .invariant error

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.Front.Expression
set_option autoImplicit false

namespace Solcore.Syntax.Parser

namespace ExpressionInternals

/-- Recognize one canonical prefix unary operator token. -/
def unaryOp? : TokenKind → Option UnaryOp
  | .symbol .bang => some .logicalNot
  | .symbol .tilde => some .bitNot
  | _ => none

end ExpressionInternals

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

/-- Wrap a postfix expression in its source-ordered prefix unary operators. -/
def ExpressionInternals.applyUnaryOperators
    (operators : List (Located UnaryOp)) (base : Expr) : Expr :=
  operators.foldr (fun operator operand => {
    span := SourceSpan.cover operator.span operand.span
    value := .unary operator operand
  }) base

/-- Parse prefix unary operators followed by one complete postfix expression. -/
def ExpressionInternals.expressionUnary (nested : Parser Expr)
    (block : Parser Block) : Parser Expr := fun state =>
  match ExpressionInternals.unaryOperators
      (state.remainingCount + 1) [] state with
  | .ok operators afterOperators =>
      match expressionPostfix nested block afterOperators with
      | .ok base next =>
          .ok (ExpressionInternals.applyUnaryOperators operators base) next
      | .reject failure next => .reject failure next
      | .invariant error => .invariant error
  | .reject failure next => .reject failure next
  | .invariant error => .invariant error

namespace ExpressionInternals

/-- Inspect the current token, and an adjacent second token for `<<` and
`>>`, for a binary operator at one precedence. -/
def binaryAtPrecedence? (state : State)
    (precedence : Nat) : Option (Located BinaryOp) :=
  match BinaryOp.at? state.tokens state.window.endIndex state.cursor with
  | some operator =>
      if operator.value.precedence == precedence then some operator else none
  | none => none

/-- Advance over the tokens of a binary operator already recognized at the
cursor. -/
def consumeBinary (operator : Located BinaryOp) : Parser Unit :=
  modifyState fun state =>
    { state with cursor := state.cursor + operator.value.tokenCount }

/-- Construct the source cover for one binary-expression node. -/
def binaryNode (left : Expr) (operator : Located BinaryOp)
    (right : Expr) : Expr := {
  span := SourceSpan.cover left.span right.span
  value := .binary left operator right
}

end ExpressionInternals

namespace ExpressionInternals

/-- Extend a left-associated expression at one binary precedence. -/
def leftAssociativeTail (operand : Parser Expr)
    (precedence : Nat) : Nat → Expr → State → Reply Expr
  | 0, _, state => .invariant (.fuelExhausted .expression state.currentSpan)
  | fuel + 1, left, state =>
      match ExpressionInternals.binaryAtPrecedence? state precedence with
      | none => .ok left state
      | some operator =>
          match ExpressionInternals.consumeBinary operator state with
          | .ok _ afterOperator =>
              match operand afterOperator with
              | .ok right next =>
                  ExpressionInternals.leftAssociativeTail operand precedence fuel
                    (ExpressionInternals.binaryNode left operator right) next
              | .reject failure next => .reject failure next
              | .invariant error => .invariant error
          | .reject failure next => .reject failure next
          | .invariant error => .invariant error

end ExpressionInternals

namespace ExpressionInternals

/-- Parse one complete left-associative binary precedence layer. -/
def leftAssociative (operand : Parser Expr)
    (precedence : Nat) : Parser Expr := fun state =>
  match operand state with
  | .ok left next =>
      ExpressionInternals.leftAssociativeTail operand precedence
        (next.remainingCount + 1) left next
  | .reject failure next => .reject failure next
  | .invariant error => .invariant error

end ExpressionInternals

namespace ExpressionInternals

/-- Parse one optional binary operator at a non-associative precedence. -/
def nonAssociative (operand : Parser Expr)
    (precedence : Nat) : Parser Expr := fun state =>
  match operand state with
  | .ok left next =>
      match ExpressionInternals.binaryAtPrecedence? next precedence with
      | none => .ok left next
      | some operator =>
          match ExpressionInternals.consumeBinary operator next with
          | .ok _ afterOperator =>
              match operand afterOperator with
              | .ok right final =>
                  .ok (ExpressionInternals.binaryNode left operator right) final
              | .reject failure failed => .reject failure failed
              | .invariant error => .invariant error
          | .reject failure failed => .reject failure failed
          | .invariant error => .invariant error
  | .reject failure next => .reject failure next
  | .invariant error => .invariant error

end ExpressionInternals

namespace ExpressionInternals

/-- One parsed `condition ? then :` prefix awaiting its else branch. -/
structure ConditionalHead where
  condition : Expr
  question : SourceSpan
  thenBranch : Expr
  colon : SourceSpan

/-- Attach an else branch to one previously parsed conditional prefix. -/
def foldConditionalHead (elseBranch : Expr)
    (head : ConditionalHead) : Expr := {
  span := SourceSpan.cover head.condition.span elseBranch.span
  value := .conditional head.condition head.question
    head.thenBranch head.colon elseBranch
}

end ExpressionInternals

namespace ExpressionInternals

/-- Parse repeated conditional prefixes, then rebuild their right nesting. -/
def conditionalTail (nested alternative : Parser Expr) :
    Nat → List ConditionalHead →
      Expr → State → Reply Expr
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
                        ExpressionInternals.conditionalTail nested alternative fuel ({
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

/-- Parse one complete right-associated conditional-expression layer. -/
def conditional (nested alternative : Parser Expr) : Parser Expr :=
    fun state =>
  match alternative state with
  | .ok condition next =>
      ExpressionInternals.conditionalTail nested alternative
        (next.remainingCount + 1)
        [] condition next
  | .reject failure next => .reject failure next
  | .invariant error => .invariant error

end ExpressionInternals

/--
Build one expression recursion layer. Recursive expressions and lambda bodies
are supplied by the later statement/expression knot with strictly less fuel.
-/
def expressionLayer (nested : Parser Expr)
    (block : Parser Block) : Parser Expr :=
  let unary := ExpressionInternals.expressionUnary nested block
  let multiply := ExpressionInternals.leftAssociative unary 9
  let add := ExpressionInternals.leftAssociative multiply 8
  let shift := ExpressionInternals.leftAssociative add 7
  let bitAnd := ExpressionInternals.leftAssociative shift 6
  let bitXor := ExpressionInternals.leftAssociative bitAnd 5
  let bitOr := ExpressionInternals.leftAssociative bitXor 4
  let relational := ExpressionInternals.nonAssociative bitOr 3
  let equality := ExpressionInternals.nonAssociative relational 2
  let logicalAnd := ExpressionInternals.leftAssociative equality 1
  let logicalOr := ExpressionInternals.leftAssociative logicalAnd 0
  ExpressionInternals.conditional nested logicalOr

/-- Whether the current token may begin a canonical Core expression. -/
def startsExpression (state : State) : Bool :=
  isCoreLiteral state || isBooleanValue state || isIdentifier state ||
    isSymbol state .dot || isSymbol state .at ||
    isSymbol state .leftParen || isSymbol state .leftBracket ||
    isSymbol state .bang || isSymbol state .tilde ||
    isKeyword state .lamKw

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.Front.Pattern
set_option autoImplicit false

namespace Solcore.Syntax.Parser

namespace PatternInternals

/-- Parse the canonical wildcard pattern leaf. -/
def wildcardPattern : Parser Pattern := do
  let marker ← symbol .underscore .pattern
  pure {
    span := marker.span
    value := .wildcard marker.span
  }

/-- Parse one canonical literal pattern leaf. -/
def literalPattern : Parser Pattern := do
  let literal ← coreLiteral
  pure {
    span := literal.span
    value := .literal literal
  }

/-- Parse `true` or `false` as a binder-shaped builtin pattern. -/
def booleanBinderPattern : Parser Pattern := do
  let name ← booleanIdentifier
  pure {
    span := name.span
    value := .binder name
  }

end PatternInternals

namespace PatternInternals

/-- Parse an ordinary or Boolean builtin constructor-pattern name. -/
def patternName : Parser Identifier := fun state =>
  if isBooleanValue state then booleanIdentifier state
  else identifier .pattern state

/-- Refine a parsed constructor argument list to its nonempty carrier. -/
def requirePatternArguments (values : DelimitedList Pattern) :
    Parser (NonemptyDelimitedList Pattern) :=
  match values.elements with
  | head :: tail => pure {
      span := values.span
      elements := { head, tail }
    }
  | [] => fun _ => .invariant (.noProgress .pattern values.span)

/-- Parse a required nonempty constructor-pattern argument list. -/
def constructorArguments
    (nested : Parser Pattern) : Parser (NonemptyDelimitedList Pattern) := do
  let values ← delimitedNoTrailing .leftParen .rightParen false nested
    .pattern .pattern
  requirePatternArguments values

/-- Parse constructor arguments when an opening parenthesis is present. -/
def optionalConstructorArguments
    (nested : Parser Pattern) : Parser (Option (NonemptyDelimitedList Pattern)) :=
    fun state =>
  if isSymbol state .leftParen then
    orElse
      (do pure (some (← constructorArguments nested)))
      (pure none) state
  else
    .ok none state

end PatternInternals

namespace PatternInternals

/-- Close a parenthesized pattern after its elements have been accumulated. -/
def closePatternTuple (opening : Token)
    (elementsRev : List Pattern) : Parser Pattern := do
  let closing ← symbol .rightParen .pattern
  let span := SourceSpan.cover opening.span closing.span
  match elementsRev with
  | [only] => pure { span, value := .group only }
  | _ => pure {
      span
      value := .tuple { span, elements := elementsRev.reverse }
    }

end PatternInternals

namespace PatternInternals

/-- Continue a parenthesized tuple after its first comma. -/
def patternTupleTail (nested : Parser Pattern) (opening : Token) :
    Nat → List Pattern → State → Reply Pattern
  | 0, _, state => .invariant (.fuelExhausted .pattern state.currentSpan)
  | fuel + 1, elementsRev, state =>
      match symbol .comma .pattern state with
      | .ok _ afterComma =>
          if isSymbol afterComma .rightParen then
            PatternInternals.closePatternTuple opening elementsRev afterComma
          else
            let before := afterComma.cursor
            match nested afterComma with
            | .ok value next =>
                if next.cursor ≤ before then
                  .invariant (.noProgress .pattern next.currentSpan)
                else if isSymbol next .comma then
                  patternTupleTail nested opening fuel
                    (value :: elementsRev) next
                else
                  PatternInternals.closePatternTuple opening
                    (value :: elementsRev) next
            | .reject failure next => .reject failure next
            | .invariant error => .invariant error
      | .reject failure next => .reject failure next
      | .invariant error => .invariant error

end PatternInternals

namespace PatternInternals

/-- Parse an empty tuple, grouped pattern, or comma-separated tuple. -/
def parenthesizedPattern (nested : Parser Pattern) : Parser Pattern :=
    fun state =>
  match symbol .leftParen .pattern state with
  | .ok opening afterOpening =>
      if isSymbol afterOpening .rightParen then
        PatternInternals.closePatternTuple opening [] afterOpening
      else
        let before := afterOpening.cursor
        match nested afterOpening with
        | .ok first next =>
            if next.cursor ≤ before then
              .invariant (.noProgress .pattern next.currentSpan)
            else if isSymbol next .comma then
              patternTupleTail nested opening
                (next.remainingCount + 1)
                [first] next
            else
              closePatternTuple opening [first] next
        | .reject failure next => .reject failure next
        | .invariant error => .invariant error
  | .reject failure next => .reject failure next
  | .invariant error => .invariant error

end PatternInternals

namespace PatternInternals

/-- Parse a leading-dot constructor pattern. -/
def dotConstructorPattern
    (nested : Parser Pattern) : Parser Pattern := do
  let dot ← symbol .dot .pattern
  let name ← PatternInternals.patternName
  let arguments ← PatternInternals.optionalConstructorArguments nested
  let endSpan := arguments.map (fun values => values.span) |>.getD name.span
  pure {
    span := SourceSpan.cover dot.span endSpan
    value := .constructor (some dot.span) [] name arguments
  }

end PatternInternals

private def startsWithLowercase (name : Identifier) : Bool :=
  match name.value.toList with
  | first :: _ => Unicode.isLowercase first
  | [] => true

namespace PatternInternals

/-- Parse a binder or constructor pattern beginning with a qualified name. -/
def qualifiedPattern (nested : Parser Pattern) : Parser Pattern := do
  let path ← qualifiedName .pattern .pattern
  let arguments ← PatternInternals.optionalConstructorArguments nested
  let components := path.value.components.toList
  match components.reverse with
  | [] => fun _ => .invariant (.noProgress .pattern path.span)
  | name :: qualifiersRev =>
      if qualifiersRev.isEmpty && arguments.isNone &&
          startsWithLowercase name then
        pure { span := path.span, value := .binder name }
      else
        let endSpan := arguments.map (fun values => values.span) |>.getD path.span
        pure {
          span := SourceSpan.cover path.span endSpan
          value := .constructor none qualifiersRev.reverse name arguments
        }

end PatternInternals

namespace PatternInternals

/-- Parse a comptime pattern using the supplied expression parser. -/
def comptimePattern (expression : Parser Expr) : Parser Pattern := fun state =>
  match contextual .comptime .pattern state with
  | .ok marker afterMarker =>
      match expression afterMarker with
      | .ok value next => .ok {
          span := SourceSpan.cover marker.span value.span
          value := .comptime marker.span value
        } next
      | .reject failure next => .reject failure next
      | .invariant error => .invariant error
  | .reject failure next => .reject failure next
  | .invariant error => .invariant error

end PatternInternals

namespace PatternInternals

/-- Dispatch one non-recovering canonical pattern layer. -/
def patternCore (nested : Parser Pattern)
    (expression : Parser Expr) : Parser Pattern := fun state =>
  if isSymbol state .underscore then
    PatternInternals.wildcardPattern state
  else if isCoreLiteral state then
    PatternInternals.literalPattern state
  else if isBooleanValue state then
    PatternInternals.booleanBinderPattern state
  else if isSymbol state .leftParen then
    PatternInternals.parenthesizedPattern nested state
  else if isSymbol state .dot then
    PatternInternals.dotConstructorPattern nested state
  else if isContextual state .comptime then
    PatternInternals.comptimePattern expression state
  else if isIdentifier state then PatternInternals.qualifiedPattern nested state
  else rejectAt state { head := .pattern, tail := [] } .pattern

end PatternInternals

namespace PatternInternals

/-- Whether pattern recovery must stop before the current token. -/
def isPatternBoundary (state : State) : Bool :=
  state.atEnd ||
    [.comma, .rightParen, .fatArrow, .pipe, .rightBrace].any
      (isSymbol state)

/-- Finish recovery with one error pattern spanning the consumed tokens. -/
def finishRecoveredPattern (first last : SourceSpan)
    (state : State) : Reply Pattern :=
  let span := SourceSpan.cover first last
  .ok { span, value := .error } (state.emit {
    span
    kind := .recovered .pattern
  })

/-- Consume malformed pattern tokens until a canonical boundary is reached. -/
def recoverPatternAux (first last : SourceSpan) :
    Nat → State → Reply Pattern
  | 0, state => .invariant (.fuelExhausted .pattern state.currentSpan)
  | fuel + 1, state =>
      if isPatternBoundary state then
        finishRecoveredPattern first last state
      else
        match state.advance? with
        | some (token, next) => recoverPatternAux first token.span fuel next
        | none => finishRecoveredPattern first last state

end PatternInternals

/-- Build one pattern recursion layer with a supplied comptime expression. -/
def patternLayer (nested : Parser Pattern)
    (expression : Parser Expr) : Parser Pattern := fun state =>
  match PatternInternals.patternCore nested expression state with
  | .ok value next => .ok value next
  | .reject failure failedState =>
      let rewound := { failedState with cursor := state.cursor }
      if PatternInternals.isPatternBoundary rewound then
        .reject failure rewound
      else
        match rewound.advance? with
        | some (token, next) =>
            PatternInternals.recoverPatternAux token.span token.span
              (next.remainingCount + 1)
              (next.emit failure.toDiagnostic)
        | none => .reject failure rewound
  | .invariant error => .invariant error

/-- Whether the current token may begin a canonical pattern. -/
def startsPattern (state : State) : Bool :=
  isSymbol state .underscore || isCoreLiteral state ||
    isBooleanValue state || isSymbol state .leftParen ||
    isSymbol state .dot || isContextual state .comptime ||
    isIdentifier state

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.Front.StatementSimple
set_option autoImplicit false

namespace Solcore.Syntax.Parser

namespace StatementSimpleInternals

/-- The value-assignment operator at the cursor, of one token or of two
adjacent tokens (`<<=`, `>>=`). -/
def valueAssignAt? (state : State) : Option (Located ValueAssignOp) :=
  ValueAssignOp.at? state.tokens state.window.endIndex state.cursor

def valueAssignOperator : Parser (Located ValueAssignOp) := fun state =>
  match valueAssignAt? state with
  | some operator => .ok operator
      { state with cursor := state.cursor + operator.value.tokenCount }
  | none => rejectAt state { head := .expression, tail := [] } .statement

end StatementSimpleInternals

namespace StatementSimpleInternals

inductive AssignmentTail where
  | value (operator : Located ValueAssignOp) (right : Expr)
  | bitNot (operator : SourceSpan)

def assignmentTail
    (expression : Parser Expr) : Parser AssignmentTail := fun state =>
  if isSymbol state .tildeEqual then
    (do
      let operator ← symbol .tildeEqual .statement
      pure (AssignmentTail.bitNot operator.span)) state
  else match StatementSimpleInternals.valueAssignAt? state with
    | some _ =>
        (do
          let operator ← StatementSimpleInternals.valueAssignOperator
          let right ← expression
          pure (AssignmentTail.value operator right)) state
    | none => rejectAt state { head := .expression, tail := [] } .statement

def optionalAssignmentTail
    (expression : Parser Expr) : Parser (Option AssignmentTail) := fun state =>
  if isSymbol state .tildeEqual ||
      (StatementSimpleInternals.valueAssignAt? state).isSome then
    (do
      let value ← assignmentTail expression
      pure (some value)) state
  else
    .ok none state

def optionalSemicolon : Parser (Option SourceSpan) := do
  let state ← getState
  if isSymbol state .semicolon then
    pure (some (← symbol .semicolon .statement).span)
  else
    pure none

/-- Parse the optional expression before a required return semicolon. -/
def optionalReturnValue
    (expression : Parser Expr) : Parser (Option Expr) := do
  let state ← getState
  if isSymbol state .semicolon then
    pure none
  else
    pure (some (← expression))

/-- Parse an optional `: type` annotation shared by Core `let` forms. -/
def optionalLetType : Parser (Option TypeExpr) := do
  let state ← getState
  if isSymbol state .colon then
    let _ ← symbol .colon .statement
    pure (some (← typeExpr))
  else
    pure none

/-- Parse an optional `= expression` initializer shared by Core `let` forms. -/
def optionalLetInitializer
    (expression : Parser Expr) : Parser (Option Expr) := do
  let state ← getState
  if isSymbol state .equal then
    let _ ← symbol .equal .statement
    pure (some (← expression))
  else
    pure none

def assignmentEnd : AssignmentTail → SourceSpan
  | .value _ right => right.span
  | .bitNot operator => operator

/-- Select the final source span of an assignment or expression statement. -/
def statementEnd (left : Expr) (tail : Option AssignmentTail)
    (semicolon : Option SourceSpan) : SourceSpan :=
  match semicolon, tail with
  | some marker, _ => marker
  | none, some value => assignmentEnd value
  | none, none => left.span

end StatementSimpleInternals

/-- Parse an expression statement or source-preserving assignment. -/
def assignmentOrExpressionStatement
    (expression : Parser Expr) : Parser Statement := do
  let left ← expression
  let tail ← StatementSimpleInternals.optionalAssignmentTail expression
  let semicolon ← StatementSimpleInternals.optionalSemicolon
  let endSpan := StatementSimpleInternals.statementEnd left tail semicolon
  let span := SourceSpan.cover left.span endSpan
  match tail with
  | some (.value operator right) =>
      if semicolon.isNone then
        let _ ← emitDiagnostic {
          span
          kind := .constraintViolation .assignmentRequiresSemicolon
        }
      pure { span, value := .assignValue left operator right }
  | some (.bitNot operator) =>
      if semicolon.isNone then
        let _ ← emitDiagnostic {
          span
          kind := .constraintViolation .assignmentRequiresSemicolon
        }
      pure { span, value := .assignBitNot left operator }
  | none => pure {
      span
      value := .expression left semicolon.isSome
    }

/-- Parse a semicolon-terminated Core `let` statement. -/
def letStatement (expression : Parser Expr) : Parser Statement := do
  let marker ← keyword .letKw .statement
  let name ← identifier .statement
  let type ← StatementSimpleInternals.optionalLetType
  let initializer ←
    StatementSimpleInternals.optionalLetInitializer expression
  let semicolon ← symbol .semicolon .statement
  pure {
    span := SourceSpan.cover marker.span semicolon.span
    value := .letDecl name type initializer
  }

/-- Parse a semicolon-terminated Core `return` statement. -/
def returnStatement (expression : Parser Expr) : Parser Statement := do
  let marker ← keyword .returnKw .statement
  let value ← StatementSimpleInternals.optionalReturnValue expression
  let semicolon ← symbol .semicolon .statement
  pure {
    span := SourceSpan.cover marker.span semicolon.span
    value := .returnStmt value
  }

namespace StatementSimpleInternals

def forLetEnd (name : Identifier) (type : Option TypeExpr)
    (initializer : Option Expr) : SourceSpan :=
  initializer.map (fun value => value.span) |>.getD
    (type.map (fun value => value.span) |>.getD name.span)

def forLetItem (expression : Parser Expr) : Parser ForItem := do
  let marker ← keyword .letKw .statement
  let name ← identifier .statement
  let type ← StatementSimpleInternals.optionalLetType
  let initializer ←
    StatementSimpleInternals.optionalLetInitializer expression
  let endSpan := forLetEnd name type initializer
  pure {
    span := SourceSpan.cover marker.span endSpan
    value := .letDecl name type initializer
  }

def forAssignmentOrExpression
    (expression : Parser Expr) : Parser ForItem := do
  let left ← expression
  let tail ← StatementSimpleInternals.optionalAssignmentTail expression
  match tail with
  | some (.value operator right) => pure {
      span := SourceSpan.cover left.span right.span
      value := .assignValue left operator right
    }
  | some (.bitNot operator) => pure {
      span := SourceSpan.cover left.span operator
      value := .assignBitNot left operator
    }
  | none => pure { span := left.span, value := .expression left }

end StatementSimpleInternals

/-- Restricted item accepted in one canonical `for` header list. -/
def forItem (expression : Parser Expr) : Parser ForItem := fun state =>
  if isKeyword state .letKw then
    StatementSimpleInternals.forLetItem expression state
  else StatementSimpleInternals.forAssignmentOrExpression expression state

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.Front.StatementMatch
set_option autoImplicit false

namespace Solcore.Syntax.Parser

def MatchInternals.requireScrutinees (values : DelimitedList Expr) :
    Parser (NonemptyDelimitedList Expr) :=
  match values.elements with
  | head :: tail => pure {
      span := values.span
      elements := { head, tail }
    }
  | [] => fun state =>
      rejectAt state { head := .expression, tail := [] } .expression

namespace MatchInternals

def matchCase (statement : Parser Statement)
    (pattern : Parser Pattern) : Parser MatchCase := do
  let marker ← keyword .caseKw .statement
  let pattern ← pattern
  let body ← coreBlock statement .require
  pure {
    span := SourceSpan.cover marker.span body.span
    value := { pattern, body }
  }

def matchCases (statement : Parser Statement)
    (pattern : Parser Pattern) :
    Nat → List MatchCase → State → Reply (List MatchCase)
  | 0, _, state => .invariant (.fuelExhausted .statement state.currentSpan)
  | fuel + 1, casesRev, state =>
      if isKeyword state .caseKw then
        let before := state.cursor
        match matchCase statement pattern state with
        | .ok value next =>
            if next.cursor > before then
              matchCases statement pattern fuel (value :: casesRev) next
            else
              .invariant (.noProgress .statement next.currentSpan)
        | .reject failure next => .reject failure next
        | .invariant error => .invariant error
      else
        .ok casesRev.reverse state

end MatchInternals

def MatchInternals.optionalDefaultBody (statement : Parser Statement) :
    Parser (Option Block) := do
  let state ← getState
  if isKeyword state .defaultKw then
    let _ ← keyword .defaultKw .statement
    pure (some (← coreBlock statement .require))
  else
    pure none

def MatchInternals.patternArity (scrutineeCount : Nat)
    (pattern : Pattern) : Nat :=
  if scrutineeCount > 1 then
    match pattern.value with
    | .tuple elements => elements.elements.length
    | _ => 1
  else
    1

def MatchInternals.validateMatchCaseArity (scrutineeCount : Nat)
    (case : MatchCase) : Parser Unit :=
  let count := MatchInternals.patternArity scrutineeCount case.value.pattern
  if count == scrutineeCount then
    pure ()
  else
    emitDiagnostic {
      span := case.span
      kind := .constraintViolation
        (.matchArityMismatch scrutineeCount count)
    }

def MatchInternals.validateMatchArities (scrutineeCount : Nat) :
    List MatchCase → Parser Unit
  | [] => pure ()
  | case :: rest => do
      let _ ← MatchInternals.validateMatchCaseArity scrutineeCount case
      MatchInternals.validateMatchArities scrutineeCount rest

/-- Parse a canonical multi-scrutinee `match` statement. -/
def matchStatement (statement : Parser Statement)
    (expression : Parser Expr) (pattern : Parser Pattern) : Parser Statement := do
  let marker ← keyword .matchKw .statement
  let scrutineeValues ← delimited .leftParen .rightParen false expression
    .expression .statement
  let scrutinees ← MatchInternals.requireScrutinees scrutineeValues
  let opening ← symbol .leftBrace .statement
  let cases ← fun state =>
    MatchInternals.matchCases statement pattern
      (state.remainingCount + 1) [] state
  let defaultBody ← MatchInternals.optionalDefaultBody statement
  let closing ← symbol .rightBrace .statement
  let armsSpan := SourceSpan.cover opening.span closing.span
  let _ ← MatchInternals.validateMatchArities
    scrutinees.elements.toList.length cases
  if cases.isEmpty && defaultBody.isNone then
    let _ ← emitDiagnostic {
      span := SourceSpan.cover marker.span closing.span
      kind := .constraintViolation .matchRequiresArm
    }
  else
    pure ()
  pure {
    span := SourceSpan.cover marker.span closing.span
    value := .matchWith scrutinees {
      span := armsSpan
      value := { cases, defaultBody }
    }
  }

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.Front.StatementControl
set_option autoImplicit false

namespace Solcore.Syntax.Parser

namespace ControlInternals

def forItemsTail (expression : Parser Expr) (stop : Symbol) :
    Nat → List ForItem → State → Reply (List ForItem)
  | 0, _, state => .invariant (.fuelExhausted .statement state.currentSpan)
  | fuel + 1, itemsRev, state =>
      if isSymbol state .comma then
        match symbol .comma .statement state with
        | .ok _ afterComma =>
            if isSymbol afterComma stop then
              rejectAt afterComma { head := .expression, tail := [] } .statement
            else
              let before := afterComma.cursor
              match forItem expression afterComma with
              | .ok value next =>
                  if next.cursor > before then
                    forItemsTail expression stop fuel (value :: itemsRev) next
                  else
                    .invariant (.noProgress .statement next.currentSpan)
              | .reject failure next => .reject failure next
              | .invariant error => .invariant error
        | .reject failure next => .reject failure next
        | .invariant error => .invariant error
      else
        .ok itemsRev.reverse state

def forItems (expression : Parser Expr)
    (stop : Symbol) : Parser (List ForItem) := fun state =>
  if isSymbol state stop then
    .ok [] state
  else
    match forItem expression state with
    | .ok first next =>
        forItemsTail expression stop (next.remainingCount + 1) [first] next
    | .reject failure next => .reject failure next
    | .invariant error => .invariant error

end ControlInternals

def forStatement (statement : Parser Statement)
    (expression : Parser Expr) : Parser Statement := do
  let marker ← keyword .forKw .statement
  let opening ← symbol .leftParen .statement
  let initializer ← ControlInternals.forItems expression .semicolon
  let _ ← symbol .semicolon .statement
  let condition ← expression
  let _ ← symbol .semicolon .statement
  let post ← ControlInternals.forItems expression .rightParen
  let closing ← symbol .rightParen .statement
  let body ← coreBlock statement .require
  pure {
    span := SourceSpan.cover marker.span body.span
    value := .forLoop (SourceSpan.cover opening.span closing.span)
      initializer condition post body
  }

def whileStatement (statement : Parser Statement)
    (expression : Parser Expr) : Parser Statement := do
  let marker ← contextual .while .statement
  let _ ← symbol .leftParen .statement
  let condition ← expression
  let _ ← symbol .rightParen .statement
  let body ← coreBlock statement .require
  pure {
    span := SourceSpan.cover marker.span body.span
    value := .whileLoop condition body
  }

namespace ControlInternals

/-- Parse the optional `else` keyword and its required braced body. -/
def optionalElseBody (statement : Parser Statement) :
    Parser (Option Block) := do
  let state ← getState
  if isKeyword state .elseKw then
    let _ ← keyword .elseKw .statement
    pure (some (← coreBlock statement .require))
  else
    pure none

end ControlInternals

def ifStatement (statement : Parser Statement)
    (expression : Parser Expr) : Parser Statement := do
  let marker ← keyword .ifKw .statement
  let _ ← symbol .leftParen .statement
  let condition ← expression
  let _ ← symbol .rightParen .statement
  let thenBody ← coreBlock statement .require
  let elseBody ← ControlInternals.optionalElseBody statement
  let endSpan := elseBody.map (fun body => body.span) |>.getD thenBody.span
  pure {
    span := SourceSpan.cover marker.span endSpan
    value := .ifThen condition thenBody elseBody
  }

def assemblyStatement : Parser Statement := do
  let marker ← keyword .assemblyKw .statement
  let body ← yulBody
  pure {
    span := SourceSpan.cover marker.span body.span
    value := .assembly body.body
  }

def blockStatement (statement : Parser Statement) : Parser Statement := do
  let body ← coreBlock statement .require
  pure { span := body.span, value := .block body.value }

def ControlInternals.terminatedControl (keywordValue : HardKeyword)
    (value : StatementValue) : Parser Statement := do
  let marker ← keyword keywordValue .statement
  let semicolon ← symbol .semicolon .statement
  pure {
    span := SourceSpan.cover marker.span semicolon.span
    value
  }

def breakStatement : Parser Statement :=
  ControlInternals.terminatedControl .breakKw .breakStmt

def continueStatement : Parser Statement :=
  ControlInternals.terminatedControl .continueKw .continueStmt

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.Front.Term
/-!
Chumsky's statement `choice` rewinds a rejected recognized branch before trying
the final assignment-or-expression branch.  Keep that behavior explicit: the
fallback supplies the recovered statement and cursor, while the more precise
failure reached by the recognized branch supplies the sole diagnostic.
-/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

namespace TermInternals

def recognizedStatementOrFallback
    (primary fallback : Parser Statement) : Parser Statement := fun state =>
  match primary state with
  | .ok value next => .ok value next
  | .reject failure _ =>
      match fallback state with
      | .ok value next =>
          let reset := { next with diagnosticsRev := state.diagnosticsRev }
          .ok value (reset.emit failure.toDiagnostic)
      | .reject _ _ => .reject failure state
      | .invariant error => .invariant error
  | .invariant error => .invariant error

def statementLayer (nestedStatement : Parser Statement)
    (expression : Parser Expr) (pattern : Parser Pattern) : Parser Statement :=
    fun state =>
  let fallback := assignmentOrExpressionStatement expression
  if isKeyword state .letKw then
    recognizedStatementOrFallback
      (letStatement expression) fallback state
  else if isKeyword state .returnKw then
    recognizedStatementOrFallback
      (returnStatement expression) fallback state
  else if isKeyword state .matchKw then
    recognizedStatementOrFallback
      (matchStatement nestedStatement expression pattern) fallback state
  else if isKeyword state .forKw then
    recognizedStatementOrFallback
      (forStatement nestedStatement expression) fallback state
  else if isContextual state .while then
    recognizedStatementOrFallback
      (whileStatement nestedStatement expression) fallback state
  else if isKeyword state .ifKw then
    recognizedStatementOrFallback
      (ifStatement nestedStatement expression) fallback state
  else if isKeyword state .assemblyKw then
    recognizedStatementOrFallback
      assemblyStatement fallback state
  else if isSymbol state .leftBrace then
    recognizedStatementOrFallback
      (blockStatement nestedStatement) fallback state
  else if isKeyword state .breakKw then
    recognizedStatementOrFallback breakStatement fallback state
  else if isKeyword state .continueKw then
    recognizedStatementOrFallback continueStatement fallback state
  else fallback state

mutual

def coreExpressionWithFuel : Nat → Parser Expr
  | 0 => fun state =>
      .invariant (.fuelExhausted .expression state.currentSpan)
  | fuel + 1 => expressionLayer
      (coreExpressionWithFuel fuel)
      (isolateBlock (coreBlock (coreStatementWithFuel fuel) .require))

def corePatternWithFuel : Nat → Parser Pattern
  | 0 => fun state =>
      .invariant (.fuelExhausted .pattern state.currentSpan)
  | fuel + 1 => patternLayer
      (corePatternWithFuel fuel)
      (coreExpressionWithFuel fuel)

def coreStatementWithFuel : Nat → Parser Statement
  | 0 => fun state =>
      .invariant (.fuelExhausted .statement state.currentSpan)
  | fuel + 1 => statementLayer
      (coreStatementWithFuel fuel)
      (coreExpressionWithFuel fuel)
      (corePatternWithFuel fuel)

end

end TermInternals

/-- Parse one complete canonical Core expression. -/
def expression : Parser Expr := fun state =>
  TermInternals.coreExpressionWithFuel (state.remainingCount + 1) state

/-- Parse one complete canonical Core pattern. -/
def pattern : Parser Pattern := fun state =>
  TermInternals.corePatternWithFuel (state.remainingCount + 1) state

/-- Parse one complete canonical Core statement. -/
def statement : Parser Statement := fun state =>
  TermInternals.coreStatementWithFuel (state.remainingCount + 2) state

/-- Parse one canonical Core block with an explicit root-tail policy. -/
def block (policy : TailExpressionPolicy) : Parser Block := fun state =>
  coreBlock
    (TermInternals.coreStatementWithFuel (state.remainingCount + 1))
    policy state

end Solcore.Syntax.Parser
end
