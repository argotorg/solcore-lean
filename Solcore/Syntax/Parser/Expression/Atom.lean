import Solcore.Syntax.Parser.Literal
import Solcore.Syntax.Parser.Signature

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

private def expressionAtomCore (nested : Parser Expr)
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

private def isAtomBoundary (state : State) : Bool :=
  state.atEnd ||
    [.semicolon, .comma, .rightParen, .rightBracket, .rightBrace,
      .question, .colon, .fatArrow, .pipe].any (isSymbol state) ||
    isKeyword state .elseKw

private def finishRecoveredAtom (first last : SourceSpan)
    (state : State) : Reply Expr :=
  let span := SourceSpan.cover first last
  .ok { span, value := .error } (state.emit {
    span
    kind := .recovered .expressionAtom
  })

private def recoverAtomAux (first last : SourceSpan) :
    Nat → State → Reply Expr
  | 0, state => .invariant (.fuelExhausted .expression state.currentSpan)
  | fuel + 1, state =>
      if isAtomBoundary state then
        finishRecoveredAtom first last state
      else
        match state.advance? with
        | some (token, next) => recoverAtomAux first token.span fuel next
        | none => finishRecoveredAtom first last state

private def recoverAtom (state : State) : Reply Expr :=
  match state.advance? with
  | some (token, next) =>
      recoverAtomAux token.span token.span (next.remainingCount + 1) next
  | none => rejectAt state { head := .expression, tail := [] } .expression

/-- Parse one recoverable expression atom. -/
def expressionAtom (nested : Parser Expr)
    (block : Parser Block) : Parser Expr := fun state =>
  match expressionAtomCore nested block state with
  | .ok value next => .ok value next
  | .reject failure failedState =>
      let rewound := { failedState with cursor := state.cursor }
      if isAtomBoundary rewound then
        .reject failure rewound
      else
        recoverAtom (rewound.emit failure.toDiagnostic)
  | .invariant error => .invariant error

private def postfixTail (nested : Parser Expr) (block : Parser Block) :
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
                    postfixTail nested block fuel {
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
            postfixTail nested block fuel {
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
                postfixTail nested block fuel {
                  span := SourceSpan.cover base.span name.span
                  value := .field base dot.span name
                } next
            | .reject failure failed => .reject failure failed
            | .invariant error => .invariant error
        | .reject failure failed => .reject failure failed
        | .invariant error => .invariant error
      else
        .ok base state

/-- Parse an atom followed by all canonical postfix operations. -/
def expressionPostfix (nested : Parser Expr)
    (block : Parser Block) : Parser Expr := fun state =>
  match expressionAtom nested block state with
  | .ok base next =>
      postfixTail nested block (next.remainingCount + 1) base next
  | .reject failure next => .reject failure next
  | .invariant error => .invariant error

end Solcore.Syntax.Parser
