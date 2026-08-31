import Solcore.Syntax.Parser.Delimited

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Parse one identifier admitted by the independent inline-Yul grammar. -/
def yulName : Parser YulIdentifier := fun state =>
  match state.peek? with
  | some { span, value := .yulIdentifier text } =>
      .ok { span, value := text } { state with cursor := state.cursor + 1 }
  | some { span, value := .symbol .underscore } =>
      .ok { span, value := "_" } { state with cursor := state.cursor + 1 }
  | some { span, value := .keyword .fallbackKw } =>
      .ok { span, value := "fallback" }
        { state with cursor := state.cursor + 1 }
  | some { value := .identifier _, .. } => identifier .yulExpression state
  | _ => rejectAt state { head := .yulIdentifier, tail := [] } .yulExpression

def startsYulName (state : State) : Bool :=
  match state.peekKind? with
  | some (.identifier _)
  | some (.yulIdentifier _)
  | some (.symbol .underscore)
  | some (.keyword .fallbackKw) => true
  | _ => false

/-- Parse one literal admitted by inline Yul, including Boolean literals. -/
def yulLiteral : Parser YulLiteral := fun state =>
  match state.peek? with
  | some { span, value := .decimalLiteral spelling } =>
      .ok { span, value := .decimal spelling }
        { state with cursor := state.cursor + 1 }
  | some { span, value := .hexadecimalLiteral spelling } =>
      .ok { span, value := .hexadecimal spelling }
        { state with cursor := state.cursor + 1 }
  | some { span, value := .stringLiteral spelling } =>
      .ok { span, value := .string spelling }
        { state with cursor := state.cursor + 1 }
  | some { span, value := .keyword .trueKw } =>
      .ok { span, value := .boolean true }
        { state with cursor := state.cursor + 1 }
  | some { span, value := .keyword .falseKw } =>
      .ok { span, value := .boolean false }
        { state with cursor := state.cursor + 1 }
  | _ => rejectAt state { head := .yulLiteral, tail := [] } .yulExpression

def startsYulLiteral (state : State) : Bool :=
  match state.peekKind? with
  | some (.decimalLiteral _)
  | some (.hexadecimalLiteral _)
  | some (.stringLiteral _)
  | some (.keyword .trueKw)
  | some (.keyword .falseKw) => true
  | _ => false

/-- Parse optional arguments using the supplied parser for recursive expressions. -/
def optionalYulCallArguments (nested : Parser YulExpr) :
    Parser (Option (DelimitedList YulExpr)) := fun state =>
  if isSymbol state .leftParen then
    orElse
      (do pure (some (← delimited .leftParen .rightParen true nested
        .yulExpression .yul)))
      (pure none) state
  else
    .ok none state

/-- Consume forbidden source-level meta syntax as a diagnosed error expression. -/
def rejectedMeta : Parser YulExpr := fun state =>
  match state.peek? with
  | some token@{ value := .yulMetaBacktick _, .. }
  | some token@{ value := .yulMetaInterpolation _, .. } =>
      .ok { span := token.span, value := .error }
        (({ state with cursor := state.cursor + 1 }).emit {
          span := token.span
          kind := .constraintViolation .yulMetaInSource
        })
  | _ => rejectAt state { head := .yulIdentifier, tail := [] } .yulExpression

/-- Parse one non-recovering Yul expression layer with a recursive parser. -/
def yulExpressionCore (nested : Parser YulExpr) : Parser YulExpr :=
    fun state =>
  if startsYulLiteral state then
    match yulLiteral state with
    | .ok literal next => .ok {
        span := literal.span
        value := .literal literal
      } next
    | .reject failure next => .reject failure next
    | .invariant error => .invariant error
  else if startsYulName state then
    match yulName state with
    | .ok name afterName =>
        match optionalYulCallArguments nested afterName with
        | .ok (some arguments) next => .ok {
            span := SourceSpan.cover name.span arguments.span
            value := .call name arguments
          } next
        | .ok none next => .ok { span := name.span, value := .identifier name } next
        | .reject failure next => .reject failure next
        | .invariant error => .invariant error
    | .reject failure next => .reject failure next
    | .invariant error => .invariant error
  else match state.peekKind? with
    | some (.yulMetaBacktick _)
    | some (.yulMetaInterpolation _) => rejectedMeta state
    | _ => rejectAt state {
        head := .yulIdentifier
        tail := [.yulLiteral]
      } .yulExpression

private def isYulExpressionBoundary (state : State) : Bool :=
  state.atEnd || [.comma, .rightParen, .rightBrace].any (isSymbol state)

private def finishRecoveredYulExpression (first last : SourceSpan)
    (state : State) : Reply YulExpr :=
  let span := SourceSpan.cover first last
  .ok { span, value := .error } (state.emit {
    span
    kind := .recovered .yulExpression
  })

private def recoverYulExpressionAux (first last : SourceSpan) :
    Nat → State → Reply YulExpr
  | 0, state => .invariant (.fuelExhausted .yul state.currentSpan)
  | fuel + 1, state =>
      if isYulExpressionBoundary state then
        finishRecoveredYulExpression first last state
      else
        match state.advance? with
        | some (token, next) =>
            recoverYulExpressionAux first token.span fuel next
        | none => finishRecoveredYulExpression first last state

private def yulExpressionLayer (nested : Parser YulExpr) : Parser YulExpr :=
    fun state =>
  match yulExpressionCore nested state with
  | .ok value next => .ok value next
  | .reject failure failedState =>
      let rewound := { failedState with cursor := state.cursor }
      if isYulExpressionBoundary rewound then
        .reject failure rewound
      else
        match rewound.advance? with
        | some (token, next) =>
            recoverYulExpressionAux token.span token.span
              (next.remainingCount + 1)
              (next.emit failure.toDiagnostic)
        | none => .reject failure rewound
  | .invariant error => .invariant error

private def yulExpressionWithFuel : Nat → Parser YulExpr
  | 0 => fun state => .invariant (.fuelExhausted .yul state.currentSpan)
  | fuel + 1 => yulExpressionLayer (yulExpressionWithFuel fuel)

/-- Parse one complete recursive inline-Yul expression. -/
def yulExpression : Parser YulExpr := fun state =>
  yulExpressionWithFuel (state.remainingCount + 1) state

end Solcore.Syntax.Parser
