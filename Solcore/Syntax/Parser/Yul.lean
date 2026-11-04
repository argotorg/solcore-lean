import Solcore.Syntax.Parser.Diagnostic
import Solcore.Syntax.Literal
import Solcore.Syntax.Parser.State
import Solcore.Syntax.Yul
import Solcore.Syntax.Source
import Solcore.Syntax.Foundation
import Solcore.Syntax.Token
import Solcore.Syntax.Parser.Primitive
import Solcore.Syntax.Parser.Tokens

/-!
Parsers for inline Yul.

Main declarations: `yulExpression`, `yulBlock`, `yulBody`, `yulForStatement`,
`yulSwitchStatement`, `yulFunctionStatement`.
-/

section
-- leanmerge: from Solcore.Syntax.Parser.Front.YulExpression
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

namespace YulExpressionInternals

def isBoundary (state : State) : Bool :=
  state.atEnd || [.comma, .rightParen, .rightBrace].any (isSymbol state)

def finishRecovered (first last : SourceSpan)
    (state : State) : Reply YulExpr :=
  let span := SourceSpan.cover first last
  .ok { span, value := .error } (state.emit {
    span
    kind := .recovered .yulExpression
  })

def recoverAux (first last : SourceSpan) :
    Nat → State → Reply YulExpr
  | 0, state => .invariant (.fuelExhausted .yul state.currentSpan)
  | fuel + 1, state =>
      if isBoundary state then
        finishRecovered first last state
      else
        match state.advance? with
        | some (token, next) =>
            recoverAux first token.span fuel next
        | none => finishRecovered first last state

def layer (nested : Parser YulExpr) : Parser YulExpr :=
    fun state =>
  match yulExpressionCore nested state with
  | .ok value next => .ok value next
  | .reject failure failedState =>
      let rewound := { failedState with cursor := state.cursor }
      if isBoundary rewound then
        .reject failure rewound
      else
        match rewound.advance? with
        | some (token, next) =>
            recoverAux token.span token.span
              (next.remainingCount + 1)
              (next.emit failure.toDiagnostic)
        | none => .reject failure rewound
  | .invariant error => .invariant error

def withFuel : Nat → Parser YulExpr
  | 0 => fun state => .invariant (.fuelExhausted .yul state.currentSpan)
  | fuel + 1 => layer (withFuel fuel)

end YulExpressionInternals

/-- Parse one complete recursive inline-Yul expression. -/
def yulExpression : Parser YulExpr := fun state =>
  YulExpressionInternals.withFuel (state.remainingCount + 1) state

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.Front.YulCommon
set_option autoImplicit false

namespace Solcore.Syntax.Parser

structure YulNameSequence where
  span : SourceSpan
  names : NonemptyList YulIdentifier

def finishYulNames (first last : YulIdentifier)
    (tailRev : List YulIdentifier) (state : State) : Reply YulNameSequence :=
  .ok {
    span := SourceSpan.cover first.span last.span
    names := { head := first, tail := tailRev.reverse }
  } state

def yulNamesTail (first : YulIdentifier) :
    Nat → YulIdentifier → List YulIdentifier → State → Reply YulNameSequence
  | 0, _, _, state => .invariant (.fuelExhausted .yul state.currentSpan)
  | fuel + 1, last, tailRev, state =>
      if isSymbol state .comma then
        match symbol .comma .yulStatement state with
        | .ok _ afterComma =>
            match yulName afterComma with
            | .ok name next =>
                yulNamesTail first fuel name (name :: tailRev) next
            | .reject failure next => .reject failure next
            | .invariant error => .invariant error
        | .reject failure next => .reject failure next
        | .invariant error => .invariant error
      else
        finishYulNames first last tailRev state

/-- Parse a nonempty, non-trailing comma-separated Yul name sequence. -/
def yulNames : Parser YulNameSequence := fun state =>
  match yulName state with
  | .ok first next =>
      yulNamesTail first (next.remainingCount + 1) first [] next
  | .reject failure next => .reject failure next
  | .invariant error => .invariant error

structure YulParsedBlock where
  span : SourceSpan
  body : List YulStmt

def closeYulBlock (opening : Token)
    (bodyRev : List YulStmt) : Parser YulParsedBlock := fun state =>
  match symbol .rightBrace .yulStatement state with
  | .ok closing next => .ok {
      span := SourceSpan.cover opening.span closing.span
      body := bodyRev.reverse
    } next
  | .reject failure next => .reject failure next
  | .invariant error => .invariant error

def yulBlockItems (statement : Parser YulStmt)
    (opening : Token) : Nat → List YulStmt → State → Reply YulParsedBlock
  | 0, _, state => .invariant (.fuelExhausted .yul state.currentSpan)
  | fuel + 1, bodyRev, state =>
      if isSymbol state .rightBrace then
        closeYulBlock opening bodyRev state
      else if state.atEnd then
        match symbol .rightBrace .yulStatement state with
        | .ok _ _ => .invariant (.noProgress .yul state.currentSpan)
        | .reject failure next => .reject failure next
        | .invariant error => .invariant error
      else
        let before := state.cursor
        match statement state with
        | .ok value next =>
            if next.cursor > before then
              yulBlockItems statement opening fuel (value :: bodyRev) next
            else
              .invariant (.noProgress .yul next.currentSpan)
        | .reject failure next => .reject failure next
        | .invariant error => .invariant error

/-- Parse braces and a progress-checked list of inline-Yul statements. -/
def yulBlock (statement : Parser YulStmt) : Parser YulParsedBlock := fun state =>
  match symbol .leftBrace .yulStatement state with
  | .ok opening next =>
      yulBlockItems statement opening (next.remainingCount + 1) [] next
  | .reject failure next => .reject failure next
  | .invariant error => .invariant error

/-- Empty/trailing parameter list used by inline-Yul function definitions. -/
def yulParameters : Parser (DelimitedList YulIdentifier) :=
  delimited .leftParen .rightParen true yulName .yulStatement .yul

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.Front.YulControl
set_option autoImplicit false

namespace Solcore.Syntax.Parser

def yulIfStatement (statement : Parser YulStmt) : Parser YulStmt := do
  let marker ← keyword .ifKw .yulStatement
  let condition ← yulExpression
  let body ← yulBlock statement
  pure {
    span := SourceSpan.cover marker.span body.span
    value := .ifThen condition body.body
  }

def yulForStatement (statement : Parser YulStmt) : Parser YulStmt := do
  let marker ← keyword .forKw .yulStatement
  let initializer ← yulBlock statement
  let condition ← yulExpression
  let post ← yulBlock statement
  let body ← yulBlock statement
  pure {
    span := SourceSpan.cover marker.span body.span
    value := .forLoop initializer.body condition post.body body.body
  }

namespace YulControl

/-- Parse one `case` arm of a Yul switch. -/
def caseArm (statement : Parser YulStmt) : Parser YulCase := do
  let marker ← keyword .caseKw .yulStatement
  let literal ← yulLiteral
  let body ← yulBlock statement
  pure {
    span := SourceSpan.cover marker.span body.span
    value := .arm literal body.body
  }

def caseList (statement : Parser YulStmt) :
    Nat → List YulCase → State → Reply (List YulCase)
  | 0, _, state => .invariant (.fuelExhausted .yul state.currentSpan)
  | fuel + 1, casesRev, state =>
      if isKeyword state .caseKw then
        let before := state.cursor
        match caseArm statement state with
        | .ok value next =>
            if next.cursor > before then
              caseList statement fuel (value :: casesRev) next
            else
              .invariant (.noProgress .yul next.currentSpan)
        | .reject failure next => .reject failure next
        | .invariant error => .invariant error
      else
        .ok casesRev.reverse state

/-- Parse the optional `default` arm of a Yul switch. -/
def optionalDefault (statement : Parser YulStmt) :
    Parser (Option YulParsedBlock) := do
  let state ← getState
  if isKeyword state .defaultKw then
    let _ ← keyword .defaultKw .yulStatement
    pure (some (← yulBlock statement))
  else
    pure none

end YulControl

def yulSwitchStatement (statement : Parser YulStmt) : Parser YulStmt := do
  let marker ← keyword .switchKw .yulStatement
  let scrutinee ← yulExpression
  let cases ← fun current =>
    YulControl.caseList statement (current.remainingCount + 1) [] current
  let defaultBody ← YulControl.optionalDefault statement
  let endSpan := match defaultBody with
    | some body => body.span
    | none => match cases.reverse with
      | last :: _ => last.span
      | [] => scrutinee.span
  let span := SourceSpan.cover marker.span endSpan
  match cases with
  | head :: tail => pure {
      span
      value := .switch scrutinee { head, tail }
        (defaultBody.map (fun body => body.body))
    }
  | [] =>
      let _ ← emitDiagnostic {
        span
        kind := .constraintViolation .yulSwitchRequiresCase
      }
      pure { span, value := .error }

namespace YulControl

/-- Parse the arrow and nonempty return-name sequence of a Yul function. -/
def returnClause : Parser YulReturnClause := do
  let arrow ← symbol .arrow .yulStatement
  let names ← yulNames
  pure {
    span := SourceSpan.cover arrow.span names.span
    value := { arrow := arrow.span, names := names.names }
  }

/-- Parse the optional return-name clause of a Yul function definition. -/
def returns : Parser (Option YulReturnClause) := do
  let state ← getState
  if isSymbol state .arrow then
    pure (some (← returnClause))
  else
    pure none

end YulControl

def yulFunctionStatement (statement : Parser YulStmt) : Parser YulStmt := do
  let marker ← keyword .functionKw .yulStatement
  let name ← yulName
  let parameters ← yulParameters
  let returns ← YulControl.returns
  let body ← yulBlock statement
  pure {
    span := SourceSpan.cover marker.span body.span
    value := .functionDef name parameters returns body.body
  }

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.Front.YulStatement
set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Lift a parsed Yul block into statement position. -/
def yulBlockStatement (statement : Parser YulStmt) : Parser YulStmt := do
  let block ← yulBlock statement
  pure { span := block.span, value := .block block.body }

/-- Parse an optional initializer following a Yul name sequence. -/
def yulLetInitializer : Parser (Option YulExpr) := do
  let state ← getState
  if isSymbol state .colonEqual then
    let _ ← symbol .colonEqual .yulStatement
    pure (some (← yulExpression))
  else
    pure none

/-- Parse a Yul `let` declaration. -/
def yulLetStatement : Parser YulStmt := do
  let marker ← keyword .letKw .yulStatement
  let names ← yulNames
  let initializer ← yulLetInitializer
  let endSpan := initializer.map (fun value => value.span) |>.getD names.span
  pure {
    span := SourceSpan.cover marker.span endSpan
    value := .letDecl names.names initializer
  }

/-- Parse a nonempty Yul assignment. -/
def yulAssignment : Parser YulStmt := do
  let names ← yulNames
  let _ ← symbol .colonEqual .yulStatement
  let value ← yulExpression
  pure {
    span := SourceSpan.cover names.span value.span
    value := .assign names.names value
  }

/-- Lift a Yul expression into statement position. -/
def yulExpressionStatement : Parser YulStmt := do
  let expression ← yulExpression
  pure { span := expression.span, value := .expression expression }

/-- Parse source-level `return(...)` as the corresponding Yul call statement. -/
def yulReturnBuiltin : Parser YulStmt := do
  let marker ← keyword .returnKw .yulStatement
  let arguments ← delimited .leftParen .rightParen true yulExpression
    .yulExpression .yul
  let span := SourceSpan.cover marker.span arguments.span
  let callee : YulIdentifier := { span := marker.span, value := "return" }
  let expression : YulExpr := {
    span
    value := .call callee arguments
  }
  pure { span, value := .expression expression }

/-- Parse one keyword-only Yul control statement. -/
def yulControlToken (value : HardKeyword)
    (result : YulStmtValue) : Parser YulStmt := do
  let marker ← keyword value .yulStatement
  pure { span := marker.span, value := result }

/-!
Chumsky's ordered statement choice rewinds a rejected recognized branch before
trying its final expression branch.  The expression parser may recover to a
`YulExpr.error`; retain that AST and its cursor, but replace its speculative
diagnostics with the more precise failure reached by the recognized branch.
-/
def recognizedYulStatementOrFallback
    (primary fallback : Parser YulStmt) : Parser YulStmt := fun state =>
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

/-- Select one non-terminating Yul statement form. -/
def yulStatementCore (nested : Parser YulStmt) : Parser YulStmt :=
    fun state =>
  let fallback := yulExpressionStatement
  if isSymbol state .leftBrace then
    recognizedYulStatementOrFallback
      (yulBlockStatement nested) fallback state
  else if isKeyword state .letKw then
    recognizedYulStatementOrFallback yulLetStatement fallback state
  else if isKeyword state .ifKw then
    recognizedYulStatementOrFallback
      (yulIfStatement nested) fallback state
  else if isKeyword state .forKw then
    recognizedYulStatementOrFallback
      (yulForStatement nested) fallback state
  else if isKeyword state .switchKw then
    recognizedYulStatementOrFallback
      (yulSwitchStatement nested) fallback state
  else if isKeyword state .functionKw then
    recognizedYulStatementOrFallback
      (yulFunctionStatement nested) fallback state
  else if isKeyword state .returnKw then
    recognizedYulStatementOrFallback yulReturnBuiltin fallback state
  else if isKeyword state .leaveKw then
    recognizedYulStatementOrFallback
      (yulControlToken .leaveKw .leave) fallback state
  else if isKeyword state .breakKw then
    recognizedYulStatementOrFallback
      (yulControlToken .breakKw .break) fallback state
  else if isKeyword state .continueKw then
    recognizedYulStatementOrFallback
      (yulControlToken .continueKw .continue) fallback state
  else if startsYulName state then
    orElse yulAssignment fallback state
  else
    fallback state

/-- Consume an optional semicolon without changing the parsed statement. -/
def optionalYulSemicolon (value : YulStmt) : Parser YulStmt := do
  let state ← getState
  if isSymbol state .semicolon then
    let _ ← symbol .semicolon .yulStatement
    pure value
  else
    pure value

/-- Parse one statement and its optional trailing semicolon. -/
def yulStatementTerminated
    (nested : Parser YulStmt) : Parser YulStmt := do
  optionalYulSemicolon (← yulStatementCore nested)

/-- Finish statement recovery with one diagnosed error node. -/
def finishRecoveredYulStatement (first last : SourceSpan)
    (state : State) : Reply YulStmt :=
  let span := SourceSpan.cover first last
  .ok { span, value := .error } (state.emit {
    span
    kind := .recovered .yulStatement
  })

/-- Scan to a Yul statement boundary using explicit fuel. -/
def recoverYulStatementAux (first last : SourceSpan) :
    Nat → State → Reply YulStmt
  | 0, state => .invariant (.fuelExhausted .yul state.currentSpan)
  | fuel + 1, state =>
      if state.atEnd || isSymbol state .rightBrace then
        finishRecoveredYulStatement first last state
      else
        match state.advance? with
        | some (token, next) =>
            recoverYulStatementAux first token.span fuel next
        | none => finishRecoveredYulStatement first last state

/-- Parse one recovering statement layer around a recursive statement parser. -/
def yulStatementLayer (nested : Parser YulStmt) : Parser YulStmt :=
    fun state =>
  match yulStatementTerminated nested state with
  | .ok value next => .ok value next
  | .reject failure failedState =>
      let rewound := { failedState with cursor := state.cursor }
      if rewound.atEnd || isSymbol rewound .rightBrace then
        .reject failure rewound
      else
        match rewound.advance? with
        | some (token, next) =>
            recoverYulStatementAux token.span token.span
              (next.remainingCount + 1)
              (next.emit failure.toDiagnostic)
        | none => .reject failure rewound
  | .invariant error => .invariant error

/-- Iterate recovering statement layers with explicit recursion fuel. -/
def yulStatementWithFuel : Nat → Parser YulStmt
  | 0 => fun state => .invariant (.fuelExhausted .yul state.currentSpan)
  | fuel + 1 => yulStatementLayer (yulStatementWithFuel fuel)

/-- Parse one complete inline-Yul statement. -/
def yulStatement : Parser YulStmt := fun state =>
  yulStatementWithFuel (state.remainingCount + 1) state

/-- Parse a complete braced inline-Yul statement sequence. -/
def yulBody : Parser YulParsedBlock := yulBlock yulStatement

end Solcore.Syntax.Parser
end
