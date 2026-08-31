import Solcore.Syntax.Parser.State

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Build one uncommitted rejection at the current cursor. -/
def rejectAt {α : Type} (state : State)
    (expected : NonemptyList ParseExpectation)
    (context : ParseContext) : Reply α :=
  .reject {
    span := state.currentSpan
    found := state.peekKind?
    expected
    context
  } state

/-- Consume the current token exactly when `accepts` recognizes it. -/
def acceptToken (expected : ParseExpectation) (context : ParseContext)
    (accepts : TokenKind → Bool) : Parser Token := fun state =>
  match state.peek? with
  | some token =>
      if accepts token.value then
        .ok token { state with cursor := state.cursor + 1 }
      else
        rejectAt state { head := expected, tail := [] } context
  | none => rejectAt state { head := expected, tail := [] } context

def keyword (value : HardKeyword) (context : ParseContext) : Parser Token :=
  acceptToken (.keyword value) context (· == .keyword value)

def symbol (value : Symbol) (context : ParseContext) : Parser Token :=
  acceptToken (.symbol value) context (· == .symbol value)

/-- Contextual words remain identifier tokens in every other production. -/
def contextual (value : ContextualKeyword)
    (context : ParseContext) : Parser Token :=
  acceptToken (.contextual value) context (·.isContextual value)

def isKeyword (state : State) (value : HardKeyword) : Bool :=
  state.peekKind? == some (.keyword value)

def isSymbol (state : State) (value : Symbol) : Bool :=
  state.peekKind? == some (.symbol value)

def isContextual (state : State) (value : ContextualKeyword) : Bool :=
  match state.peekKind? with
  | some kind => kind.isContextual value
  | none => false

def isIdentifier (state : State) : Bool :=
  match state.peekKind? with
  | some (.identifier _) => true
  | _ => false

/-- Accept an ordinary identifier without applying grammar-specific checks. -/
def rawIdentifier (context : ParseContext) : Parser Identifier := fun state =>
  match state.peek? with
  | some { span, value := .identifier text } =>
      .ok { span, value := text } { state with cursor := state.cursor + 1 }
  | _ => rejectAt state { head := .identifier, tail := [] } context

/-- Canonical identifier parser, retaining the Rust parser's hyphen error. -/
def identifier (context : ParseContext) : Parser Identifier := fun state =>
  match rawIdentifier context state with
  | .ok name next =>
      if name.value.toList.contains '-' then
        .ok name (next.emit {
          span := name.span
          kind := .invalidIdentifierHyphen name.value
        })
      else
        .ok name next
  | .reject failure next => .reject failure next
  | .invariant error => .invariant error

def yulIdentifier (context : ParseContext) : Parser Identifier := fun state =>
  match state.peek? with
  | some { span, value := .yulIdentifier text } =>
      .ok { span, value := text } { state with cursor := state.cursor + 1 }
  | _ => rejectAt state { head := .yulIdentifier, tail := [] } context

/-- Commit an unhandled rejection as an ordinary source diagnostic. -/
def emitFailure (failure : Failure) (state : State) : State :=
  state.emit failure.toDiagnostic

end Solcore.Syntax.Parser
