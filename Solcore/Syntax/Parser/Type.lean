import Solcore.Syntax.Parser.Delimited
import Solcore.Syntax.Parser.Name

set_option autoImplicit false

namespace Solcore.Syntax.Parser

private def requireNonempty {α : Type} (parsed : DelimitedList α)
    (phase : ParserPhase) : Parser (NonemptyDelimitedList α) :=
  match parsed.elements with
  | head :: tail => pure {
      span := parsed.span
      elements := { head, tail }
    }
  | [] => fun _ => .invariant (.noProgress phase parsed.span)

private def parseNamedType (nested : Parser TypeExpr) : Parser TypeExpr := do
  let name ← qualifiedName .typeExpr .typeExpr
  let state ← getState
  let arguments ←
    if isSymbol state .less then
      do
        let parsed ← delimited .less .greater false nested
          .typeExpr .typeExpr
        let nonempty ← requireNonempty parsed .typeExpr
        pure (some nonempty)
    else
      pure none
  let span := match arguments with
    | some values => SourceSpan.cover name.span values.span
    | none => name.span
  let ty : TypeExpr := {
    span
    value := .named name arguments
  }
  if name.value.components.tail.isEmpty &&
      name.value.components.head.value == "mapping" then
    emitDiagnostic {
      span
      kind := .constraintViolation .mappingRequiresCanonicalForm
    }
  else
    pure ()
  pure ty

private def parseMappingType (nested : Parser TypeExpr) : Parser TypeExpr := do
  let mapping ← contextual .mapping .typeExpr
  let opening ← symbol .leftParen .typeExpr
  let key ← nested
  let _ ← symbol .fatArrow .typeExpr
  let value ← nested
  let closing ← symbol .rightParen .typeExpr
  pure {
    span := SourceSpan.cover mapping.span closing.span
    value := .mapping mapping.span
      (SourceSpan.cover opening.span closing.span) key value
  }

private def parseComptimeType (nested : Parser TypeExpr) : Parser TypeExpr := do
  let comptime ← contextual .comptime .typeExpr
  let opening ← symbol .less .typeExpr
  let inner ← nested
  let closing ← symbol .greater .typeExpr
  pure {
    span := SourceSpan.cover comptime.span closing.span
    value := .comptime comptime.span
      (SourceSpan.cover opening.span closing.span) inner
  }

private def parseProxyType (nested : Parser TypeExpr) : Parser TypeExpr := do
  let marker ← symbol .at .typeExpr
  let inner ← nested
  pure {
    span := SourceSpan.cover marker.span inner.span
    value := .proxy marker.span inner
  }

private def parseTupleType (nested : Parser TypeExpr) : Parser TypeExpr := do
  let tuple ← delimited .leftParen .rightParen true nested
    .typeExpr .typeExpr
  pure {
    span := tuple.span
    value := .tuple tuple.elements
  }

private def parseFunctionType (nested : Parser TypeExpr) : Parser TypeExpr := do
  let functionKeyword ← keyword .functionKw .typeExpr
  let parameters ← delimited .leftParen .rightParen true nested
    .typeExpr .typeExpr
  let state ← getState
  let returns ←
    if isContextual state .returns then
      do
        let _ ← contextual .returns .typeExpr
        let values ← delimited .leftParen .rightParen true nested
          .typeExpr .typeExpr
        pure (some values)
    else
      pure none
  let endSpan := match returns with
    | some values => values.span
    | none => parameters.span
  pure {
    span := SourceSpan.cover functionKeyword.span endSpan
    value := .function functionKeyword.span parameters returns
  }

private def hasFollowingSymbol (state : State) (value : Symbol) : Bool :=
  state.peekOffsetKind? 1 == some (.symbol value)

/-- Recursive Core type parser, parameterized by remaining nesting depth. -/
def typeExprWithFuel : Nat → Parser TypeExpr
  | 0 => fun state =>
      .invariant (.fuelExhausted .typeExpr state.currentSpan)
  | fuel + 1 => fun state =>
      let nested := typeExprWithFuel fuel
      if isKeyword state .functionKw then
        parseFunctionType nested state
      else if isContextual state .comptime &&
          hasFollowingSymbol state .less then
        parseComptimeType nested state
      else if isContextual state .mapping &&
          hasFollowingSymbol state .leftParen then
        parseMappingType nested state
      else if isSymbol state .at then
        parseProxyType nested state
      else if isSymbol state .leftParen then
        parseTupleType nested state
      else if isIdentifier state then
        parseNamedType nested state
      else
        rejectAt state { head := .typeExpr, tail := [] } .typeExpr

/-- Parse one complete canonical Core type expression. -/
def typeExpr : Parser TypeExpr := fun state =>
  typeExprWithFuel (state.remainingCount + 1) state

end Solcore.Syntax.Parser
