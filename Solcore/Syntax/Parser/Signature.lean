import Solcore.Syntax.Parser.Parameter
import Solcore.Syntax.Parser.Predicate

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Syntactic location controlling whether contract modifiers are valid. -/
inductive FunctionLocation where
  | module
  | contract
  deriving Repr, BEq, DecidableEq

private def requireGenericParameters
    (values : DelimitedList Identifier) : Parser GenericParameters :=
  match values.elements with
  | head :: tail => pure {
      span := values.span
      elements := { head, tail }
    }
  | [] => fun _ => .invariant (.noProgress .topLevel values.span)

/-- Parse a nonempty generic parameter list `<a, b,>`. -/
def genericParameters : Parser GenericParameters := do
  let values ← delimited .less .greater false (identifier .parameter)
    .parameter .topLevel
  requireGenericParameters values

/-- Parse an optional generic parameter list selected by a leading `<`. -/
def optionalGenericParameters : Parser (Option GenericParameters) := do
  let state ← getState
  if isSymbol state .less then
    pure (some (← genericParameters))
  else
    pure none

private def functionParameters : Parser (DelimitedList FunctionParameter) :=
  delimited .leftParen .rightParen true namedParameter
    .parameter .topLevel

private def emitModifierOutsideContract (location : FunctionLocation)
    (keywordValue : HardKeyword) (marker : Option SourceSpan) : Parser Unit :=
  match location, marker with
  | .module, some span => emitDiagnostic {
      span
      kind := .constraintViolation (.modifierOutsideContract keywordValue)
    }
  | _, _ => pure ()

private def functionModifiers
    (location : FunctionLocation) : Parser FunctionModifiers := do
  let state ← getState
  let publicMarker ←
    if isKeyword state .publicKw then
      pure (some (← keyword .publicKw .parameter).span)
    else
      pure none
  let state ← getState
  let payableMarker ←
    if isKeyword state .payableKw then
      pure (some (← keyword .payableKw .parameter).span)
    else
      pure none
  let _ ← emitModifierOutsideContract location .publicKw publicMarker
  let _ ← emitModifierOutsideContract location .payableKw payableMarker
  pure { publicMarker, payableMarker }

private def returnClause : Parser (Option ReturnClause) := do
  let state ← getState
  if isContextual state .returns then
    let marker ← contextual .returns .typeExpr
    let types ← delimited .leftParen .rightParen true typeExpr
      .typeExpr .typeExpr
    pure (some {
      span := SourceSpan.cover marker.span types.span
      types
    })
  else
    pure none

private def signatureEnd (parameters : DelimitedList FunctionParameter)
    (modifiers : FunctionModifiers) (returnsClause : Option ReturnClause)
    (whereClause : Option WhereClause) : SourceSpan :=
  match whereClause with
  | some clause => clause.span
  | none => match returnsClause with
    | some clause => clause.span
    | none => match modifiers.payableMarker with
      | some span => span
      | none => match modifiers.publicMarker with
        | some span => span
        | none => parameters.span

/-- Parse a complete named-function signature, excluding its body. -/
def functionSignature
    (location : FunctionLocation) : Parser FunctionSignature := do
  let functionToken ← keyword .functionKw .topItem
  let name ← identifier .topItem
  let genericParameters ← optionalGenericParameters
  let parameters ← functionParameters
  let modifiers ← functionModifiers location
  let returnsClause ← returnClause
  let whereClause ← whereClause
  pure {
    span := SourceSpan.cover functionToken.span
      (signatureEnd parameters modifiers returnsClause whereClause)
    name
    genericParameters
    parameters
    modifiers
    returnsClause
    whereClause
  }

end Solcore.Syntax.Parser
