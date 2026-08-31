import Solcore.Syntax.Parser.Function

set_option autoImplicit false

namespace Solcore.Syntax.Parser

private def entryParameters : Parser (DelimitedList FunctionParameter) :=
  delimited .leftParen .rightParen true namedParameter
    .parameter .topLevel

private def implicitPublicModifiers
    (declaration : HardKeyword) : Parser (Option SourceSpan) := do
  let state ← getState
  let publicMarker ←
    if isKeyword state .publicKw then
      pure (some (← keyword .publicKw .contractMember).span)
    else
      pure none
  match publicMarker with
  | some span =>
      let _ ← emitDiagnostic {
        span
        kind := .constraintViolation (.implicitPublicModifier declaration)
      }
  | none => pure ()
  let state ← getState
  if isKeyword state .payableKw then
    pure (some (← keyword .payableKw .contractMember).span)
  else
    pure none

/-- Parse a contract constructor with an explicitly non-tail body. -/
def constructorDecl : Parser ConstructorDecl := do
  let marker ← keyword .constructorKw .contractMember
  let parameters ← entryParameters
  let payableMarker ← implicitPublicModifiers .constructorKw
  let body ← isolateBlock (block .require)
  pure {
    span := SourceSpan.cover marker.span body.span
    value := { parameters, payableMarker, body }
  }

/-- Parse a fallback entry point while retaining invalid parameters. -/
def fallbackDecl : Parser FallbackDecl := do
  let marker ← keyword .fallbackKw .contractMember
  let parameters ← entryParameters
  if parameters.elements.isEmpty then
    pure ()
  else
    let _ ← emitDiagnostic {
      span := parameters.span
      kind := .constraintViolation .fallbackRequiresNoParameters
    }
  let payableMarker ← implicitPublicModifiers .fallbackKw
  let body ← isolateBlock (block .require)
  pure {
    span := SourceSpan.cover marker.span body.span
    value := { parameters, payableMarker, body }
  }

end Solcore.Syntax.Parser
