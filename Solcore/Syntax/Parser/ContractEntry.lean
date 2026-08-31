import Solcore.Syntax.Parser.Function

set_option autoImplicit false

namespace Solcore.Syntax.Parser

namespace ContractEntryInternals

def entryParameters : Parser (DelimitedList FunctionParameter) :=
  delimited .leftParen .rightParen true namedParameter
    .parameter .topLevel

/-- Parse one optional contract-entry modifier marker. -/
def optionalModifier (modifier : HardKeyword) : Parser (Option SourceSpan) := do
  let state ← getState
  if isKeyword state modifier then
    pure (some (← keyword modifier .contractMember).span)
  else
    pure none

def implicitPublicModifiers
    (declaration : HardKeyword) : Parser (Option SourceSpan) := do
  let publicMarker ← optionalModifier .publicKw
  match publicMarker with
  | some span =>
      let _ ← emitDiagnostic {
        span
        kind := .constraintViolation (.implicitPublicModifier declaration)
      }
  | none => pure ()
  optionalModifier .payableKw

end ContractEntryInternals

/-- Parse a contract constructor with an explicitly non-tail body. -/
def constructorDecl : Parser ConstructorDecl := do
  let marker ← keyword .constructorKw .contractMember
  let parameters ← ContractEntryInternals.entryParameters
  let payableMarker ←
    ContractEntryInternals.implicitPublicModifiers .constructorKw
  let body ← isolateBlock (block .require)
  pure {
    span := SourceSpan.cover marker.span body.span
    value := { parameters, payableMarker, body }
  }

/-- Parse a fallback entry point while retaining invalid parameters. -/
def fallbackDecl : Parser FallbackDecl := do
  let marker ← keyword .fallbackKw .contractMember
  let parameters ← ContractEntryInternals.entryParameters
  if parameters.elements.isEmpty then
    pure ()
  else
    let _ ← emitDiagnostic {
      span := parameters.span
      kind := .constraintViolation .fallbackRequiresNoParameters
    }
  let payableMarker ←
    ContractEntryInternals.implicitPublicModifiers .fallbackKw
  let body ← isolateBlock (block .require)
  pure {
    span := SourceSpan.cover marker.span body.span
    value := { parameters, payableMarker, body }
  }

end Solcore.Syntax.Parser
