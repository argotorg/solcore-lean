import Solcore.Syntax.Parser.Type

set_option autoImplicit false

namespace Solcore.Syntax.Parser

private def finishTypedParameter (start : SourceSpan)
    (comptimeMarker : Option SourceSpan) (name : Identifier)
    (type : TypeExpr) : Parser FunctionParameter := do
  match type.value with
  | .comptime .. =>
      let _ ← emitDiagnostic {
        span := type.span
        kind := .constraintViolation .comptimeTypeInParameter
      }
  | _ => pure ()
  pure {
    span := SourceSpan.cover start type.span
    value := .typed comptimeMarker name type
  }

private def errorParameter (span : SourceSpan)
    (constraint : ParseConstraint) : Parser FunctionParameter := do
  let _ ← emitDiagnostic {
    span
    kind := .constraintViolation constraint
  }
  pure { span, value := .error }

private def ordinaryNamedParameter : Parser FunctionParameter := do
  let name ← identifier .parameter
  if name.value == ContextualKeyword.comptime.spelling then
    let _ ← emitDiagnostic {
      span := name.span
      kind := .constraintViolation .comptimeUsedAsParameterName
    }
  else
    pure ()
  let state ← getState
  if isSymbol state .colon then
    let _ ← symbol .colon .parameter
    let type ← typeExpr
    finishTypedParameter name.span none name type
  else
    errorParameter name.span .namedParameterRequiresType

private def comptimeNamedParameter : Parser FunctionParameter := do
  let marker ← contextual .comptime .parameter
  let name ← identifier .parameter
  let state ← getState
  if isSymbol state .colon then
    let _ ← symbol .colon .parameter
    let type ← typeExpr
    finishTypedParameter marker.span (some marker.span) name type
  else
    errorParameter (SourceSpan.cover marker.span name.span)
      .namedParameterRequiresType

private def namedParameterCore : Parser FunctionParameter := fun state =>
  if isContextual state .comptime &&
      match state.peekOffsetKind? 1 with
      | some (.identifier _) => true
      | _ => false then
    comptimeNamedParameter state
  else
    ordinaryNamedParameter state

private def finishRecoveredParameter (first last : SourceSpan)
    (state : State) : Reply FunctionParameter :=
  let span := SourceSpan.cover first last
  .ok { span, value := .error } (state.emit {
    span
    kind := .recovered .functionParameter
  })

private def recoverParameterAux (first last : SourceSpan) :
    Nat → State → Reply FunctionParameter
  | 0, state => .invariant (.fuelExhausted .topLevel state.currentSpan)
  | fuel + 1, state =>
      if state.atEnd || isSymbol state .comma ||
          isSymbol state .rightParen then
        finishRecoveredParameter first last state
      else
        match state.advance? with
        | some (token, next) =>
            recoverParameterAux first token.span fuel next
        | none => finishRecoveredParameter first last state

private def recoverParameter (state : State) : Reply FunctionParameter :=
  match state.advance? with
  | some (token, next) =>
      recoverParameterAux token.span token.span
        (next.remainingCount + 1) next
  | none => rejectAt state { head := .identifier, tail := [] } .parameter

/-- Named function-like parameter with comma/right-paren recovery. -/
def namedParameter : Parser FunctionParameter := fun state =>
  match namedParameterCore state with
  | .ok value next => .ok value next
  | .reject failure failedState =>
      let rewound := { failedState with cursor := state.cursor }
      if rewound.atEnd || isSymbol rewound .comma ||
          isSymbol rewound .rightParen then
        .reject failure rewound
      else
        recoverParameter (rewound.emit failure.toDiagnostic)
  | .invariant error => .invariant error

end Solcore.Syntax.Parser
