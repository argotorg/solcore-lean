import Solcore.Syntax.Parser.Type

set_option autoImplicit false

namespace Solcore.Syntax.Parser

namespace FunctionParameterInternals

def finishTypedParameter (start : SourceSpan)
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

def errorParameter (span : SourceSpan)
    (constraint : ParseConstraint) : Parser FunctionParameter := do
  let _ ← emitDiagnostic {
    span
    kind := .constraintViolation constraint
  }
  pure { span, value := .error }

def namedParameterTail (start : SourceSpan)
    (comptimeMarker : Option SourceSpan) (name : Identifier)
    (errorSpan : SourceSpan) : Parser FunctionParameter := do
  let state ← getState
  if isSymbol state .colon then
    let _ ← symbol .colon .parameter
    let type ← typeExpr
    finishTypedParameter start comptimeMarker name type
  else
    errorParameter errorSpan .namedParameterRequiresType

def ordinaryNamedParameter : Parser FunctionParameter := do
  let name ← identifier .parameter
  if name.value == ContextualKeyword.comptime.spelling then
    let _ ← emitDiagnostic {
      span := name.span
      kind := .constraintViolation .comptimeUsedAsParameterName
    }
  else
    pure ()
  namedParameterTail name.span none name name.span

def comptimeNamedParameter : Parser FunctionParameter := do
  let marker ← contextual .comptime .parameter
  let name ← identifier .parameter
  namedParameterTail marker.span (some marker.span) name
    (SourceSpan.cover marker.span name.span)

def namedParameterCore : Parser FunctionParameter := fun state =>
  if isContextual state .comptime &&
      match state.peekOffsetKind? 1 with
      | some (.identifier _) => true
      | _ => false then
    comptimeNamedParameter state
  else
    ordinaryNamedParameter state

def finishRecoveredParameter (first last : SourceSpan)
    (state : State) : Reply FunctionParameter :=
  let span := SourceSpan.cover first last
  .ok { span, value := .error } (state.emit {
    span
    kind := .recovered .functionParameter
  })

def recoverParameterAux (first last : SourceSpan) :
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

def recoverParameter (state : State) : Reply FunctionParameter :=
  match state.advance? with
  | some (token, next) =>
      recoverParameterAux token.span token.span
        (next.remainingCount + 1) next
  | none => rejectAt state { head := .identifier, tail := [] } .parameter

end FunctionParameterInternals

/-- Named function-like parameter with comma/right-paren recovery. -/
def namedParameter : Parser FunctionParameter := fun state =>
  match FunctionParameterInternals.namedParameterCore state with
  | .ok value next => .ok value next
  | .reject failure failedState =>
      let rewound := { failedState with cursor := state.cursor }
      if rewound.atEnd || isSymbol rewound .comma ||
          isSymbol rewound .rightParen then
        .reject failure rewound
      else
        FunctionParameterInternals.recoverParameter
          (rewound.emit failure.toDiagnostic)
  | .invariant error => .invariant error

namespace LambdaParameterInternals

/-- Retag a named-function parameter while preserving every retained range. -/
def ofFunctionParameter (parameter : FunctionParameter) : LambdaParameter := {
  span := parameter.span
  value := match parameter.value with
    | .typed comptime name type => .typed comptime name type
    | .error => .error
}

def ordinaryLambdaParameterTail (name : Identifier) : Parser LambdaParameter := do
  let state ← getState
  if isSymbol state .colon then
    let parameter ← FunctionParameterInternals.namedParameterTail
      name.span none name name.span
    pure (ofFunctionParameter parameter)
  else
    pure { span := name.span, value := .inferred name }

def ordinaryLambdaParameter : Parser LambdaParameter := do
  let name ← identifier .parameter
  if name.value == ContextualKeyword.comptime.spelling then
    let _ ← emitDiagnostic {
      span := name.span
      kind := .constraintViolation .comptimeUsedAsParameterName
    }
  else
    pure ()
  ordinaryLambdaParameterTail name

def comptimeLambdaParameterTail (marker : Token)
    (name : Identifier) : Parser LambdaParameter := do
  let state ← getState
  if isSymbol state .colon then
    let parameter ← FunctionParameterInternals.namedParameterTail
      marker.span (some marker.span) name
      (SourceSpan.cover marker.span name.span)
    pure (ofFunctionParameter parameter)
  else
    let span := SourceSpan.cover marker.span name.span
    let parameter ← FunctionParameterInternals.errorParameter span
      .comptimeParameterRequiresType
    pure (ofFunctionParameter parameter)

def comptimeLambdaParameter : Parser LambdaParameter := do
  let marker ← contextual .comptime .parameter
  let name ← identifier .parameter
  comptimeLambdaParameterTail marker name

def lambdaParameterCore : Parser LambdaParameter := fun state =>
  if isContextual state .comptime &&
      match state.peekOffsetKind? 1 with
      | some (.identifier _) => true
      | _ => false then
    comptimeLambdaParameter state
  else
    ordinaryLambdaParameter state

def recoverLambdaParameter (state : State) : Reply LambdaParameter :=
  match FunctionParameterInternals.recoverParameter state with
  | .ok recovered next => .ok {
      span := recovered.span
      value := .error
    } next
  | .reject failure next => .reject failure next
  | .invariant error => .invariant error

end LambdaParameterInternals

/-- Lambda parameter, retaining inference only for ordinary unmodified names. -/
def lambdaParameter : Parser LambdaParameter := fun state =>
  match LambdaParameterInternals.lambdaParameterCore state with
  | .ok value next => .ok value next
  | .reject failure failedState =>
      let rewound := { failedState with cursor := state.cursor }
      if rewound.atEnd || isSymbol rewound .comma ||
          isSymbol rewound .rightParen then
        .reject failure rewound
      else
        LambdaParameterInternals.recoverLambdaParameter
          (rewound.emit failure.toDiagnostic)
  | .invariant error => .invariant error

end Solcore.Syntax.Parser
