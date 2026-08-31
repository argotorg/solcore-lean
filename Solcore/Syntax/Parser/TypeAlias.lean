import Solcore.Syntax.Parser.Type

set_option autoImplicit false

namespace Solcore.Syntax.Parser

namespace TypeAliasInternals

def finishRecoveredType (span : SourceSpan)
    (state : State) : Reply TypeExpr :=
  .ok { span, value := .error } (state.emit {
    span
    kind := .recovered .typeAliasValue
  })

def recoverTypeAliasValueAux (first last : SourceSpan) :
    Nat → State → Reply TypeExpr
  | 0, state => .invariant (.fuelExhausted .typeAlias state.currentSpan)
  | fuel + 1, state =>
      if state.atEnd || isSymbol state .semicolon then
        finishRecoveredType (SourceSpan.cover first last) state
      else
        match state.advance? with
        | some (token, next) =>
            recoverTypeAliasValueAux first token.span fuel next
        | none => finishRecoveredType (SourceSpan.cover first last) state

/-- Consume the nonempty malformed RHS prefix before the first semicolon. -/
def recoverTypeAliasValue (state : State) : Reply TypeExpr :=
  if state.atEnd || isSymbol state .semicolon then
    rejectAt state { head := .typeExpr, tail := [] } .typeAlias
  else
    match state.advance? with
    | some (token, next) =>
        recoverTypeAliasValueAux token.span token.span
          (next.remainingCount + 1) next
    | none => rejectAt state { head := .typeExpr, tail := [] } .typeAlias

def parseAliasValue : Parser TypeExpr := fun state =>
  match typeExpr state with
  | .ok value next => .ok value next
  | .reject failure failedState =>
      let rewound := {
        failedState with
        cursor := state.cursor
      }
      if rewound.atEnd || isSymbol rewound .semicolon then
        .reject failure rewound
      else
        recoverTypeAliasValue
          (rewound.emit failure.toDiagnostic)
  | .invariant error => .invariant error

end TypeAliasInternals

/-- Parse one canonical transparent type-alias declaration. -/
def typeAlias : Parser TypeAliasDecl := do
  let typeKeyword ← keyword .typeKw .typeAlias
  let name ← identifier .typeAlias
  let state ← getState
  let parameters ←
    if isSymbol state .leftParen then
      do
        let values ← delimited .leftParen .rightParen true
          (identifier .parameter) .typeAlias .typeAlias
        pure (some values)
    else
      pure none
  let _ ← symbol .equal .typeAlias
  let value ← TypeAliasInternals.parseAliasValue
  let semicolon ← symbol .semicolon .typeAlias
  pure {
    span := SourceSpan.cover typeKeyword.span semicolon.span
    value := {
      name
      parameters
      value
    }
  }

end Solcore.Syntax.Parser
