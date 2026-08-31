import Solcore

/-! External compile consumers for canonical parser-state invariants. -/

set_option autoImplicit false

namespace Tests

open Solcore.Syntax
open Solcore.Syntax.Parser

example (file : SourceFile) (lexed : LexedFile)
    (valid : lexed.ValidFor file) :
    (State.initial file lexed).ValidFor :=
  State.initial_validFor valid

example (state : State) (valid : state.ValidFor)
    (token : Token) (found : state.peek? = some token) :
    token.span.ValidFor state.file :=
  valid.peek?_span_validFor found

example (state : State) (valid : state.ValidFor) :
    state.currentSpan.ValidFor state.file :=
  valid.currentSpan_validFor

example (state next : State) (valid : state.ValidFor)
    (token : Token) (advanced : state.advance? = some (token, next)) :
    next.ValidFor :=
  valid.advance?_validFor advanced

example (state : State) (valid : state.ValidFor)
    (diagnostic : ParseDiagnostic)
    (diagnosticValid : diagnostic.span.ValidFor state.file) :
    (state.emit diagnostic).ValidFor :=
  valid.emit_validFor diagnostic diagnosticValid

example (state : State) (valid : state.ValidFor)
    (diagnostic : ParseDiagnostic) (member : diagnostic ∈ state.diagnostics) :
    diagnostic.span.ValidFor state.file :=
  valid.diagnostics_span_validFor member

example (file : SourceFile) (failure : Failure)
    (valid : failure.span.ValidFor file) :
    failure.toDiagnostic.span.ValidFor file :=
  failure.toDiagnostic_span_validFor valid

end Tests
