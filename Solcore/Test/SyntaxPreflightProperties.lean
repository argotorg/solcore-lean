import Solcore

/-! External compile consumers for canonical parser preflight laws. -/

set_option autoImplicit false

namespace Tests

open Solcore.Syntax
open Solcore.Syntax.Parser

example (file : SourceFile) (lexed : LexedFile)
    (accepted : validateLexed file lexed = .ok ()) :
    lexed.source = file.id :=
  (validateLexed_ok_validFor file lexed accepted).source_eq

example (file : SourceFile) (lexed : LexedFile)
    (accepted : validateLexed file lexed = .ok ())
    (token : Token) (member : token ∈ lexed.tokens) :
    token.span.ValidFor file :=
  (validateLexed_ok_validFor file lexed accepted).token_span member

example (file : SourceFile) (lexed : LexedFile)
    (accepted : validateLexed file lexed = .ok ())
    (comment : Comment) (member : comment ∈ lexed.comments) :
    comment.span.ValidFor file :=
  (validateLexed_ok_validFor file lexed accepted).comment_span member

example (file : SourceFile) (lexed : LexedFile)
    (accepted : validateLexed file lexed = .ok ())
    (diagnostic : LexicalDiagnostic)
    (member : diagnostic ∈ lexed.diagnostics) :
    diagnostic.span.ValidFor file :=
  (validateLexed_ok_validFor file lexed accepted).diagnostic_span member

example (file : SourceFile) (lexed : LexedFile)
    (accepted : validateLexed file lexed = .ok ()) :
    SpanSequence.ValidFor file (fun token : Token => token.span)
      0 lexed.tokens :=
  (validateLexed_ok_validFor file lexed accepted).tokens

example (file : SourceFile) (lexed : LexedFile)
    (accepted : validateLexed file lexed = .ok ())
    (token : Token) (rest : List Token)
    (startsWith : lexed.tokens = token :: rest) :
    token.span.ValidFor file ∧
      0 ≤ token.span.startByte ∧
      token.span.startByte < token.span.endByte ∧
      SpanSequence.ValidFor file (fun item : Token => item.span)
        token.span.endByte rest := by
  have valid := (validateLexed_ok_validFor file lexed accepted).tokens
  rw [startsWith] at valid
  exact valid

example (file : SourceFile) (lexed : LexedFile) (output : ParseOutput)
    (parsed : parseLexed file lexed = .ok output) :
    lexed.ValidFor file :=
  parseLexed_ok_input_validFor file lexed output parsed

end Tests
