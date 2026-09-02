import Solcore

/-! External compile consumers for canonical parser preflight laws. -/

set_option autoImplicit false

namespace Tests

open Solcore.Syntax
open Solcore.Syntax.DeclarativeGrammar
open Solcore.Syntax.Parser

example := @IndexedSpan
example := @LexedValidationFailure
example := @OrderedSpanAccepted
example := @OrderedSpanValidationScans
example := @SpanValidationScans
example := @TokenSpanValidationScans
example := @CommentSpanValidationScans
example := @LexicalDiagnosticSpanValidationScans
example := @LexedFileValidationOutcome
example := @LexedFileValidationAccepts
example := @LexedFileValidationRejects
example := @OrderedSpanValidationScans.result_unique
example := @OrderedSpanValidationScans.exists_result
example := @OrderedSpanValidationScans.none_iff_spanSequenceValidFor
example := @SpanValidationScans.result_unique
example := @SpanValidationScans.exists_result
example := @SpanValidationScans.none_iff_forall_validFor
example := @LexedFileValidationOutcome.exists_result
example := @LexedFileValidationOutcome.result_unique
example := @lexedFileValidationOutcome_total
example := @LexedFileValidationRejects.disjointAccepts
example := @LexedFileValidationRejects.failure_unique
example := @lexedFileValidationAccepts_iff_validFor
example := @lexedValidationInvariantError
example := @validateLexed_eq_result_of_outcome
example := @validateLexed_reflects_outcome
example := @validateLexed_ok_iff_validationAccepts
example := @validateLexed_error_iff_validationRejects
example := @productionParseLexed_error_iff_validateLexed_error
example := @productionParseLexed_error_iff_validationRejects
example := @productionParseLexed_certifiedOutcome

example (file : SourceFile) (lexed : LexedFile)
    (result : Lexer.lex file = .ok lexed) :
    validateLexed file lexed = .ok () :=
  lex_ok_validateLexed file lexed result

example (file : SourceFile) (lexed : LexedFile)
    (lexing : Lexer.lex file = .ok lexed)
    (error : ParserInvariantError)
    (validation : validateLexed file lexed = .error error) : False :=
  lex_ok_validateLexed_error_impossible file lexed lexing error validation

example (file : SourceFile) (lexed : LexedFile) :
    validateLexed file lexed = .ok () ↔ lexed.ValidFor file :=
  validateLexed_ok_iff_validFor file lexed

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

example (file : SourceFile) (output : ParseOutput)
    (parsed : parse file = .ok output) :
    ∃ lexed,
      Lexer.lex file = .ok lexed ∧
      parseLexed file lexed = .ok output ∧
      lexed.ValidFor file ∧
      output.tokens = lexed.tokens ∧
      output.lexicalDiagnostics = lexed.diagnostics ∧
      output.parsed.comments = lexed.comments :=
  parse_ok_valid_lexed_provenance file output parsed

example (file : SourceFile) (output : ParseOutput)
    (parsed : parse file = .ok output)
    (token : Token) (member : token ∈ output.tokens) :
    token.span.ValidFor file :=
  parse_ok_tokens_validFor file output parsed token member

example (file : SourceFile) (output : ParseOutput)
    (parsed : parse file = .ok output)
    (comment : Comment) (member : comment ∈ output.parsed.comments) :
    comment.span.ValidFor file :=
  parse_ok_comments_validFor file output parsed comment member

example (file : SourceFile) (output : ParseOutput)
    (parsed : parse file = .ok output)
    (diagnostic : LexicalDiagnostic)
    (member : diagnostic ∈ output.lexicalDiagnostics) :
    diagnostic.span.ValidFor file :=
  parse_ok_lexicalDiagnostics_validFor file output parsed diagnostic member

example (file : SourceFile) (output : ParseOutput)
    (parsed : parse file = .ok output) :
    SpanSequence.ValidFor file (fun token : Token => token.span)
      0 output.tokens :=
  parse_ok_tokens_sequence_validFor file output parsed

example (file : SourceFile) (output : ParseOutput)
    (parsed : parse file = .ok output) :
    SpanSequence.ValidFor file (fun comment : Comment => comment.span)
      0 output.parsed.comments :=
  parse_ok_comments_sequence_validFor file output parsed

example (file : SourceFile) (tokens : List Token)
    (valid : SpanSequence.ValidFor file (fun token : Token => token.span)
      0 tokens) (token : Token) (member : token ∈ tokens) :
    0 ≤ token.span.startByte ∧
      token.span.startByte < token.span.endByte :=
  ⟨valid.previousEnd_le_start member, valid.span_nonempty member⟩

example (file : SourceFile) (output : ParseOutput)
    (parsed : parse file = .ok output) :
    output.tokens.Pairwise fun left right =>
      left.span.endByte ≤ right.span.startByte :=
  parse_ok_tokens_pairwise_nonoverlap file output parsed

example (file : SourceFile) (output : ParseOutput)
    (parsed : parse file = .ok output) :
    output.parsed.comments.Pairwise fun left right =>
      left.span.endByte ≤ right.span.startByte :=
  parse_ok_comments_pairwise_nonoverlap file output parsed

end Tests
