import Solcore.Syntax.Parser.PublicPragmaSequenceOutputProperties

/-! Complete public pragma-sequence consumers, including empty token carriers.
No example assumes an executable item or source-file reply. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserPublicPragmaSequenceOutputProperties

open Solcore.Syntax
open Solcore.Syntax.Parser
open Solcore.Syntax.DeclarativeGrammar

variable {file : SourceFile} {lexed : LexedFile} {declarations : List PragmaDecl}
  {after : Remainder} {trace kept : List ParseDiagnostic}
  (accepted : LexedFileValidationAccepts file lexed)
  (clears : NestingClears lexed.tokens)
  (parsed : PragmaSequenceTraceParses (sourceFileRootRemainder lexed.tokens)
    declarations after trace)

example : parseLexed file lexed = .ok {
    parsed := {
      source := file.id
      span := SourceSpan.fullFile file
      items := (declarations.map FileInternals.wrapPragma).map
        (Trivia.attachTopItemComments file lexed.comments)
      comments := lexed.comments
    }
    tokens := lexed.tokens
    lexicalDiagnostics := lexed.diagnostics
    parseDiagnostics := trace
  } :=
  parseLexed_eq_ok_of_pragmaSequence accepted clears parsed

example (result : parseLexed file lexed =
    .ok (pragmaSequenceParseOutput file lexed declarations kept)) :
    LexedFileValidationAccepts file lexed ∧ kept = trace :=
  (parseLexed_eq_ok_pragmaSequence_iff clears parsed).mp result

example (same : kept = trace) :
    parseLexed file lexed = .ok (pragmaSequenceParseOutput file lexed declarations kept) :=
  (parseLexed_eq_ok_pragmaSequence_iff clears parsed).mpr ⟨accepted, same⟩

example (lexing : Lexer.lex file = .ok lexed) :
    parse file = .ok (pragmaSequenceParseOutput file lexed declarations trace) :=
  parse_eq_ok_of_pragmaSequence lexing clears parsed

example (lexing : Lexer.lex file = .ok lexed)
    (result : parse file = .ok (pragmaSequenceParseOutput file lexed declarations kept)) :
    kept = trace := (parse_eq_ok_pragmaSequence_iff lexing clears parsed).mp result

example (lexing : Lexer.lex file = .ok lexed) (same : kept = trace) :
    parse file = .ok (pragmaSequenceParseOutput file lexed declarations kept) :=
  (parse_eq_ok_pragmaSequence_iff lexing clears parsed).mpr same

example (filtered : ParseDiagnosticCascadeFilters file.content
    (lexed.diagnostics.map (·.span)) trace kept) : kept = trace :=
  (parsed.cascadeFilters_iff file.content (lexed.diagnostics.map (·.span))).mp filtered

/-- The empty grammar case retains arbitrary lexical diagnostics and comments;
neither clear nesting nor an executable parser result needs to be assumed. -/
theorem empty_sequence_parse_eq_output
    (lexing : Lexer.lex file = .ok lexed) (empty : lexed.tokens = []) :
    parse file = .ok {
      parsed := {
        source := file.id
        span := SourceSpan.fullFile file
        items := []
        comments := lexed.comments
      }
      tokens := lexed.tokens
      lexicalDiagnostics := lexed.diagnostics
      parseDiagnostics := []
    } := by
  have emptyGrammar : PragmaSequenceTraceParses (sourceFileRootRemainder lexed.tokens)
      [] (sourceFileRootRemainder lexed.tokens) [] :=
    .done (by simp [sourceFileRootRemainder, empty])
  have emptyClears : NestingClears lexed.tokens := by
    rw [empty]
    exact .done
  exact parse_eq_ok_of_pragmaSequence lexing emptyClears emptyGrammar

end Solcore.Test.SyntaxParserPublicPragmaSequenceOutputProperties
