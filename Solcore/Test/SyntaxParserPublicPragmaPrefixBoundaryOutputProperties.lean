import Solcore.Syntax.Parser.PublicPragmaPrefixBoundaryOutputProperties

/-! Public successful-prefix boundary consumers. Complete output construction
uses independent syntax and filtering, never an executable declaration reply. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserPublicPragmaPrefixBoundaryOutputProperties

open Solcore.Syntax
open Solcore.Syntax.Parser
open Solcore.Syntax.DeclarativeGrammar

variable {file : SourceFile} {lexed : LexedFile} {declarations : List PragmaDecl}
  {stopped : Remainder} {diagnostic : ParseDiagnostic} {trace kept : List ParseDiagnostic}
  (accepted : LexedFileValidationAccepts file lexed)
  (clears : NestingClears lexed.tokens)
  (parsed : PragmaPrefixBoundaryTraceParses file.id file.content.utf8ByteSize
    (sourceFileRootRemainder lexed.tokens) declarations stopped diagnostic trace)
  (filtered : ParseDiagnosticCascadeFilters file.content
    (lexed.diagnostics.map (·.span)) (trace ++ [diagnostic]) kept)

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
    parseDiagnostics := kept
  } :=
  parseLexed_eq_ok_of_pragmaPrefixBoundary accepted clears parsed filtered

example (result : parseLexed file lexed =
    .ok (pragmaSequenceParseOutput file lexed declarations kept)) :
    LexedFileValidationAccepts file lexed ∧
      ParseDiagnosticCascadeFilters file.content
        (lexed.diagnostics.map (·.span)) (trace ++ [diagnostic]) kept :=
  (parseLexed_eq_ok_pragmaPrefixBoundary_iff clears parsed).mp result

example : parseLexed file lexed =
    .ok (pragmaSequenceParseOutput file lexed declarations kept) :=
  (parseLexed_eq_ok_pragmaPrefixBoundary_iff clears parsed).mpr ⟨accepted, filtered⟩

example (lexing : Lexer.lex file = .ok lexed) :
    parse file = .ok (pragmaSequenceParseOutput file lexed declarations kept) :=
  parse_eq_ok_of_pragmaPrefixBoundary lexing clears parsed filtered

example (lexing : Lexer.lex file = .ok lexed)
    (result : parse file = .ok (pragmaSequenceParseOutput file lexed declarations kept)) :
    ParseDiagnosticCascadeFilters file.content
      (lexed.diagnostics.map (·.span)) (trace ++ [diagnostic]) kept :=
  (parse_eq_ok_pragmaPrefixBoundary_iff lexing clears parsed).mp result

example (lexing : Lexer.lex file = .ok lexed) :
    parse file = .ok (pragmaSequenceParseOutput file lexed declarations kept) :=
  (parse_eq_ok_pragmaPrefixBoundary_iff lexing clears parsed).mpr filtered

include clears parsed in
/-- Suppressing the final report leaves all earlier events, including those
emitted inside the rejected pragma, and all successful prefix items intact. -/
theorem suppressed_report_keeps_prefix_and_events
    (lexing : Lexer.lex file = .ok lexed)
    (suppressed : ParseDiagnosticCascadeSuppresses file.content
      (lexed.diagnostics.map (·.span)) diagnostic) :
    parse file = .ok (pragmaSequenceParseOutput file lexed declarations trace) := by
  apply parse_eq_ok_of_pragmaPrefixBoundary lexing clears parsed
  simpa only [List.append_nil] using
    (parsed.cascadeFilters file.content (lexed.diagnostics.map (·.span))).append
      (.drop suppressed .nil)

include clears parsed in
/-- A retained final report occurs once after the complete ordered preceding
trace. It neither replaces prior reports nor contributes a rejected AST item. -/
theorem retained_report_follows_prefix_events
    (lexing : Lexer.lex file = .ok lexed)
    (retained : ¬ ParseDiagnosticCascadeSuppresses file.content
      (lexed.diagnostics.map (·.span)) diagnostic) :
    parse file = .ok
      (pragmaSequenceParseOutput file lexed declarations (trace ++ [diagnostic])) := by
  apply parse_eq_ok_of_pragmaPrefixBoundary lexing clears parsed
  exact (parsed.cascadeFilters file.content (lexed.diagnostics.map (·.span))).append
    (.keep retained .nil)

include clears parsed in
/-- Without lexical diagnostics, the full trace and final report survive,
regardless of the number of successful declarations or duplicate events. -/
theorem no_lexical_errors_keeps_prefix_and_committed_trace
    (lexing : Lexer.lex file = .ok lexed) (noErrors : lexed.diagnostics = []) :
    parse file = .ok
      (pragmaSequenceParseOutput file lexed declarations (trace ++ [diagnostic])) := by
  apply parse_eq_ok_of_pragmaPrefixBoundary lexing clears parsed
  rw [noErrors, List.map_nil]
  exact parseDiagnosticCascadeFilters_nil_lexical file.content (trace ++ [diagnostic])

include clears filtered in
/-- The zero-successful-prefix constructor recovers the initial-pragma stop
case, with comments and lexical fields retained and no fabricated AST item. -/
theorem stopped_initial_pragma_has_no_items
    {marker : SourceSpan} {afterKeyword rejected : Remainder}
    (lexing : Lexer.lex file = .ok lexed)
    (recognized : ExactTokenParses (.keyword .pragmaKw)
      (sourceFileRootRemainder lexed.tokens) marker afterKeyword)
    (rejected : PragmaDeclTraceRejects file.id file.content.utf8ByteSize
      (sourceFileRootRemainder lexed.tokens) rejected diagnostic trace) :
    parse file = .ok (pragmaSequenceParseOutput file lexed [] kept) :=
  parse_eq_ok_of_pragmaPrefixBoundary lexing clears (.stopped marker recognized rejected) filtered

end Solcore.Test.SyntaxParserPublicPragmaPrefixBoundaryOutputProperties
