import Solcore.Syntax.Parser.PublicPragmaRejectionOutputProperties
import Solcore.Syntax.DeclarativeParseDiagnosticCascadeStabilityProperties

/-! Complete public rejection consumers. Every premise describes independent
input, grammar, or filtering; none assumes a declaration or file parser reply. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserPublicPragmaRejectionOutputProperties

open Solcore.Syntax
open Solcore.Syntax.Parser
open Solcore.Syntax.DeclarativeGrammar

variable {file : SourceFile} {lexed : LexedFile}
  {marker : SourceSpan} {afterKeyword rejected : Remainder}
  {diagnostic : ParseDiagnostic} {trace kept : List ParseDiagnostic}
  (accepted : LexedFileValidationAccepts file lexed)
  (clears : NestingClears lexed.tokens)
  (keywordParsed : ExactTokenParses (.keyword .pragmaKw)
    (sourceFileRootRemainder lexed.tokens) marker afterKeyword)
  (traced : PragmaDeclTraceRejects file.id file.content.utf8ByteSize
    (sourceFileRootRemainder lexed.tokens) rejected diagnostic trace)
  (filtered : ParseDiagnosticCascadeFilters file.content
    (lexed.diagnostics.map (·.span)) (trace ++ [diagnostic]) kept)

example : parseLexed file lexed = .ok {
    parsed := {
      source := file.id
      span := SourceSpan.fullFile file
      items := []
      comments := lexed.comments
    }
    tokens := lexed.tokens
    lexicalDiagnostics := lexed.diagnostics
    parseDiagnostics := kept
  } :=
  parseLexed_eq_ok_of_pragmaRejection accepted clears keywordParsed traced filtered

example (result : parseLexed file lexed = .ok (pragmaRejectionParseOutput file lexed kept)) :
    LexedFileValidationAccepts file lexed ∧
      ParseDiagnosticCascadeFilters file.content
        (lexed.diagnostics.map (·.span)) (trace ++ [diagnostic]) kept :=
  (parseLexed_eq_ok_pragmaRejection_iff clears keywordParsed traced).mp result

example : parseLexed file lexed = .ok (pragmaRejectionParseOutput file lexed kept) :=
  (parseLexed_eq_ok_pragmaRejection_iff clears keywordParsed traced).mpr ⟨accepted, filtered⟩

example (lexing : Lexer.lex file = .ok lexed) :
    parse file = .ok (pragmaRejectionParseOutput file lexed kept) :=
  parse_eq_ok_of_pragmaRejection lexing clears keywordParsed traced filtered

example (lexing : Lexer.lex file = .ok lexed)
    (result : parse file = .ok (pragmaRejectionParseOutput file lexed kept)) :
    ParseDiagnosticCascadeFilters file.content
      (lexed.diagnostics.map (·.span)) (trace ++ [diagnostic]) kept :=
  (parse_eq_ok_pragmaRejection_iff lexing clears keywordParsed traced).mp result

example (lexing : Lexer.lex file = .ok lexed) :
    parse file = .ok (pragmaRejectionParseOutput file lexed kept) :=
  (parse_eq_ok_pragmaRejection_iff lexing clears keywordParsed traced).mpr filtered

include traced in
/-- Already emitted item diagnostics are protected even though the declaration
ultimately rejects; lexical cascade suppression cannot erase these events. -/
theorem rejected_item_events_retained :
    ParseDiagnosticCascadeFilters file.content (lexed.diagnostics.map (·.span)) trace trace :=
  traced.cascadeFilters file.content (lexed.diagnostics.map (·.span))

include clears keywordParsed traced in
/-- If no lexical errors occur, every prior event and the final report survive
in exactly that order. This is a complete output computation from grammar. -/
theorem no_lexical_errors_keeps_committed_trace
    (lexing : Lexer.lex file = .ok lexed) (noErrors : lexed.diagnostics = []) :
    parse file = .ok (pragmaRejectionParseOutput file lexed (trace ++ [diagnostic])) := by
  apply parse_eq_ok_of_pragmaRejection lexing clears keywordParsed traced
  rw [noErrors]
  apply parseDiagnosticCascadeFilters_of_retained file.content ([] : List SourceSpan)
  intro event _member suppressed
  rcases suppressed.2 with ⟨span, membership, _⟩
  simp only [List.not_mem_nil] at membership

end Solcore.Test.SyntaxParserPublicPragmaRejectionOutputProperties
