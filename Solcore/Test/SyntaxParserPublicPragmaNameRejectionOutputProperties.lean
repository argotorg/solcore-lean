import Solcore.Syntax.Parser.PublicPragmaNameRejectionOutputProperties

/-! Consumers of complete public outputs from an independent missing pragma
name, preserving source context and exact expectation-report metadata. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserPublicPragmaNameRejectionOutputProperties

open Solcore.Syntax
open Solcore.Syntax.Parser
open Solcore.Syntax.DeclarativeGrammar

variable {file : SourceFile} {lexed : LexedFile} {after : Remainder}
  {span : SourceSpan} {found : Option TokenKind} {kept : List SourceSpan}
  (accepted : LexedFileValidationAccepts file lexed)
  (clears : NestingClears lexed.tokens)
  (missing : PragmaNameMissingAt file.id file.content.utf8ByteSize
    (sourceFileRootRemainder lexed.tokens) after span found)

example (filtered : LexicalCascadeFilters file.content
    (lexed.diagnostics.map (·.span)) [span] kept) :
    parseLexed file lexed = .ok {
      parsed := {
        source := file.id
        span := SourceSpan.fullFile file
        items := []
        comments := lexed.comments
      }
      tokens := lexed.tokens
      lexicalDiagnostics := lexed.diagnostics
      parseDiagnostics := unexpectedDiagnostics found
        { head := .identifier, tail := [] } .pragmaDecl kept
    } :=
  parseLexed_eq_ok_of_pragmaNameMissing accepted clears missing filtered

example (result : parseLexed file lexed =
    .ok (pragmaNameMissingParseOutput file lexed found kept)) :
    LexedFileValidationAccepts file lexed ∧
      LexicalCascadeFilters file.content (lexed.diagnostics.map (·.span)) [span] kept :=
  (parseLexed_eq_ok_pragmaNameMissing_iff clears missing).mp result

example (suppressed : LexicalCascadeSuppresses file.content
    (lexed.diagnostics.map (·.span)) span) :
    parseLexed file lexed = .ok (pragmaNameMissingParseOutput file lexed found []) :=
  parseLexed_eq_ok_of_pragmaNameMissing accepted clears missing (.drop suppressed .nil)

example (retained : ¬ LexicalCascadeSuppresses file.content
    (lexed.diagnostics.map (·.span)) span) :
    parseLexed file lexed = .ok (pragmaNameMissingParseOutput file lexed found [span]) :=
  parseLexed_eq_ok_of_pragmaNameMissing accepted clears missing (.keep retained .nil)

example (lexing : Lexer.lex file = .ok lexed)
    (filtered : LexicalCascadeFilters file.content
      (lexed.diagnostics.map (·.span)) [span] kept) :
    parse file = .ok (pragmaNameMissingParseOutput file lexed found kept) :=
  parse_eq_ok_of_pragmaNameMissing lexing clears missing filtered

example (lexing : Lexer.lex file = .ok lexed)
    (result : parse file = .ok (pragmaNameMissingParseOutput file lexed found kept)) :
    LexicalCascadeFilters file.content (lexed.diagnostics.map (·.span)) [span] kept :=
  (parse_eq_ok_pragmaNameMissing_iff lexing clears missing).mp result

end Solcore.Test.SyntaxParserPublicPragmaNameRejectionOutputProperties
