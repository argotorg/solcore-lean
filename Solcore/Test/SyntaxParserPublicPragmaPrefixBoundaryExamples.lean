import Solcore.Syntax.Parser.PublicPragmaPrefixBoundaryOutputProperties
import Solcore.Test.SyntaxParserPragmaPrefixBoundaryFixtures

/-! Complete successful-prefix outputs followed by a recognized pragma failure.
The successful AST survives, as do both prior checked-name events; only the
separately committed EOF report is eligible for lexical-cascade suppression. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserPublicPragmaPrefixBoundaryExamples

open Solcore.Syntax
open Solcore.Syntax.Parser
open Solcore.Syntax.DeclarativeGrammar
open Solcore.Test.SyntaxParserPublicPragmaNameRejectionExamples
open Solcore.Test.SyntaxParserPublicPragmaSuccessExamples
open Solcore.Test.SyntaxParserPragmaLaterRejectionFixtures (eofUnexpected)
open Solcore.Test.SyntaxParserPragmaPrefixBoundaryFixtures

/-- Only the first pragma contributes an AST. Tokens and lexical diagnostics
still describe the entire input, including the unfinished second declaration. -/
private def boundaryOutput (content : String) (offset : Nat)
    (lexical : List LexicalDiagnostic) (kept : List ParseDiagnostic) : ParseOutput := {
  parsed := {
    source := exampleSource
    span := SourceSpan.fullFile (exampleFile content)
    items := [{
      span := keptDeclaration.span
      leadingComments := []
      value := .pragmaDecl keptDeclaration }]
    comments := []
  }
  tokens := boundaryTokens offset
  lexicalDiagnostics := lexical
  parseDiagnostics := kept
}

/-- The successful item's event precedes the rejected pragma's event, followed
exactly once by the committed identifier expectation at EOF byte 27. -/
theorem successfulThenRejected_parse_eq_output :
    parse (exampleFile "pragma p a-b; pragma q c-d,") =
      .ok (boundaryOutput "pragma p a-b; pragma q c-d," 14 []
        [firstEvent, secondEvent 14, eofUnexpected 27 .identifier]) :=
  parse_eq_ok_of_pragmaPrefixBoundary cleanBoundaryLexes (boundaryClears 14) (boundaryParsed 14)
    (parseDiagnosticCascadeFilters_nil_lexical "pragma p a-b; pragma q c-d,"
      [firstEvent, secondEvent 14, eofUnexpected 27 .identifier])

/-- Both protected events retain their exact order and payloads while the
same-line lexical error suppresses only the final unexpected-token report. -/
theorem sameLineMixedFiltered :
    ParseDiagnosticCascadeFilters "pragma p a-b; § pragma q c-d," [lexicalBetween.span]
      [firstEvent, secondEvent 17, eofUnexpected 30 .identifier] [firstEvent, secondEvent 17] := by
  refine .keep (fun h => h.1) (.keep (fun h => h.1) (.drop ?_ .nil))
  refine ⟨True.intro, lexicalBetween.span, by simp, rfl, Or.inl ?_⟩
  decide

/-- A lexical error between the declarations retains the successful singleton
AST and both hyphen events, but removes the committed EOF report from the output. -/
theorem sameLineLexical_parse_eq_output :
    parse (exampleFile "pragma p a-b; § pragma q c-d,") =
      .ok (boundaryOutput "pragma p a-b; § pragma q c-d," 17 [lexicalBetween]
        [firstEvent, secondEvent 17]) :=
  parse_eq_ok_of_pragmaPrefixBoundary sameLineBoundaryLexes
    (boundaryClears 17) (boundaryParsed 17) sameLineMixedFiltered

/-- Validation comes from canonical lexing; no executable parser outcome is
assumed when computing the identical complete token-to-file result. -/
theorem sameLineLexical_parseLexed_eq_output :
    parseLexed (exampleFile "pragma p a-b; § pragma q c-d,")
        (lexicalCarrier (boundaryTokens 17) [lexicalBetween]) =
      .ok (boundaryOutput "pragma p a-b; § pragma q c-d," 17 [lexicalBetween]
        [firstEvent, secondEvent 17]) :=
  parseLexed_eq_ok_of_pragmaPrefixBoundary
    ((lexedFileValidationAccepts_iff_validFor _ _).mpr
      (Lexer.lex_ok_validFor _ _ sameLineBoundaryLexes))
    (boundaryClears 17) (boundaryParsed 17) sameLineMixedFiltered

end Solcore.Test.SyntaxParserPublicPragmaPrefixBoundaryExamples
