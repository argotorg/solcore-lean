import Solcore.Syntax.Parser.PublicPragmaRejectionOutputProperties
import Solcore.Test.SyntaxParserPragmaLaterRejectionFixtures

/-! Complete canonical-source outputs after a recognized pragma fails later.
Independent grammar and mixed filtering preserve prior events before the
committed failure, while lexical cascades remove only eligible reports. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserPublicPragmaLaterRejectionExamples

open Solcore.Syntax
open Solcore.Syntax.Parser
open Solcore.Syntax.DeclarativeGrammar
open Solcore.Test.SyntaxParserPublicPragmaNameRejectionExamples
open Solcore.Test.SyntaxParserPublicPragmaSuccessExamples
open Solcore.Test.SyntaxParserPragmaLaterRejectionFixtures

/-- Comma followed by EOF is not the accepted comma-semicolon trailing form.
The checked-name event precedes the committed missing-identifier report. -/
theorem missingItem_parse_eq_output :
    parse (exampleFile "pragma p a-b,") =
      .ok (expectedOutput "pragma p a-b," (missingItemTokens 0) []
        [hyphenEvent 0, eofUnexpected 13 .identifier]) :=
  parse_eq_ok_of_pragmaRejection missingItemLexes
    (prefixClears 0 [commaToken 12] (.reset rfl .done))
    (prefixKeyword 0 [commaToken 12]) (missingItemDeclRejects 0)
    (parseDiagnosticCascadeFilters_nil_lexical "pragma p a-b,"
      [hyphenEvent 0, eofUnexpected 13 .identifier])

/-- Without a comma, item scanning succeeds and the final semicolon is
expected. No unfinished pragma AST escapes, but its checked-name event remains. -/
theorem missingSemicolon_parse_eq_output :
    parse (exampleFile "pragma p a-b") =
      .ok (expectedOutput "pragma p a-b" (prefixTokens 0) []
        [hyphenEvent 0, eofUnexpected 12 (.symbol .semicolon)]) :=
  parse_eq_ok_of_pragmaRejection missingSemicolonLexes
    (prefixClears 0 [] .done) (prefixKeyword 0 []) (missingSemicolonDeclRejects 0)
    (parseDiagnosticCascadeFilters_nil_lexical "pragma p a-b"
      [hyphenEvent 0, eofUnexpected 12 (.symbol .semicolon)])

/-- A same-line lexical error suppresses only the trailing unexpected event;
the earlier invalid-identifier kind remains protected despite the same line. -/
theorem sameLineMixedFiltered :
    ParseDiagnosticCascadeFilters "§ pragma p a-b," [lexicalInvalid.span]
      [hyphenEvent 3, eofUnexpected 16 .identifier] [hyphenEvent 3] := by
  apply parseDiagnosticCascadeFilters_protected_cons
  · change ¬ False
    exact id
  · apply ParseDiagnosticCascadeFilters.drop
    · refine ⟨True.intro, lexicalInvalid.span, by simp, rfl, Or.inl ?_⟩
      decide
    · exact .nil

/-- Lexical diagnostics and the protected checked-name event survive in the
complete output, while the committed EOF expectation is filtered out. -/
theorem sameLineLexical_parse_eq_output :
    parse (exampleFile "§ pragma p a-b,") =
      .ok (expectedOutput "§ pragma p a-b," (missingItemTokens 3) [lexicalInvalid]
        [hyphenEvent 3]) :=
  parse_eq_ok_of_pragmaRejection sameLineLexes
    (prefixClears 3 [commaToken 15] (.reset rfl .done))
    (prefixKeyword 3 [commaToken 15]) (missingItemDeclRejects 3) sameLineMixedFiltered

/-- The token-to-file entry point returns all the same fields using validity
from the identical canonical lexer fixture, not an assumed parser execution. -/
theorem sameLineLexical_parseLexed_eq_output :
    parseLexed (exampleFile "§ pragma p a-b,")
        (lexicalCarrier (missingItemTokens 3) [lexicalInvalid]) =
      .ok (expectedOutput "§ pragma p a-b," (missingItemTokens 3) [lexicalInvalid]
        [hyphenEvent 3]) :=
  parseLexed_eq_ok_of_pragmaRejection
    ((lexedFileValidationAccepts_iff_validFor _ _).mpr (Lexer.lex_ok_validFor _ _ sameLineLexes))
    (prefixClears 3 [commaToken 15] (.reset rfl .done))
    (prefixKeyword 3 [commaToken 15]) (missingItemDeclRejects 3) sameLineMixedFiltered

end Solcore.Test.SyntaxParserPublicPragmaLaterRejectionExamples
