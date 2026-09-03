import Solcore.Syntax.Parser.CertifiedLexedParseOutcomeProperties
import Solcore.Syntax.Parser.PublicSourceFileValueProperties
import Solcore.Syntax.Parser.SourceFileCompletenessProperties

/-! Exact public AST correspondence with validation and lexical provenance. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- A token-to-file result with the specified AST exists exactly when the supplied
carrier passes validation and the independent public grammar derives that AST.
Both nesting branches are included, without a diagnostic-free premise. -/
theorem parseLexed_exists_ok_iff_publicSourceFileOrdinary_of_topItem
    (itemOutcomes : DeclarativeGrammar.ExactDeterministicOutcomeSpec
      DeclarativeGrammar.TopItemOrdinaryParses DeclarativeGrammar.TopItemRejects)
    (file : SourceFile) (lexed : LexedFile) (parsed : ParsedFile) :
    (∃ output, parseLexed file lexed = .ok output ∧ output.parsed = parsed) ↔
      DeclarativeGrammar.LexedFileValidationAccepts file lexed ∧
        DeclarativeGrammar.PublicSourceFileOrdinaryParses file
          lexed.tokens lexed.comments parsed := by
  constructor
  · rintro ⟨output, result, rfl⟩
    exact ⟨(DeclarativeGrammar.lexedFileValidationAccepts_iff_validFor file lexed).mpr
      (parseLexed_ok_input_validFor file lexed output result),
      parseLexed_ok_publicSourceFileOrdinary_sound result⟩
  · rintro ⟨accepted, expected⟩
    have valid :=
      (DeclarativeGrammar.lexedFileValidationAccepts_iff_validFor file lexed).mp accepted
    rcases productionParseLexed_exists_ok file lexed valid with ⟨output, result⟩
    exact ⟨output, result,
      DeclarativeGrammar.PublicSourceFileOrdinaryParses.value_unique_of_exact_topItem
        itemOutcomes (parseLexed_ok_publicSourceFileOrdinary_sound result) expected⟩

/-- A source-to-file result with the specified AST exists exactly when canonical
lexing supplies carriers on which the independent public grammar derives that AST.
The lexical witness supplies all required carrier validity. -/
theorem parse_exists_ok_iff_publicSourceFileOrdinary_of_topItem
    (itemOutcomes : DeclarativeGrammar.ExactDeterministicOutcomeSpec
      DeclarativeGrammar.TopItemOrdinaryParses DeclarativeGrammar.TopItemRejects)
    (file : SourceFile) (parsed : ParsedFile) :
    (∃ output, parse file = .ok output ∧ output.parsed = parsed) ↔
      ∃ lexed, Lexer.lex file = .ok lexed ∧
        DeclarativeGrammar.PublicSourceFileOrdinaryParses file
          lexed.tokens lexed.comments parsed := by
  constructor
  · rintro ⟨output, result, rfl⟩
    rcases parse_ok_lexed_provenance file output result with
      ⟨lexed, lexing, parsing, _⟩
    exact ⟨lexed, lexing, parseLexed_ok_publicSourceFileOrdinary_sound parsing⟩
  · rintro ⟨lexed, lexing, expected⟩
    have accepted :=
      (DeclarativeGrammar.lexedFileValidationAccepts_iff_validFor file lexed).mpr
        (Lexer.lex_ok_validFor file lexed lexing)
    rcases (parseLexed_exists_ok_iff_publicSourceFileOrdinary_of_topItem
        itemOutcomes file lexed parsed).mpr ⟨accepted, expected⟩ with
      ⟨output, parsing, valueEq⟩
    exact ⟨output, by simp only [parse, lexing, parsing], valueEq⟩

/-- Public token-to-file AST correspondence has no recursive exactness premise.
Validation remains explicit because the syntax relation does not certify carriers. -/
theorem parseLexed_exists_ok_iff_publicSourceFileOrdinary
    (file : SourceFile) (lexed : LexedFile) (parsed : ParsedFile) :
    (∃ output, parseLexed file lexed = .ok output ∧ output.parsed = parsed) ↔
      DeclarativeGrammar.LexedFileValidationAccepts file lexed ∧
        DeclarativeGrammar.PublicSourceFileOrdinaryParses file
          lexed.tokens lexed.comments parsed :=
  parseLexed_exists_ok_iff_publicSourceFileOrdinary_of_topItem
    DeclarativeGrammar.topItemExactOutcomeSpec file lexed parsed

/-- Public source-to-file AST correspondence has no validity or recursive
exactness premise: canonical lexical provenance supplies the input certificate. -/
theorem parse_exists_ok_iff_publicSourceFileOrdinary
    (file : SourceFile) (parsed : ParsedFile) :
    (∃ output, parse file = .ok output ∧ output.parsed = parsed) ↔
      ∃ lexed, Lexer.lex file = .ok lexed ∧
        DeclarativeGrammar.PublicSourceFileOrdinaryParses file
          lexed.tokens lexed.comments parsed :=
  parse_exists_ok_iff_publicSourceFileOrdinary_of_topItem
    DeclarativeGrammar.topItemExactOutcomeSpec file parsed

end Solcore.Syntax.Parser
