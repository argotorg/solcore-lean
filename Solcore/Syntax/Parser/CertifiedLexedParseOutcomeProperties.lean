import Solcore.Syntax.Parser.CertifiedParseProperties
import Solcore.Syntax.Parser.LexedValidation
import Solcore.Syntax.Parser.ParseLexedErrorProperties

/-! Branch-complete certification of the public token-to-file boundary. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

open DeclarativeGrammar

/-- A public token-to-file error is exactly the mapped first declarative
validation rejection. No later parser invariant can escape. -/
theorem productionParseLexed_error_iff_validationRejects
    (file : SourceFile) (lexed : LexedFile)
    (error : ParserInvariantError) :
    parseLexed file lexed = .error error ↔
      ∃ failure,
        LexedFileValidationRejects file lexed failure ∧
          error = lexedValidationInvariantError failure := by
  rw [productionParseLexed_error_iff_validateLexed_error]
  exact validateLexed_error_iff_validationRejects file lexed error

/--
Every tokenized source has one certified outer public branch. Rejection exposes
the exact first validation failure. Acceptance exposes an actual output, broad
public syntax, exact retained lexical carriers, and complete canonical
validity. The theorem deliberately does not claim an independent exact trace
for normal-branch parse diagnostics.
-/
theorem productionParseLexed_certifiedOutcome
    (file : SourceFile) (lexed : LexedFile) :
    (∃ failure,
      LexedFileValidationRejects file lexed failure ∧
        parseLexed file lexed =
          .error (lexedValidationInvariantError failure)) ∨
    (∃ output,
      LexedFileValidationAccepts file lexed ∧
        parseLexed file lexed = .ok output ∧
        PublicSourceFileOrdinaryParses file
          lexed.tokens lexed.comments output.parsed ∧
        output.tokens = lexed.tokens ∧
        output.lexicalDiagnostics = lexed.diagnostics ∧
        output.parsed.comments = lexed.comments ∧
        output.CanonicalValidFor file) := by
  rcases lexedFileValidationOutcome_total file lexed with
    accepts | ⟨failure, rejects⟩
  · have valid :=
      (lexedFileValidationAccepts_iff_validFor file lexed).mp accepts
    rcases productionParseLexed_exists_ok_publicSourceFileOrdinary
        file lexed valid with
      ⟨output, parsed, syntaxOutcome, canonical⟩
    rcases parseLexed_ok_retention file lexed output parsed with
      ⟨tokens, diagnostics, comments⟩
    exact Or.inr ⟨output, accepts, parsed, syntaxOutcome, tokens, diagnostics,
      comments, canonical⟩
  · apply Or.inl
    refine ⟨failure, rejects, ?_⟩
    exact (productionParseLexed_error_iff_validationRejects file lexed
      (lexedValidationInvariantError failure)).mpr ⟨failure, rejects, rfl⟩

end Solcore.Syntax.Parser
