import Solcore.Syntax.Parser.PublicParseCompletenessProperties

/-! Consequences for independent public syntax, with no executable parser
reply in the hypotheses: validated carriers determine one AST, and every such
derivation satisfies the complete recursive source-provenance contract. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- An independently derived public AST over validated carriers has valid
recursive source spans, including recovered and nesting-overflow syntax. -/
theorem PublicSourceFileOrdinaryParses.validFor_of_validation
    {file : SourceFile} {lexed : LexedFile} {parsed : ParsedFile}
    (accepted : LexedFileValidationAccepts file lexed)
    (derivation : PublicSourceFileOrdinaryParses file
      lexed.tokens lexed.comments parsed) :
    ParsedFile.ValidFor CoreStatement.ValidFor CoreExpr.ValidFor file parsed := by
  rcases (Parser.parseLexed_exists_ok_iff_publicSourceFileOrdinary
      file lexed parsed).mpr ⟨accepted, derivation⟩ with
    ⟨output, result, valueEq⟩
  have valid := (Parser.parseLexed_ok_completeOutput_validFor
    file lexed output result).parsed
  simpa only [valueEq] using valid

/-- Validated token carriers have exactly one independently derived public
AST. No diagnostic-free or nesting-clearance hypothesis is required. -/
theorem publicSourceFileOrdinary_exists_unique_of_validation
    (file : SourceFile) (lexed : LexedFile)
    (accepted : LexedFileValidationAccepts file lexed) :
    ∃ parsed,
      PublicSourceFileOrdinaryParses file lexed.tokens lexed.comments parsed ∧
      ∀ other, PublicSourceFileOrdinaryParses file
        lexed.tokens lexed.comments other → other = parsed := by
  have valid := (lexedFileValidationAccepts_iff_validFor file lexed).mp accepted
  rcases Parser.productionParseLexed_exists_ok_publicSourceFileOrdinary
      file lexed valid with ⟨output, _, derivation, _⟩
  exact ⟨output.parsed, derivation, fun _ other =>
    PublicSourceFileOrdinaryParses.value_unique other derivation⟩

/-- Canonical lexical provenance supplies validation for any independently
derived public AST; no executable parser result is assumed. -/
theorem PublicSourceFileOrdinaryParses.validFor_of_lexing
    {file : SourceFile} {lexed : LexedFile} {parsed : ParsedFile}
    (lexing : Lexer.lex file = .ok lexed)
    (derivation : PublicSourceFileOrdinaryParses file
      lexed.tokens lexed.comments parsed) :
    ParsedFile.ValidFor CoreStatement.ValidFor CoreExpr.ValidFor file parsed :=
  derivation.validFor_of_validation
    ((lexedFileValidationAccepts_iff_validFor file lexed).mpr
      (Lexer.lex_ok_validFor file lexed lexing))

end Solcore.Syntax.DeclarativeGrammar
