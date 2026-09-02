import Solcore.Syntax.Parser.PublicSourceFileOrdinaryOutcomeSoundnessProperties

/-! Exact public token-to-file output for the nesting-overflow branch. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Complete public output produced when nesting preflight stops the grammar. -/
def nestingExceededParseOutput (file : SourceFile) (lexed : LexedFile)
    (overflow : DeclarativeGrammar.NestingOverflow) : ParseOutput := {
  parsed := DeclarativeGrammar.nestingExceededParsedFile file lexed.comments
  tokens := lexed.tokens
  lexicalDiagnostics := lexed.diagnostics
  parseDiagnostics := [nestingOverflowDiagnostic overflow]
}

/-- Valid tokenized input with a declarative overflow computes the complete
canonical early output exactly. -/
theorem parseLexed_eq_ok_of_nestingExceeds
    (file : SourceFile) (lexed : LexedFile)
    (overflow : DeclarativeGrammar.NestingOverflow)
    (valid : lexed.ValidFor file)
    (exceeds : DeclarativeGrammar.NestingExceeds lexed.tokens overflow) :
    parseLexed file lexed =
      .ok (nestingExceededParseOutput file lexed overflow) := by
  unfold parseLexed
  rw [validateLexed_validFor_ok file lexed valid]
  have checked : checkNesting lexed.tokens =
      some (nestingOverflowDiagnostic overflow) := by
    simpa using checkNesting_eq_map_of_outcome exceeds
  rw [checked]
  cases overflow with
  | mk span dimension limit =>
      cases dimension <;>
        simp [nestingExceededParseOutput,
          DeclarativeGrammar.nestingExceededParsedFile,
          nestingOverflowDiagnostic] <;> rfl

/-- Any successful result under the same overflow equals the complete early
output, including retained carriers and the unsuppressed singleton diagnostic. -/
theorem parseLexed_ok_eq_nestingExceededParseOutput
    {file : SourceFile} {lexed : LexedFile} {output : ParseOutput}
    {overflow : DeclarativeGrammar.NestingOverflow}
    (exceeds : DeclarativeGrammar.NestingExceeds lexed.tokens overflow)
    (result : parseLexed file lexed = .ok output) :
    output = nestingExceededParseOutput file lexed overflow := by
  have valid := parseLexed_ok_input_validFor file lexed output result
  have expected :=
    parseLexed_eq_ok_of_nestingExceeds file lexed overflow valid exceeds
  rw [expected] at result
  exact (Except.ok.inj result).symm

/-- Nesting overflow is always exposed as the exact singleton public parser
diagnostic and is never removed as a lexical cascade. -/
theorem parseLexed_ok_parseDiagnostics_eq_of_nestingExceeds
    {file : SourceFile} {lexed : LexedFile} {output : ParseOutput}
    {overflow : DeclarativeGrammar.NestingOverflow}
    (exceeds : DeclarativeGrammar.NestingExceeds lexed.tokens overflow)
    (result : parseLexed file lexed = .ok output) :
    output.parseDiagnostics = [nestingOverflowDiagnostic overflow] := by
  rw [parseLexed_ok_eq_nestingExceededParseOutput exceeds result]
  rfl

end Solcore.Syntax.Parser
