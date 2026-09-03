import Solcore.Syntax.Parser.LexedValidationOutcomeSoundnessProperties
import Solcore.Syntax.Parser.PublicSourceFileExecutionWitnessProperties

/-! Complete normal-branch outputs for independently empty token carriers.
Comments and lexical diagnostics need not be empty or diagnostic-free. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- An exhausted token window retains its complete state, including earlier
diagnostics, while returning an empty file with the supplied comments. -/
theorem sourceFile_atWindowEnd_exact (comments : List Comment) {input : State}
    (atEnd : input.window.endIndex ≤ input.cursor) :
    sourceFile comments input = .ok {
      source := input.file.id
      span := SourceSpan.fullFile input.file
      items := []
      comments
    } input := by
  have ended : input.atEnd = true := by simp [State.atEnd, atEnd]
  simp [sourceFile, FileInternals.parseItems, ended]

/-- Empty token input retains the lexical carrier and comments, and introduces
no parser diagnostic. This does not require empty source text. -/
def emptyTokensParseOutput (file : SourceFile) (lexed : LexedFile) : ParseOutput := {
  parsed := {
    source := file.id
    span := SourceSpan.fullFile file
    items := []
    comments := lexed.comments
  }
  tokens := lexed.tokens
  lexicalDiagnostics := lexed.diagnostics
  parseDiagnostics := []
}

/-- Validation is the only precondition for the complete empty-token output;
nesting clearance and the empty raw diagnostic trace follow from the carrier. -/
theorem parseLexed_eq_ok_emptyTokens_iff {file : SourceFile} {lexed : LexedFile}
    (empty : lexed.tokens = []) :
    parseLexed file lexed = .ok (emptyTokensParseOutput file lexed) ↔
      DeclarativeGrammar.LexedFileValidationAccepts file lexed := by
  constructor
  · intro result
    exact (DeclarativeGrammar.lexedFileValidationAccepts_iff_validFor file lexed).mpr
      (parseLexed_ok_input_validFor file lexed _ result)
  · intro accepted
    have clears : DeclarativeGrammar.NestingClears lexed.tokens := by
      rw [empty]
      exact .done
    have parsed := sourceFile_atWindowEnd_exact lexed.comments
      (input := State.initial file lexed) (by simp [State.initial, empty])
    unfold parseLexed
    rw [(validateLexed_ok_iff_validationAccepts file lexed).mpr accepted]
    rw [(checkNesting_none_iff_nestingClears lexed.tokens).mpr clears]
    rw [parsed]
    simp only [State.initial, State.diagnostics, List.reverse_nil,
      filterParseDiagnostics_nil_parsed]
    rfl

/-- Independent empty tokens and validation compute every public output field. -/
theorem parseLexed_eq_ok_of_emptyTokens {file : SourceFile} {lexed : LexedFile}
    (accepted : DeclarativeGrammar.LexedFileValidationAccepts file lexed)
    (empty : lexed.tokens = []) :
    parseLexed file lexed = .ok (emptyTokensParseOutput file lexed) :=
  (parseLexed_eq_ok_emptyTokens_iff empty).mpr accepted

/-- Canonical lexing supplies validation for empty, comment-only, or
lexically diagnosed tokenless input. No parser execution is assumed. -/
theorem parse_eq_ok_of_emptyTokens {file : SourceFile} {lexed : LexedFile}
    (lexing : Lexer.lex file = .ok lexed) (empty : lexed.tokens = []) :
    parse file = .ok (emptyTokensParseOutput file lexed) := by
  have accepted := (DeclarativeGrammar.lexedFileValidationAccepts_iff_validFor file lexed).mpr
    (Lexer.lex_ok_validFor file lexed lexing)
  have parsed := parseLexed_eq_ok_of_emptyTokens accepted empty
  simp only [parse, lexing, parsed]

end Solcore.Syntax.Parser
