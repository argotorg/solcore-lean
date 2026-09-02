import Solcore.Syntax.Parser.PublicNestingExceededOutputProperties

/-! Exact executable witnesses for the clear public source-file branch. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Complete public output assembled from one successful source-file reply. -/
def sourceFileParseOutput (file : SourceFile) (lexed : LexedFile)
    (parsed : ParsedFile) (finalState : State) : ParseOutput := {
  parsed
  tokens := lexed.tokens
  lexicalDiagnostics := lexed.diagnostics
  parseDiagnostics := filterParseDiagnostics file lexed.diagnostics
    finalState.diagnostics
}

/-- A successful clear token-to-file parse exposes the exact underlying
source-file execution and complete public output assembled from it. -/
theorem parseLexed_ok_sourceFile_executionWitness_of_nestingClears
    {file : SourceFile} {lexed : LexedFile} {output : ParseOutput}
    (clears : DeclarativeGrammar.NestingClears lexed.tokens)
    (result : parseLexed file lexed = .ok output) :
    ∃ parsed finalState,
      sourceFile lexed.comments (State.initial file lexed) =
          .ok parsed finalState ∧
        output = sourceFileParseOutput file lexed parsed finalState := by
  have lexedValid := parseLexed_ok_input_validFor file lexed output result
  unfold parseLexed at result
  rw [validateLexed_validFor_ok file lexed lexedValid] at result
  have nesting :=
    (checkNesting_none_iff_nestingClears lexed.tokens).mpr clears
  simp only [nesting] at result
  cases grammar : sourceFile lexed.comments (State.initial file lexed) with
  | ok parsed finalState =>
      simp only [grammar] at result
      cases result
      exact ⟨parsed, finalState, rfl, rfl⟩
  | reject failure rejected =>
      simp only [grammar] at result
      contradiction
  | invariant error =>
      simp only [grammar] at result
      contradiction

/-- The normal public parse-diagnostic list has an exact executable final-state
witness even though the broad declarative grammar does not yet carry traces. -/
theorem parseLexed_ok_parseDiagnostics_executionWitness_of_nestingClears
    {file : SourceFile} {lexed : LexedFile} {output : ParseOutput}
    (clears : DeclarativeGrammar.NestingClears lexed.tokens)
    (result : parseLexed file lexed = .ok output) :
    ∃ finalState,
      sourceFile lexed.comments (State.initial file lexed) =
          .ok output.parsed finalState ∧
        output.parseDiagnostics = filterParseDiagnostics file
          lexed.diagnostics finalState.diagnostics := by
  rcases parseLexed_ok_sourceFile_executionWitness_of_nestingClears
      clears result with ⟨parsed, finalState, grammar, outputEq⟩
  subst output
  exact ⟨finalState, grammar, rfl⟩

/-- A clear complete-source parse exposes both its lexical execution and exact
underlying source-file execution over the same tokenized carrier. -/
theorem parse_ok_sourceFile_executionWitness_of_nestingClears
    {file : SourceFile} {output : ParseOutput}
    (clears : DeclarativeGrammar.NestingClears output.tokens)
    (result : parse file = .ok output) :
    ∃ lexed parsed finalState,
      Lexer.lex file = .ok lexed ∧
        sourceFile lexed.comments (State.initial file lexed) =
          .ok parsed finalState ∧
        output = sourceFileParseOutput file lexed parsed finalState := by
  rcases parse_ok_lexed_provenance file output result with
    ⟨lexed, lexing, parsing, tokens, _diagnostics, _comments⟩
  have lexedClears : DeclarativeGrammar.NestingClears lexed.tokens := by
    simpa only [tokens] using clears
  rcases parseLexed_ok_sourceFile_executionWitness_of_nestingClears
      lexedClears parsing with ⟨parsed, finalState, grammar, outputEq⟩
  exact ⟨lexed, parsed, finalState, lexing, grammar, outputEq⟩

end Solcore.Syntax.Parser
