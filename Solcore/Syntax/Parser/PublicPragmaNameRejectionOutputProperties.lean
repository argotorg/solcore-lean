import Solcore.Syntax.Parser.LexedValidationOutcomeSoundnessProperties
import Solcore.Syntax.Parser.PragmaNameRejectionTraceProperties
import Solcore.Syntax.Parser.PublicSourceFileExecutionWitnessProperties
import Solcore.Syntax.Parser.SourceFileBoundaryStopTraceProperties
import Solcore.Syntax.Parser.UnexpectedDiagnosticCascadeProperties

/-! Complete public outputs when a recognized pragma start stops at a missing
name. Independent rejection reports retain their source/end-byte context;
lexical-cascade filtering fixes the complete committed diagnostic sequence. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- A rejected pragma name stops before adding an AST item. Tokens, comments,
and lexical diagnostics are retained, with the exact filtered expectation report. -/
def pragmaNameMissingParseOutput (file : SourceFile) (lexed : LexedFile)
    (found : Option TokenKind) (kept : List SourceSpan) : ParseOutput := {
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
}

private theorem parseLexed_pragmaNameMissing_raw_eq
    {file : SourceFile} {lexed : LexedFile}
    {after : DeclarativeGrammar.Remainder} {span : SourceSpan}
    {found : Option TokenKind}
    (accepted : DeclarativeGrammar.LexedFileValidationAccepts file lexed)
    (clears : DeclarativeGrammar.NestingClears lexed.tokens)
    (missing : DeclarativeGrammar.PragmaNameMissingAt file.id file.content.utf8ByteSize
      (DeclarativeGrammar.sourceFileRootRemainder lexed.tokens) after span found) :
    parseLexed file lexed = .ok {
      pragmaNameMissingParseOutput file lexed found [] with
      parseDiagnostics := filterParseDiagnostics file lexed.diagnostics
        (unexpectedDiagnostics found { head := .identifier, tail := [] }
          .pragmaDecl [span])
    } := by
  cases missing with
  | missing keywordParsed nameAbsent current =>
      rcases FileInternals.parseItemsItem_pragmaNameMissing_exact
          (input := State.initial file lexed) keywordParsed nameAbsent current with
        ⟨rejected, _afterEq, priorEq⟩
      have inside : (State.initial file lexed).cursor <
          (State.initial file lexed).window.endIndex := keywordParsed.1.1
      have starts := FileInternals.atTopItemStart_eq_true_of_pragmaToken
        (input := State.initial file lexed) keywordParsed
      rcases FileInternals.sourceFile_boundaryStop_trace_exact lexed.comments
          inside starts rejected with ⟨output, result, _rewound, trace⟩
      have traceEq : output.diagnostics = unexpectedDiagnostics found
          { head := .identifier, tail := [] } .pragmaDecl [span] := by
        rw [priorEq] at trace
        simpa only [State.initial, State.diagnostics, List.reverse_nil,
          List.nil_append, Failure.toDiagnostic, unexpectedDiagnostics,
          List.map_cons, List.map_nil] using trace
      unfold parseLexed
      rw [(validateLexed_ok_iff_validationAccepts file lexed).mpr accepted]
      rw [(checkNesting_none_iff_nestingClears lexed.tokens).mpr clears]
      simp only [result, traceEq]
      rfl

/-- A missing-name prefix independently determines the full token-to-file
output exactly when validation accepts and the cascade grammar keeps the
specified spans. No attempted parser reply is part of the premise. -/
theorem parseLexed_eq_ok_pragmaNameMissing_iff
    {file : SourceFile} {lexed : LexedFile}
    {after : DeclarativeGrammar.Remainder} {span : SourceSpan}
    {found : Option TokenKind} {kept : List SourceSpan}
    (clears : DeclarativeGrammar.NestingClears lexed.tokens)
    (missing : DeclarativeGrammar.PragmaNameMissingAt file.id file.content.utf8ByteSize
      (DeclarativeGrammar.sourceFileRootRemainder lexed.tokens) after span found) :
    parseLexed file lexed = .ok (pragmaNameMissingParseOutput file lexed found kept) ↔
      DeclarativeGrammar.LexedFileValidationAccepts file lexed ∧
        DeclarativeGrammar.LexicalCascadeFilters file.content
          (lexed.diagnostics.map (·.span)) [span] kept := by
  constructor
  · intro result
    have accepted :=
      (DeclarativeGrammar.lexedFileValidationAccepts_iff_validFor file lexed).mpr
        (parseLexed_ok_input_validFor file lexed _ result)
    have expected := parseLexed_pragmaNameMissing_raw_eq accepted clears missing
    rw [expected] at result
    have diagnosticsEq := congrArg ParseOutput.parseDiagnostics (Except.ok.inj result)
    exact ⟨accepted, (filterParseDiagnostics_unexpected_iff file lexed.diagnostics found
      { head := .identifier, tail := [] } .pragmaDecl [span] kept).mpr diagnosticsEq⟩
  · rintro ⟨accepted, filtered⟩
    have filteredEq := filterParseDiagnostics_unexpected_of_filters file
      lexed.diagnostics found { head := .identifier, tail := [] } .pragmaDecl filtered
    have expected := parseLexed_pragmaNameMissing_raw_eq accepted clears missing
    simpa only [filteredEq, pragmaNameMissingParseOutput] using expected

/-- Independent validation, clear nesting, a missing pragma name, and exact
cascade filtering compute every field of the public token-to-file result. -/
theorem parseLexed_eq_ok_of_pragmaNameMissing
    {file : SourceFile} {lexed : LexedFile}
    {after : DeclarativeGrammar.Remainder} {span : SourceSpan}
    {found : Option TokenKind} {kept : List SourceSpan}
    (accepted : DeclarativeGrammar.LexedFileValidationAccepts file lexed)
    (clears : DeclarativeGrammar.NestingClears lexed.tokens)
    (missing : DeclarativeGrammar.PragmaNameMissingAt file.id file.content.utf8ByteSize
      (DeclarativeGrammar.sourceFileRootRemainder lexed.tokens) after span found)
    (filtered : DeclarativeGrammar.LexicalCascadeFilters file.content
      (lexed.diagnostics.map (·.span)) [span] kept) :
    parseLexed file lexed = .ok (pragmaNameMissingParseOutput file lexed found kept) :=
  (parseLexed_eq_ok_pragmaNameMissing_iff clears missing).mpr ⟨accepted, filtered⟩

/-- Canonical lexing supplies validation; the independent cascade relation then
exactly characterizes the complete source-to-file output of a missing-name prefix. -/
theorem parse_eq_ok_pragmaNameMissing_iff
    {file : SourceFile} {lexed : LexedFile}
    {after : DeclarativeGrammar.Remainder} {span : SourceSpan}
    {found : Option TokenKind} {kept : List SourceSpan}
    (lexing : Lexer.lex file = .ok lexed)
    (clears : DeclarativeGrammar.NestingClears lexed.tokens)
    (missing : DeclarativeGrammar.PragmaNameMissingAt file.id file.content.utf8ByteSize
      (DeclarativeGrammar.sourceFileRootRemainder lexed.tokens) after span found) :
    parse file = .ok (pragmaNameMissingParseOutput file lexed found kept) ↔
      DeclarativeGrammar.LexicalCascadeFilters file.content
        (lexed.diagnostics.map (·.span)) [span] kept := by
  have accepted :=
    (DeclarativeGrammar.lexedFileValidationAccepts_iff_validFor file lexed).mpr
      (Lexer.lex_ok_validFor file lexed lexing)
  constructor
  · intro result
    have parsing : parseLexed file lexed =
        .ok (pragmaNameMissingParseOutput file lexed found kept) := by
      unfold parse at result
      rw [lexing] at result
      cases parsed : parseLexed file lexed with
      | ok output =>
          simp only [parsed] at result
          cases result
          rfl
      | error error => simp only [parsed] at result; contradiction
    exact ((parseLexed_eq_ok_pragmaNameMissing_iff clears missing).mp parsing).2
  · intro filtered
    have parsing := parseLexed_eq_ok_of_pragmaNameMissing accepted clears missing filtered
    simp only [parse, lexing, parsing]

/-- The independently reported pragma failure and cascade decision determine
the complete source result, not only its empty AST or a diagnostic witness. -/
theorem parse_eq_ok_of_pragmaNameMissing
    {file : SourceFile} {lexed : LexedFile}
    {after : DeclarativeGrammar.Remainder} {span : SourceSpan}
    {found : Option TokenKind} {kept : List SourceSpan}
    (lexing : Lexer.lex file = .ok lexed)
    (clears : DeclarativeGrammar.NestingClears lexed.tokens)
    (missing : DeclarativeGrammar.PragmaNameMissingAt file.id file.content.utf8ByteSize
      (DeclarativeGrammar.sourceFileRootRemainder lexed.tokens) after span found)
    (filtered : DeclarativeGrammar.LexicalCascadeFilters file.content
      (lexed.diagnostics.map (·.span)) [span] kept) :
    parse file = .ok (pragmaNameMissingParseOutput file lexed found kept) :=
  (parse_eq_ok_pragmaNameMissing_iff lexing clears missing).mpr filtered

end Solcore.Syntax.Parser
