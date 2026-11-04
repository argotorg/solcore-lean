import Solcore.Syntax.Parser.Correctness
import Solcore.Syntax.Parser.Internal.FileProofs
import Solcore.Syntax.Parser.Internal.PragmaTrace
import Solcore.Syntax.Parser.Internal.SourceFileTrace
import Solcore.Syntax.Parser.Internal.DiagnosticTrace
import Solcore.Syntax.Parser.Internal.ParseProperties
import Solcore.Syntax.Internal.PragmaTrace

/-!
The parser's exact output on complete public slices.

For these inputs the theorems fix the whole `ParseOutput`, diagnostics included. Main
declarations: `parse_eq_ok_of_emptyTokens`, `parseLexed_eq_ok_of_nestingExceeds`,
`parse_eq_ok_singleRecovery_iff`, `parse_eq_ok_singlePragma_iff`,
`parse_eq_ok_pragmaRejection_iff`.
-/

section
-- leanmerge: from Solcore.Syntax.Parser.PublicNestingExceededOutputProperties
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
end

section
-- leanmerge: from Solcore.Syntax.Parser.PublicSourceFileExecutionWitnessProperties
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
end

section
-- leanmerge: from Solcore.Syntax.Parser.PublicPragmaNameRejectionOutputProperties
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
end

section
-- leanmerge: from Solcore.Syntax.Parser.PublicEmptyTokensOutputProperties
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
end

section
-- leanmerge: from Solcore.Syntax.Parser.PublicSingleRecoveryOutputProperties
/-! Complete public outputs for a single unrecognized top-level recovery that
consumes the root token window. Independent recovery and cascade derivations
fix the AST, retained lexical carriers, and complete filtered diagnostic list. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Complete output fixed by the recovered item and the retained event spans.
Comment attachment preserves the canonical source-order AST construction. -/
def singleRecoveryParseOutput (file : SourceFile) (lexed : LexedFile)
    (item : TopItem) (kept : List SourceSpan) : ParseOutput := {
  parsed := {
    source := file.id
    span := SourceSpan.fullFile file
    items := [Trivia.attachTopItemComments file lexed.comments item]
    comments := lexed.comments
  }
  tokens := lexed.tokens
  lexicalDiagnostics := lexed.diagnostics
  parseDiagnostics := FileInternals.topItemRecoveryDiagnostics kept
}

private theorem parseLexed_singleRecovery_raw_eq
    {file : SourceFile} {lexed : LexedFile} {item : TopItem}
    {after : DeclarativeGrammar.Remainder}
    (accepted : DeclarativeGrammar.LexedFileValidationAccepts file lexed)
    (clears : DeclarativeGrammar.NestingClears lexed.tokens)
    (startsAbsent : DeclarativeGrammar.TopItemKindsAbsentAt
      (DeclarativeGrammar.sourceFileRootRemainder lexed.tokens)
      DeclarativeGrammar.ImportTerminatorTopItemStartKinds)
    (recovered : DeclarativeGrammar.TopItemRecoveryParses
      (DeclarativeGrammar.sourceFileRootRemainder lexed.tokens) item after)
    (atEnd : after.cursor = lexed.tokens.length) :
    parseLexed file lexed = .ok {
      singleRecoveryParseOutput file lexed item [] with
      parseDiagnostics := filterParseDiagnostics file lexed.diagnostics
        (FileInternals.topItemRecoveryDiagnostics [item.span])
    } := by
  rcases FileInternals.sourceFile_singleRecoveryToEnd_exact lexed.comments
      (input := State.initial file lexed) startsAbsent recovered atEnd with
    ⟨output, result, _remainder, trace⟩
  have traceEq : output.diagnostics =
      FileInternals.topItemRecoveryDiagnostics [item.span] := by
    simpa only [State.initial, State.diagnostics, List.reverse_nil,
      List.nil_append, FileInternals.topItemRecoveryDiagnostics,
      List.map_cons, List.map_nil] using trace
  unfold parseLexed
  rw [(validateLexed_ok_iff_validationAccepts file lexed).mpr accepted]
  rw [(checkNesting_none_iff_nestingClears lexed.tokens).mpr clears]
  simp only [result, traceEq]
  rfl

/-- Under independent root recovery and clear nesting, the complete public
output is exact iff validation accepts and the cascade grammar retains the
specified event spans. No executable parser reply is assumed. -/
theorem parseLexed_eq_ok_singleRecovery_iff
    {file : SourceFile} {lexed : LexedFile} {item : TopItem}
    {after : DeclarativeGrammar.Remainder} {kept : List SourceSpan}
    (clears : DeclarativeGrammar.NestingClears lexed.tokens)
    (startsAbsent : DeclarativeGrammar.TopItemKindsAbsentAt
      (DeclarativeGrammar.sourceFileRootRemainder lexed.tokens)
      DeclarativeGrammar.ImportTerminatorTopItemStartKinds)
    (recovered : DeclarativeGrammar.TopItemRecoveryParses
      (DeclarativeGrammar.sourceFileRootRemainder lexed.tokens) item after)
    (atEnd : after.cursor = lexed.tokens.length) :
    parseLexed file lexed = .ok (singleRecoveryParseOutput file lexed item kept) ↔
      DeclarativeGrammar.LexedFileValidationAccepts file lexed ∧
        DeclarativeGrammar.LexicalCascadeFilters file.content
          (lexed.diagnostics.map (·.span)) [item.span] kept := by
  constructor
  · intro result
    have accepted :=
      (DeclarativeGrammar.lexedFileValidationAccepts_iff_validFor file lexed).mpr
        (parseLexed_ok_input_validFor file lexed _ result)
    have expected := parseLexed_singleRecovery_raw_eq accepted clears
      startsAbsent recovered atEnd
    rw [expected] at result
    have diagnosticsEq := congrArg ParseOutput.parseDiagnostics
      (Except.ok.inj result)
    refine ⟨accepted, ?_⟩
    exact (filterParseDiagnostics_recoveredTopItems_iff
      file lexed.diagnostics [item.span] kept).mpr diagnosticsEq
  · rintro ⟨accepted, filtered⟩
    have filteredEq := (filterParseDiagnostics_recoveredTopItems_iff
      file lexed.diagnostics [item.span] kept).mp filtered
    have expected := parseLexed_singleRecovery_raw_eq accepted clears
      startsAbsent recovered atEnd
    simpa only [filteredEq, singleRecoveryParseOutput] using expected

/-- Independent validated recovery and lexical-cascade derivations compute
the exact token-to-file output, including all four public fields. -/
theorem parseLexed_eq_ok_of_singleRecoveryToEnd
    {file : SourceFile} {lexed : LexedFile} {item : TopItem}
    {after : DeclarativeGrammar.Remainder} {kept : List SourceSpan}
    (accepted : DeclarativeGrammar.LexedFileValidationAccepts file lexed)
    (clears : DeclarativeGrammar.NestingClears lexed.tokens)
    (startsAbsent : DeclarativeGrammar.TopItemKindsAbsentAt
      (DeclarativeGrammar.sourceFileRootRemainder lexed.tokens)
      DeclarativeGrammar.ImportTerminatorTopItemStartKinds)
    (recovered : DeclarativeGrammar.TopItemRecoveryParses
      (DeclarativeGrammar.sourceFileRootRemainder lexed.tokens) item after)
    (atEnd : after.cursor = lexed.tokens.length)
    (filtered : DeclarativeGrammar.LexicalCascadeFilters file.content
      (lexed.diagnostics.map (·.span)) [item.span] kept) :
    parseLexed file lexed = .ok (singleRecoveryParseOutput file lexed item kept) :=
  (parseLexed_eq_ok_singleRecovery_iff clears startsAbsent recovered atEnd).mpr
    ⟨accepted, filtered⟩

/-- Canonical lexing supplies validation, leaving exactly the independent
cascade relation to characterize the complete source-to-file result. -/
theorem parse_eq_ok_singleRecovery_iff
    {file : SourceFile} {lexed : LexedFile} {item : TopItem}
    {after : DeclarativeGrammar.Remainder} {kept : List SourceSpan}
    (lexing : Lexer.lex file = .ok lexed)
    (clears : DeclarativeGrammar.NestingClears lexed.tokens)
    (startsAbsent : DeclarativeGrammar.TopItemKindsAbsentAt
      (DeclarativeGrammar.sourceFileRootRemainder lexed.tokens)
      DeclarativeGrammar.ImportTerminatorTopItemStartKinds)
    (recovered : DeclarativeGrammar.TopItemRecoveryParses
      (DeclarativeGrammar.sourceFileRootRemainder lexed.tokens) item after)
    (atEnd : after.cursor = lexed.tokens.length) :
    parse file = .ok (singleRecoveryParseOutput file lexed item kept) ↔
      DeclarativeGrammar.LexicalCascadeFilters file.content
        (lexed.diagnostics.map (·.span)) [item.span] kept := by
  have accepted :=
    (DeclarativeGrammar.lexedFileValidationAccepts_iff_validFor file lexed).mpr
      (Lexer.lex_ok_validFor file lexed lexing)
  constructor
  · intro result
    have parsing : parseLexed file lexed =
        .ok (singleRecoveryParseOutput file lexed item kept) := by
      unfold parse at result
      rw [lexing] at result
      cases parsed : parseLexed file lexed with
      | ok output =>
          simp only [parsed] at result
          cases result
          rfl
      | error error => simp only [parsed] at result; contradiction
    exact ((parseLexed_eq_ok_singleRecovery_iff
      clears startsAbsent recovered atEnd).mp parsing).2
  · intro filtered
    have parsing := parseLexed_eq_ok_of_singleRecoveryToEnd accepted clears
      startsAbsent recovered atEnd filtered
    simp only [parse, lexing, parsing]

/-- Independent root recovery and filtering also determine the complete
source-to-file result; lexical execution supplies provenance automatically. -/
theorem parse_eq_ok_of_singleRecoveryToEnd
    {file : SourceFile} {lexed : LexedFile} {item : TopItem}
    {after : DeclarativeGrammar.Remainder} {kept : List SourceSpan}
    (lexing : Lexer.lex file = .ok lexed)
    (clears : DeclarativeGrammar.NestingClears lexed.tokens)
    (startsAbsent : DeclarativeGrammar.TopItemKindsAbsentAt
      (DeclarativeGrammar.sourceFileRootRemainder lexed.tokens)
      DeclarativeGrammar.ImportTerminatorTopItemStartKinds)
    (recovered : DeclarativeGrammar.TopItemRecoveryParses
      (DeclarativeGrammar.sourceFileRootRemainder lexed.tokens) item after)
    (atEnd : after.cursor = lexed.tokens.length)
    (filtered : DeclarativeGrammar.LexicalCascadeFilters file.content
      (lexed.diagnostics.map (·.span)) [item.span] kept) :
    parse file = .ok (singleRecoveryParseOutput file lexed item kept) :=
  (parse_eq_ok_singleRecovery_iff lexing clears startsAbsent recovered atEnd).mpr
    filtered

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.PublicPragmaRejectionOutputProperties
/-! Complete public output after a recognized pragma start rejects. Checked-item
events emitted before the failure survive boundary rollback; the final failure
is committed once and the complete mixed sequence is normalized independently. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- A rejected initial pragma contributes no AST item. Every lexical field,
all comments, and the exact proposed parser diagnostic list remain explicit. -/
def pragmaRejectionParseOutput (file : SourceFile) (lexed : LexedFile)
    (kept : List ParseDiagnostic) : ParseOutput := {
  parsed := {
    source := file.id
    span := SourceSpan.fullFile file
    items := []
    comments := lexed.comments
  }
  tokens := lexed.tokens
  lexicalDiagnostics := lexed.diagnostics
  parseDiagnostics := kept
}

private theorem parseLexed_pragmaRejection_raw_eq
    {file : SourceFile} {lexed : LexedFile}
    {marker : SourceSpan} {afterKeyword rejected : DeclarativeGrammar.Remainder}
    {diagnostic : ParseDiagnostic} {trace : List ParseDiagnostic}
    (accepted : DeclarativeGrammar.LexedFileValidationAccepts file lexed)
    (clears : DeclarativeGrammar.NestingClears lexed.tokens)
    (keywordParsed : DeclarativeGrammar.ExactTokenParses (.keyword .pragmaKw)
      (DeclarativeGrammar.sourceFileRootRemainder lexed.tokens) marker afterKeyword)
    (traced : DeclarativeGrammar.PragmaDeclTraceRejects file.id file.content.utf8ByteSize
      (DeclarativeGrammar.sourceFileRootRemainder lexed.tokens) rejected diagnostic trace) :
    parseLexed file lexed = .ok (pragmaRejectionParseOutput file lexed
      (filterParseDiagnostics file lexed.diagnostics (trace ++ [diagnostic]))) := by
  rcases (pragmaDecl_trace_reject_iff (input := State.initial file lexed)).mp traced with
    ⟨failure, failed, declarationResult, _remainderEq, reportEq, declarationTrace⟩
  have itemResult : FileInternals.parseItemsItem (State.initial file lexed) =
      .reject failure failed := by
    unfold FileInternals.parseItemsItem
    rw [FileInternals.topItem_eq_pragma_of_exactTokenParses
      (input := State.initial file lexed) keywordParsed]
    simp only [FileInternals.mapTopItem, declarationResult]
  have inside : (State.initial file lexed).cursor <
      (State.initial file lexed).window.endIndex := keywordParsed.1.1
  have starts := FileInternals.atTopItemStart_eq_true_of_pragmaToken
    (input := State.initial file lexed) keywordParsed
  rcases FileInternals.sourceFile_boundaryStop_trace_exact lexed.comments
      inside starts itemResult with ⟨output, result, _rewound, outputTrace⟩
  have traceEq : output.diagnostics = trace ++ [diagnostic] := by
    rw [outputTrace, declarationTrace, reportEq]
    simp only [State.initial, State.diagnostics, List.reverse_nil, List.nil_append]
  unfold parseLexed
  rw [(validateLexed_ok_iff_validationAccepts file lexed).mpr accepted]
  rw [(checkNesting_none_iff_nestingClears lexed.tokens).mpr clears]
  simp only [result, traceEq]
  rfl

/-- A leading pragma marker selects the file boundary-stop branch. Given its
independent rejection, a proposed complete output is equivalent to validation
and exact mixed filtering of prior item events followed by the committed report. -/
theorem parseLexed_eq_ok_pragmaRejection_iff
    {file : SourceFile} {lexed : LexedFile}
    {marker : SourceSpan} {afterKeyword rejected : DeclarativeGrammar.Remainder}
    {diagnostic : ParseDiagnostic} {trace kept : List ParseDiagnostic}
    (clears : DeclarativeGrammar.NestingClears lexed.tokens)
    (keywordParsed : DeclarativeGrammar.ExactTokenParses (.keyword .pragmaKw)
      (DeclarativeGrammar.sourceFileRootRemainder lexed.tokens) marker afterKeyword)
    (traced : DeclarativeGrammar.PragmaDeclTraceRejects file.id file.content.utf8ByteSize
      (DeclarativeGrammar.sourceFileRootRemainder lexed.tokens) rejected diagnostic trace) :
    parseLexed file lexed = .ok (pragmaRejectionParseOutput file lexed kept) ↔
      DeclarativeGrammar.LexedFileValidationAccepts file lexed ∧
        DeclarativeGrammar.ParseDiagnosticCascadeFilters file.content
          (lexed.diagnostics.map (·.span)) (trace ++ [diagnostic]) kept := by
  constructor
  · intro result
    have accepted :=
      (DeclarativeGrammar.lexedFileValidationAccepts_iff_validFor file lexed).mpr
        (parseLexed_ok_input_validFor file lexed _ result)
    rw [parseLexed_pragmaRejection_raw_eq accepted clears keywordParsed traced] at result
    have diagnosticsEq := congrArg ParseOutput.parseDiagnostics (Except.ok.inj result)
    exact ⟨accepted, (filterParseDiagnostics_eq_iff_cascadeFilters
      file lexed.diagnostics (trace ++ [diagnostic]) kept).mp diagnosticsEq⟩
  · rintro ⟨accepted, filtered⟩
    have filteredEq := filterParseDiagnostics_eq_of_cascadeFilters file lexed.diagnostics filtered
    simpa only [filteredEq] using
      parseLexed_pragmaRejection_raw_eq accepted clears keywordParsed traced

/-- Independent validation, branch selection, rejection, and filtering compute
all public output fields without assuming an executable declaration result. -/
theorem parseLexed_eq_ok_of_pragmaRejection
    {file : SourceFile} {lexed : LexedFile}
    {marker : SourceSpan} {afterKeyword rejected : DeclarativeGrammar.Remainder}
    {diagnostic : ParseDiagnostic} {trace kept : List ParseDiagnostic}
    (accepted : DeclarativeGrammar.LexedFileValidationAccepts file lexed)
    (clears : DeclarativeGrammar.NestingClears lexed.tokens)
    (keywordParsed : DeclarativeGrammar.ExactTokenParses (.keyword .pragmaKw)
      (DeclarativeGrammar.sourceFileRootRemainder lexed.tokens) marker afterKeyword)
    (traced : DeclarativeGrammar.PragmaDeclTraceRejects file.id file.content.utf8ByteSize
      (DeclarativeGrammar.sourceFileRootRemainder lexed.tokens) rejected diagnostic trace)
    (filtered : DeclarativeGrammar.ParseDiagnosticCascadeFilters file.content
      (lexed.diagnostics.map (·.span)) (trace ++ [diagnostic]) kept) :
    parseLexed file lexed = .ok (pragmaRejectionParseOutput file lexed kept) :=
  (parseLexed_eq_ok_pragmaRejection_iff clears keywordParsed traced).mpr ⟨accepted, filtered⟩

/-- Canonical lexing supplies validation. The independent mixed cascade grammar
then characterizes the complete source result, including retained lexical errors. -/
theorem parse_eq_ok_pragmaRejection_iff
    {file : SourceFile} {lexed : LexedFile}
    {marker : SourceSpan} {afterKeyword rejected : DeclarativeGrammar.Remainder}
    {diagnostic : ParseDiagnostic} {trace kept : List ParseDiagnostic}
    (lexing : Lexer.lex file = .ok lexed)
    (clears : DeclarativeGrammar.NestingClears lexed.tokens)
    (keywordParsed : DeclarativeGrammar.ExactTokenParses (.keyword .pragmaKw)
      (DeclarativeGrammar.sourceFileRootRemainder lexed.tokens) marker afterKeyword)
    (traced : DeclarativeGrammar.PragmaDeclTraceRejects file.id file.content.utf8ByteSize
      (DeclarativeGrammar.sourceFileRootRemainder lexed.tokens) rejected diagnostic trace) :
    parse file = .ok (pragmaRejectionParseOutput file lexed kept) ↔
      DeclarativeGrammar.ParseDiagnosticCascadeFilters file.content
        (lexed.diagnostics.map (·.span)) (trace ++ [diagnostic]) kept := by
  have accepted :=
    (DeclarativeGrammar.lexedFileValidationAccepts_iff_validFor file lexed).mpr
      (Lexer.lex_ok_validFor file lexed lexing)
  constructor
  · intro result
    have parsing : parseLexed file lexed =
        .ok (pragmaRejectionParseOutput file lexed kept) := by
      unfold parse at result
      rw [lexing] at result
      cases executed : parseLexed file lexed with
      | ok output => simp only [executed] at result; cases result; rfl
      | error error => simp only [executed] at result; contradiction
    exact ((parseLexed_eq_ok_pragmaRejection_iff clears keywordParsed traced).mp parsing).2
  · intro filtered
    have parsing := parseLexed_eq_ok_of_pragmaRejection accepted clears keywordParsed traced filtered
    simp only [parse, lexing, parsing]

/-- A recognized rejected pragma keeps its checked-item events before the
committed failure; the independently filtered list determines the entire result. -/
theorem parse_eq_ok_of_pragmaRejection
    {file : SourceFile} {lexed : LexedFile}
    {marker : SourceSpan} {afterKeyword rejected : DeclarativeGrammar.Remainder}
    {diagnostic : ParseDiagnostic} {trace kept : List ParseDiagnostic}
    (lexing : Lexer.lex file = .ok lexed)
    (clears : DeclarativeGrammar.NestingClears lexed.tokens)
    (keywordParsed : DeclarativeGrammar.ExactTokenParses (.keyword .pragmaKw)
      (DeclarativeGrammar.sourceFileRootRemainder lexed.tokens) marker afterKeyword)
    (traced : DeclarativeGrammar.PragmaDeclTraceRejects file.id file.content.utf8ByteSize
      (DeclarativeGrammar.sourceFileRootRemainder lexed.tokens) rejected diagnostic trace)
    (filtered : DeclarativeGrammar.ParseDiagnosticCascadeFilters file.content
      (lexed.diagnostics.map (·.span)) (trace ++ [diagnostic]) kept) :
    parse file = .ok (pragmaRejectionParseOutput file lexed kept) :=
  (parse_eq_ok_pragmaRejection_iff lexing clears keywordParsed traced).mpr filtered

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.PublicPragmaSuccessOutputProperties
/-! Independent successful pragma grammar and ordered traces determine one
complete public file, including mixed-diagnostic normalization. The final
public premises contain no executable item or declaration reply. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Complete singleton-pragma output with canonical comment attachment and
the exact retained diagnostic sequence, not merely its projected spans. -/
def singlePragmaParseOutput (file : SourceFile) (lexed : LexedFile)
    (declaration : PragmaDecl) (kept : List ParseDiagnostic) : ParseOutput := {
  parsed := {
    source := file.id
    span := SourceSpan.fullFile file
    items := [Trivia.attachTopItemComments file lexed.comments
      (FileInternals.wrapPragma declaration)]
    comments := lexed.comments
  }
  tokens := lexed.tokens
  lexicalDiagnostics := lexed.diagnostics
  parseDiagnostics := kept
}

private theorem pragmaDeclOrdinary_has_marker
    {input after : DeclarativeGrammar.Remainder} {declaration : PragmaDecl}
    (parsed : DeclarativeGrammar.PragmaDeclOrdinaryParses input declaration after) :
    ∃ marker afterKeyword,
      DeclarativeGrammar.ExactTokenParses (.keyword .pragmaKw) input marker afterKeyword := by
  cases parsed with
  | parsed marker _ keywordParsed _ _ _ => exact ⟨marker, _, keywordParsed⟩

private theorem parseLexed_singlePragma_raw_eq
    {file : SourceFile} {lexed : LexedFile} {declaration : PragmaDecl}
    {after : DeclarativeGrammar.Remainder} {trace : List ParseDiagnostic}
    (accepted : DeclarativeGrammar.LexedFileValidationAccepts file lexed)
    (clears : DeclarativeGrammar.NestingClears lexed.tokens)
    (parsed : DeclarativeGrammar.PragmaDeclTraceParses
      (DeclarativeGrammar.sourceFileRootRemainder lexed.tokens) declaration after trace)
    (atEnd : after.cursor = lexed.tokens.length) :
    parseLexed file lexed = .ok (singlePragmaParseOutput file lexed declaration
      (filterParseDiagnostics file lexed.diagnostics trace)) := by
  rcases (pragmaDecl_trace_success_iff (input := State.initial file lexed)).mp parsed with
    ⟨next, declarationResult, remainderEq, declarationTrace⟩
  rcases pragmaDeclOrdinary_has_marker parsed.1 with ⟨marker, afterKeyword, keywordParsed⟩
  have itemResult : FileInternals.parseItemsItem (State.initial file lexed) =
      .ok (FileInternals.wrapPragma declaration) next := by
    unfold FileInternals.parseItemsItem
    rw [FileInternals.topItem_eq_pragma_of_exactTokenParses
      (input := State.initial file lexed) keywordParsed]
    simp only [FileInternals.mapTopItem, declarationResult]
  have nextAtEnd : next.cursor = (State.initial file lexed).window.endIndex :=
    (congrArg DeclarativeGrammar.Remainder.cursor remainderEq).trans atEnd
  rcases FileInternals.sourceFile_singleSuccessToEnd_exact lexed.comments
      itemResult nextAtEnd with ⟨output, result, _final, outputTrace⟩
  have traceEq : output.diagnostics = trace := by
    rw [outputTrace, declarationTrace]
    simp only [State.initial, State.diagnostics, List.reverse_nil, List.nil_append]
  unfold parseLexed
  rw [(validateLexed_ok_iff_validationAccepts file lexed).mpr accepted]
  rw [(checkNesting_none_iff_nestingClears lexed.tokens).mpr clears]
  simp only [result, traceEq]
  rfl

/-- A root pragma derivation reaching the end determines the complete public
output iff validation accepts and the independent mixed filter retains exactly
the proposed diagnostics, including their payloads, order, and multiplicity. -/
theorem parseLexed_eq_ok_singlePragma_iff
    {file : SourceFile} {lexed : LexedFile} {declaration : PragmaDecl}
    {after : DeclarativeGrammar.Remainder} {trace kept : List ParseDiagnostic}
    (clears : DeclarativeGrammar.NestingClears lexed.tokens)
    (parsed : DeclarativeGrammar.PragmaDeclTraceParses
      (DeclarativeGrammar.sourceFileRootRemainder lexed.tokens) declaration after trace)
    (atEnd : after.cursor = lexed.tokens.length) :
    parseLexed file lexed = .ok (singlePragmaParseOutput file lexed declaration kept) ↔
      DeclarativeGrammar.LexedFileValidationAccepts file lexed ∧
        DeclarativeGrammar.ParseDiagnosticCascadeFilters file.content
          (lexed.diagnostics.map (·.span)) trace kept := by
  constructor
  · intro result
    have accepted :=
      (DeclarativeGrammar.lexedFileValidationAccepts_iff_validFor file lexed).mpr
        (parseLexed_ok_input_validFor file lexed _ result)
    have expected := parseLexed_singlePragma_raw_eq accepted clears parsed atEnd
    rw [expected] at result
    have diagnosticsEq := congrArg ParseOutput.parseDiagnostics (Except.ok.inj result)
    exact ⟨accepted, (filterParseDiagnostics_eq_iff_cascadeFilters
      file lexed.diagnostics trace kept).mp diagnosticsEq⟩
  · rintro ⟨accepted, filtered⟩
    have filteredEq := filterParseDiagnostics_eq_of_cascadeFilters file lexed.diagnostics filtered
    simpa only [filteredEq] using parseLexed_singlePragma_raw_eq accepted clears parsed atEnd

/-- Independent grammar, trace, validation, and mixed filtering compute the
entire singleton-pragma token-to-file output. -/
theorem parseLexed_eq_ok_of_singlePragma
    {file : SourceFile} {lexed : LexedFile} {declaration : PragmaDecl}
    {after : DeclarativeGrammar.Remainder} {trace kept : List ParseDiagnostic}
    (accepted : DeclarativeGrammar.LexedFileValidationAccepts file lexed)
    (clears : DeclarativeGrammar.NestingClears lexed.tokens)
    (parsed : DeclarativeGrammar.PragmaDeclTraceParses
      (DeclarativeGrammar.sourceFileRootRemainder lexed.tokens) declaration after trace)
    (atEnd : after.cursor = lexed.tokens.length)
    (filtered : DeclarativeGrammar.ParseDiagnosticCascadeFilters file.content
      (lexed.diagnostics.map (·.span)) trace kept) :
    parseLexed file lexed = .ok (singlePragmaParseOutput file lexed declaration kept) :=
  (parseLexed_eq_ok_singlePragma_iff clears parsed atEnd).mpr ⟨accepted, filtered⟩

/-- Canonical lexing supplies validation, leaving the independent mixed filter
as the exact characterization of the complete source-to-file output. -/
theorem parse_eq_ok_singlePragma_iff
    {file : SourceFile} {lexed : LexedFile} {declaration : PragmaDecl}
    {after : DeclarativeGrammar.Remainder} {trace kept : List ParseDiagnostic}
    (lexing : Lexer.lex file = .ok lexed)
    (clears : DeclarativeGrammar.NestingClears lexed.tokens)
    (parsed : DeclarativeGrammar.PragmaDeclTraceParses
      (DeclarativeGrammar.sourceFileRootRemainder lexed.tokens) declaration after trace)
    (atEnd : after.cursor = lexed.tokens.length) :
    parse file = .ok (singlePragmaParseOutput file lexed declaration kept) ↔
      DeclarativeGrammar.ParseDiagnosticCascadeFilters file.content
        (lexed.diagnostics.map (·.span)) trace kept := by
  have accepted :=
    (DeclarativeGrammar.lexedFileValidationAccepts_iff_validFor file lexed).mpr
      (Lexer.lex_ok_validFor file lexed lexing)
  constructor
  · intro result
    have parsing : parseLexed file lexed =
        .ok (singlePragmaParseOutput file lexed declaration kept) := by
      unfold parse at result
      rw [lexing] at result
      cases executed : parseLexed file lexed with
      | ok output => simp only [executed] at result; cases result; rfl
      | error error => simp only [executed] at result; contradiction
    exact ((parseLexed_eq_ok_singlePragma_iff clears parsed atEnd).mp parsing).2
  · intro filtered
    have parsing := parseLexed_eq_ok_of_singlePragma accepted clears parsed atEnd filtered
    simp only [parse, lexing, parsing]

/-- The independent root pragma and mixed diagnostic derivations also compute
the complete source result, without an assumed parser success. -/
theorem parse_eq_ok_of_singlePragma
    {file : SourceFile} {lexed : LexedFile} {declaration : PragmaDecl}
    {after : DeclarativeGrammar.Remainder} {trace kept : List ParseDiagnostic}
    (lexing : Lexer.lex file = .ok lexed)
    (clears : DeclarativeGrammar.NestingClears lexed.tokens)
    (parsed : DeclarativeGrammar.PragmaDeclTraceParses
      (DeclarativeGrammar.sourceFileRootRemainder lexed.tokens) declaration after trace)
    (atEnd : after.cursor = lexed.tokens.length)
    (filtered : DeclarativeGrammar.ParseDiagnosticCascadeFilters file.content
      (lexed.diagnostics.map (·.span)) trace kept) :
    parse file = .ok (singlePragmaParseOutput file lexed declaration kept) :=
  (parse_eq_ok_singlePragma_iff lexing clears parsed atEnd).mpr filtered

/-- Every successful pragma event is a protected checked-identifier report,
so no lexical error can change its independently determined trace. -/
theorem parseLexed_eq_ok_of_singlePragmaTrace
    {file : SourceFile} {lexed : LexedFile} {declaration : PragmaDecl}
    {after : DeclarativeGrammar.Remainder} {trace : List ParseDiagnostic}
    (accepted : DeclarativeGrammar.LexedFileValidationAccepts file lexed)
    (clears : DeclarativeGrammar.NestingClears lexed.tokens)
    (parsed : DeclarativeGrammar.PragmaDeclTraceParses
      (DeclarativeGrammar.sourceFileRootRemainder lexed.tokens) declaration after trace)
    (atEnd : after.cursor = lexed.tokens.length) :
    parseLexed file lexed = .ok (singlePragmaParseOutput file lexed declaration trace) :=
  parseLexed_eq_ok_of_singlePragma accepted clears parsed atEnd
    (parsed.cascadeFilters file.content (lexed.diagnostics.map (·.span)))

/-- Canonical lexing and the independent protected pragma trace suffice to
compute all public fields, with no separate filter or validity premise. -/
theorem parse_eq_ok_of_singlePragmaTrace
    {file : SourceFile} {lexed : LexedFile} {declaration : PragmaDecl}
    {after : DeclarativeGrammar.Remainder} {trace : List ParseDiagnostic}
    (lexing : Lexer.lex file = .ok lexed)
    (clears : DeclarativeGrammar.NestingClears lexed.tokens)
    (parsed : DeclarativeGrammar.PragmaDeclTraceParses
      (DeclarativeGrammar.sourceFileRootRemainder lexed.tokens) declaration after trace)
    (atEnd : after.cursor = lexed.tokens.length) :
    parse file = .ok (singlePragmaParseOutput file lexed declaration trace) :=
  parse_eq_ok_of_singlePragma lexing clears parsed atEnd
    (parsed.cascadeFilters file.content (lexed.diagnostics.map (·.span)))

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.PublicPragmaSequenceOutputProperties
/-! Complete public outputs of independent pragma-only windows, including the
empty sequence. Written declaration order and complete protected traces survive
unchanged; no executable declaration or file reply occurs in the premises. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Wrap every declaration and attach its comments without changing source
order. All lexical fields and the complete proposed diagnostic list are retained. -/
def pragmaSequenceParseOutput (file : SourceFile) (lexed : LexedFile)
    (declarations : List PragmaDecl) (kept : List ParseDiagnostic) : ParseOutput := {
  parsed := {
    source := file.id
    span := SourceSpan.fullFile file
    items := (declarations.map FileInternals.wrapPragma).map
      (Trivia.attachTopItemComments file lexed.comments)
    comments := lexed.comments
  }
  tokens := lexed.tokens
  lexicalDiagnostics := lexed.diagnostics
  parseDiagnostics := kept
}

/-- Independent root grammar and validation determine every public field.
Successful pragma events are protected, regardless of lexical error locations. -/
theorem parseLexed_eq_ok_of_pragmaSequence
    {file : SourceFile} {lexed : LexedFile} {declarations : List PragmaDecl}
    {after : DeclarativeGrammar.Remainder} {trace : List ParseDiagnostic}
    (accepted : DeclarativeGrammar.LexedFileValidationAccepts file lexed)
    (clears : DeclarativeGrammar.NestingClears lexed.tokens)
    (parsed : DeclarativeGrammar.PragmaSequenceTraceParses
      (DeclarativeGrammar.sourceFileRootRemainder lexed.tokens) declarations after trace) :
    parseLexed file lexed = .ok (pragmaSequenceParseOutput file lexed declarations trace) := by
  rcases FileInternals.sourceFile_pragmaSequence_trace lexed.comments
      (input := State.initial file lexed) parsed with
    ⟨output, result, _afterEq, outputTrace⟩
  have traceEq : output.diagnostics = trace := by
    simpa only [State.initial, State.diagnostics, List.reverse_nil, List.nil_append]
      using outputTrace
  have filtered := filterParseDiagnostics_eq_of_cascadeFilters file lexed.diagnostics
    (parsed.cascadeFilters file.content (lexed.diagnostics.map (·.span)))
  unfold parseLexed
  rw [(validateLexed_ok_iff_validationAccepts file lexed).mpr accepted]
  rw [(checkNesting_none_iff_nestingClears lexed.tokens).mpr clears]
  simp only [result, traceEq, filtered]
  rfl

/-- For a fixed independent complete pragma derivation, public success with a
proposed diagnostic list is exactly validation plus equality to the full trace. -/
theorem parseLexed_eq_ok_pragmaSequence_iff
    {file : SourceFile} {lexed : LexedFile} {declarations : List PragmaDecl}
    {after : DeclarativeGrammar.Remainder} {trace kept : List ParseDiagnostic}
    (clears : DeclarativeGrammar.NestingClears lexed.tokens)
    (parsed : DeclarativeGrammar.PragmaSequenceTraceParses
      (DeclarativeGrammar.sourceFileRootRemainder lexed.tokens) declarations after trace) :
    parseLexed file lexed = .ok (pragmaSequenceParseOutput file lexed declarations kept) ↔
      DeclarativeGrammar.LexedFileValidationAccepts file lexed ∧ kept = trace := by
  constructor
  · intro result
    have accepted :=
      (DeclarativeGrammar.lexedFileValidationAccepts_iff_validFor file lexed).mpr
        (parseLexed_ok_input_validFor file lexed _ result)
    rw [parseLexed_eq_ok_of_pragmaSequence accepted clears parsed] at result
    have traceEq := congrArg ParseOutput.parseDiagnostics (Except.ok.inj result)
    exact ⟨accepted, traceEq.symm⟩
  · rintro ⟨accepted, rfl⟩
    exact parseLexed_eq_ok_of_pragmaSequence accepted clears parsed

/-- Canonical lexical analysis supplies validation for the independent pragma
sequence. The result includes comments, lexical diagnostics, and all item events. -/
theorem parse_eq_ok_of_pragmaSequence
    {file : SourceFile} {lexed : LexedFile} {declarations : List PragmaDecl}
    {after : DeclarativeGrammar.Remainder} {trace : List ParseDiagnostic}
    (lexing : Lexer.lex file = .ok lexed)
    (clears : DeclarativeGrammar.NestingClears lexed.tokens)
    (parsed : DeclarativeGrammar.PragmaSequenceTraceParses
      (DeclarativeGrammar.sourceFileRootRemainder lexed.tokens) declarations after trace) :
    parse file = .ok (pragmaSequenceParseOutput file lexed declarations trace) := by
  have accepted := (DeclarativeGrammar.lexedFileValidationAccepts_iff_validFor file lexed).mpr
    (Lexer.lex_ok_validFor file lexed lexing)
  have parsing := parseLexed_eq_ok_of_pragmaSequence accepted clears parsed
  simp only [parse, lexing, parsing]

/-- The complete source result has exactly the independently ordered pragma
trace, including duplicate reports and every payload, not just equal spans. -/
theorem parse_eq_ok_pragmaSequence_iff
    {file : SourceFile} {lexed : LexedFile} {declarations : List PragmaDecl}
    {after : DeclarativeGrammar.Remainder} {trace kept : List ParseDiagnostic}
    (lexing : Lexer.lex file = .ok lexed)
    (clears : DeclarativeGrammar.NestingClears lexed.tokens)
    (parsed : DeclarativeGrammar.PragmaSequenceTraceParses
      (DeclarativeGrammar.sourceFileRootRemainder lexed.tokens) declarations after trace) :
    parse file = .ok (pragmaSequenceParseOutput file lexed declarations kept) ↔ kept = trace := by
  constructor
  · intro result
    rw [parse_eq_ok_of_pragmaSequence lexing clears parsed] at result
    exact (congrArg ParseOutput.parseDiagnostics (Except.ok.inj result)).symm
  · intro same
    subst kept
    exact parse_eq_ok_of_pragmaSequence lexing clears parsed

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.PublicPragmaPrefixBoundaryOutputProperties
/-! Complete public outputs of successful pragma prefixes followed by a
recognized rejected pragma. The prefix AST survives while the final report is
committed after all earlier events and normalized by the mixed cascade grammar. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

private theorem parseLexed_pragmaPrefixBoundary_raw_eq
    {file : SourceFile} {lexed : LexedFile} {declarations : List PragmaDecl}
    {stopped : DeclarativeGrammar.Remainder} {diagnostic : ParseDiagnostic}
    {trace : List ParseDiagnostic}
    (accepted : DeclarativeGrammar.LexedFileValidationAccepts file lexed)
    (clears : DeclarativeGrammar.NestingClears lexed.tokens)
    (parsed : DeclarativeGrammar.PragmaPrefixBoundaryTraceParses
      file.id file.content.utf8ByteSize
      (DeclarativeGrammar.sourceFileRootRemainder lexed.tokens)
      declarations stopped diagnostic trace) :
    parseLexed file lexed = .ok (pragmaSequenceParseOutput file lexed declarations
      (filterParseDiagnostics file lexed.diagnostics (trace ++ [diagnostic]))) := by
  rcases FileInternals.sourceFile_pragmaPrefixBoundary_trace lexed.comments
      (input := State.initial file lexed) parsed with
    ⟨output, result, _stoppedEq, outputTrace⟩
  have traceEq : output.diagnostics = trace ++ [diagnostic] := by
    simpa only [State.initial, State.diagnostics, List.reverse_nil, List.nil_append]
      using outputTrace
  unfold parseLexed
  rw [(validateLexed_ok_iff_validationAccepts file lexed).mpr accepted]
  rw [(checkNesting_none_iff_nestingClears lexed.tokens).mpr clears]
  simp only [result, traceEq]
  rfl

/-- The independent prefix grammar fixes every successful item and the
recognized stopping boundary. The complete output is exactly validation plus
mixed filtering of all pre-failure events followed by the final report. -/
theorem parseLexed_eq_ok_pragmaPrefixBoundary_iff
    {file : SourceFile} {lexed : LexedFile} {declarations : List PragmaDecl}
    {stopped : DeclarativeGrammar.Remainder} {diagnostic : ParseDiagnostic}
    {trace kept : List ParseDiagnostic}
    (clears : DeclarativeGrammar.NestingClears lexed.tokens)
    (parsed : DeclarativeGrammar.PragmaPrefixBoundaryTraceParses
      file.id file.content.utf8ByteSize
      (DeclarativeGrammar.sourceFileRootRemainder lexed.tokens)
      declarations stopped diagnostic trace) :
    parseLexed file lexed = .ok (pragmaSequenceParseOutput file lexed declarations kept) ↔
      DeclarativeGrammar.LexedFileValidationAccepts file lexed ∧
        DeclarativeGrammar.ParseDiagnosticCascadeFilters file.content
          (lexed.diagnostics.map (·.span)) (trace ++ [diagnostic]) kept := by
  constructor
  · intro result
    have accepted :=
      (DeclarativeGrammar.lexedFileValidationAccepts_iff_validFor file lexed).mpr
        (parseLexed_ok_input_validFor file lexed _ result)
    rw [parseLexed_pragmaPrefixBoundary_raw_eq accepted clears parsed] at result
    have diagnosticsEq := congrArg ParseOutput.parseDiagnostics (Except.ok.inj result)
    exact ⟨accepted, (filterParseDiagnostics_eq_iff_cascadeFilters
      file lexed.diagnostics (trace ++ [diagnostic]) kept).mp diagnosticsEq⟩
  · rintro ⟨accepted, filtered⟩
    have filteredEq := filterParseDiagnostics_eq_of_cascadeFilters file lexed.diagnostics filtered
    simpa only [filteredEq] using
      parseLexed_pragmaPrefixBoundary_raw_eq accepted clears parsed

/-- Validation, independent prefix/rejection syntax, and independent filtering
determine all lexical fields, comment-attached prefix items, and diagnostics. -/
theorem parseLexed_eq_ok_of_pragmaPrefixBoundary
    {file : SourceFile} {lexed : LexedFile} {declarations : List PragmaDecl}
    {stopped : DeclarativeGrammar.Remainder} {diagnostic : ParseDiagnostic}
    {trace kept : List ParseDiagnostic}
    (accepted : DeclarativeGrammar.LexedFileValidationAccepts file lexed)
    (clears : DeclarativeGrammar.NestingClears lexed.tokens)
    (parsed : DeclarativeGrammar.PragmaPrefixBoundaryTraceParses
      file.id file.content.utf8ByteSize
      (DeclarativeGrammar.sourceFileRootRemainder lexed.tokens)
      declarations stopped diagnostic trace)
    (filtered : DeclarativeGrammar.ParseDiagnosticCascadeFilters file.content
      (lexed.diagnostics.map (·.span)) (trace ++ [diagnostic]) kept) :
    parseLexed file lexed = .ok (pragmaSequenceParseOutput file lexed declarations kept) :=
  (parseLexed_eq_ok_pragmaPrefixBoundary_iff clears parsed).mpr ⟨accepted, filtered⟩

/-- Canonical lexing supplies validation. Filtering characterizes the complete
source result without dropping retained prefix items or lexical diagnostics. -/
theorem parse_eq_ok_pragmaPrefixBoundary_iff
    {file : SourceFile} {lexed : LexedFile} {declarations : List PragmaDecl}
    {stopped : DeclarativeGrammar.Remainder} {diagnostic : ParseDiagnostic}
    {trace kept : List ParseDiagnostic}
    (lexing : Lexer.lex file = .ok lexed)
    (clears : DeclarativeGrammar.NestingClears lexed.tokens)
    (parsed : DeclarativeGrammar.PragmaPrefixBoundaryTraceParses
      file.id file.content.utf8ByteSize
      (DeclarativeGrammar.sourceFileRootRemainder lexed.tokens)
      declarations stopped diagnostic trace) :
    parse file = .ok (pragmaSequenceParseOutput file lexed declarations kept) ↔
      DeclarativeGrammar.ParseDiagnosticCascadeFilters file.content
        (lexed.diagnostics.map (·.span)) (trace ++ [diagnostic]) kept := by
  have accepted :=
    (DeclarativeGrammar.lexedFileValidationAccepts_iff_validFor file lexed).mpr
      (Lexer.lex_ok_validFor file lexed lexing)
  constructor
  · intro result
    have parsing : parseLexed file lexed =
        .ok (pragmaSequenceParseOutput file lexed declarations kept) := by
      unfold parse at result
      rw [lexing] at result
      cases executed : parseLexed file lexed with
      | ok output => simp only [executed] at result; cases result; rfl
      | error error => simp only [executed] at result; contradiction
    exact ((parseLexed_eq_ok_pragmaPrefixBoundary_iff clears parsed).mp parsing).2
  · intro filtered
    have parsing := parseLexed_eq_ok_of_pragmaPrefixBoundary accepted clears parsed filtered
    simp only [parse, lexing, parsing]

/-- The rejected declaration adds no item; its pre-failure events and final
report follow the successful prefix events in the independently filtered list. -/
theorem parse_eq_ok_of_pragmaPrefixBoundary
    {file : SourceFile} {lexed : LexedFile} {declarations : List PragmaDecl}
    {stopped : DeclarativeGrammar.Remainder} {diagnostic : ParseDiagnostic}
    {trace kept : List ParseDiagnostic}
    (lexing : Lexer.lex file = .ok lexed)
    (clears : DeclarativeGrammar.NestingClears lexed.tokens)
    (parsed : DeclarativeGrammar.PragmaPrefixBoundaryTraceParses
      file.id file.content.utf8ByteSize
      (DeclarativeGrammar.sourceFileRootRemainder lexed.tokens)
      declarations stopped diagnostic trace)
    (filtered : DeclarativeGrammar.ParseDiagnosticCascadeFilters file.content
      (lexed.diagnostics.map (·.span)) (trace ++ [diagnostic]) kept) :
    parse file = .ok (pragmaSequenceParseOutput file lexed declarations kept) :=
  (parse_eq_ok_pragmaPrefixBoundary_iff lexing clears parsed).mpr filtered

end Solcore.Syntax.Parser
end
