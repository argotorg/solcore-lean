import Solcore.Syntax.Parser.DiagnosticCascadeProperties
import Solcore.Syntax.Parser.LexedValidationOutcomeSoundnessProperties
import Solcore.Syntax.Parser.PublicSourceFileExecutionWitnessProperties
import Solcore.Syntax.Parser.SourceFileSingleRecoveryTraceProperties
import Solcore.Syntax.Parser.TopItemRecoveryTraceCompletenessProperties

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
