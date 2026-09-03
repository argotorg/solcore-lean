import Solcore.Syntax.Parser.LexedValidationOutcomeSoundnessProperties
import Solcore.Syntax.Parser.ParseDiagnosticCascadeProperties
import Solcore.Syntax.Parser.PragmaDeclarationRejectionTraceCompletenessProperties
import Solcore.Syntax.Parser.PragmaKeywordExecutionProperties
import Solcore.Syntax.Parser.PublicSourceFileExecutionWitnessProperties
import Solcore.Syntax.Parser.SourceFileBoundaryStopTraceProperties

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
