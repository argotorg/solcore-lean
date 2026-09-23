import Solcore.Syntax.DeclarativePragmaCascadeProperties
import Solcore.Syntax.Parser.LexedValidation
import Solcore.Syntax.Parser.ParseDiagnosticCascadeProperties
import Solcore.Syntax.Parser.PragmaDeclarationTraceProperties
import Solcore.Syntax.Parser.PragmaKeywordExecutionProperties
import Solcore.Syntax.Parser.PublicSourceFileExecutionWitnessProperties
import Solcore.Syntax.Parser.SourceFileSingleSuccessTraceProperties

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
