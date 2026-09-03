import Solcore.Syntax.Parser.PragmaPrefixBoundaryTraceProperties
import Solcore.Syntax.Parser.PublicPragmaSequenceOutputProperties

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
