import Solcore.Syntax.DeclarativePragmaSequenceCascadeProperties
import Solcore.Syntax.Parser.LexedValidation
import Solcore.Syntax.Parser.ParseDiagnosticCascadeProperties
import Solcore.Syntax.Parser.PragmaSequenceTraceProperties
import Solcore.Syntax.Parser.PublicSourceFileExecutionWitnessProperties

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
