import Solcore.Syntax.DeclarativeQualifiedNameTraceOutcomeProperties
import Solcore.Syntax.Parser.QualifiedNameRejectionTraceStateProperties
import Solcore.Syntax.Parser.ParseDiagnosticCascadeStabilityProperties
import Solcore.Syntax.Lexer

/-! A canonical rejected maximal dotted name retains both preceding checked
components. The selected final dot is consumed, the plus stays current, and the
identifier report is still uncommitted in every parse context and phase. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxCanonicalQualifiedNameRejectionTraceExamples

open Solcore.Syntax Solcore.Syntax.Parser Solcore.Syntax.DeclarativeGrammar

private def source : SourceId := { origin := .main, path := "qualified-name-rejection-trace.sol" }
private def file : SourceFile := { id := source, content := "a-b.c-d.+ tail" }
private def span (first last : Nat) : SourceSpan := { source, startByte := first, endByte := last }
private def nameA : Identifier := { span := span 0 3, value := "a-b" }
private def nameC : Identifier := { span := span 4 7, value := "c-d" }
private def nameToken (name : Identifier) : Token := { span := name.span, value := .identifier name.value }
private def hyphen (name : Identifier) : ParseDiagnostic := { span := name.span, kind := .invalidIdentifierHyphen name.value }
private def tokens : List Token := [nameToken nameA, { span := span 3 4, value := .symbol .dot },
  nameToken nameC, { span := span 7 8, value := .symbol .dot },
  { span := span 8 9, value := .symbol .plus }, { span := span 10 14, value := .identifier "tail" }]
private def lexed : LexedFile := { source, tokens, comments := [], diagnostics := [] }
private def remaining (cursor : Nat) : Remainder := { tokens := tokens.toArray, endIndex := 6, cursor }
private def failure (context : ParseContext) : Failure := {
  span := span 8 9, found := some (.symbol .plus), expected := { head := .identifier, tail := [] }, context
}
private def events : List ParseDiagnostic := [hyphen nameA, hyphen nameC]

private theorem rejected_trace (context : ParseContext) :
    QualifiedNameTraceRejects context source 14 (remaining 0) (remaining 4) (failure context).toDiagnostic events := by
  have last : DottedIdentifierTailTraceRejects context source 14 (remaining 3) (remaining 4)
      (failure context).toDiagnostic [] :=
    .componentRejected (span 7 8) ⟨⟨by decide, rfl⟩, rfl⟩
      (by simp [IdentifierAbsentAt, TokenAt, remaining, tokens])
      (.reported (.token (current := { span := span 8 9, value := .symbol .plus }) ⟨by decide, rfl⟩))
  have rest : DottedIdentifierTailTraceRejects context source 14 (remaining 1) (remaining 4)
      (failure context).toDiagnostic [hyphen nameC] :=
    .laterRejected (span 3 4) (afterDot := remaining 2) (afterComponent := remaining 3)
      ⟨⟨by decide, rfl⟩, rfl⟩
      (.parsed ⟨⟨by decide, rfl⟩, rfl, rfl, rfl⟩ (.hyphen (by unfold IdentifierHyphenSpelling nameC; decide))) last
  have head : IdentifierTraceParses (remaining 0) nameA (remaining 1) [hyphen nameA] :=
    .parsed ⟨⟨by decide, rfl⟩, rfl, rfl, rfl⟩ (.hyphen (by unfold IdentifierHyphenSpelling nameA; decide))
  exact .tailRejected head rest

set_option maxRecDepth 16384 in
set_option maxHeartbeats 1600000 in
theorem rejected_names_lex : Lexer.lex file = .ok lexed := by
  have checked : (Lexer.lex file).toOption = some lexed := by decide +kernel
  cases result : Lexer.lex file with
  | error error => simp only [result, Except.toOption] at checked; contradiction
  | ok actual => simp only [result, Except.toOption] at checked; cases checked; rfl

theorem canonical_names_rejected (context : ParseContext) (phase : ParserPhase)
    (prior : List ParseDiagnostic) :
    ∃ actualLexed output, Lexer.lex file = .ok actualLexed ∧
      qualifiedName context phase { State.initial file actualLexed with diagnosticsRev := prior.reverse } =
        .reject (failure context) output ∧ output.declarativeRemainder = remaining 4 ∧
      output.diagnostics = prior ++ events ∧ output.file = file ∧
      output.window = { endIndex := 6, endByte := 14 } ∧
      output.peek? = some { span := span 8 9, value := .symbol .plus } ∧
      output.tokens[5]? = some { span := span 10 14, value := .identifier "tail" } := by
  let input : State := { State.initial file lexed with diagnosticsRev := prior.reverse }
  have rejection : QualifiedNameTraceRejects context input.file.id input.window.endByte input.declarativeRemainder
      (remaining 4) (failure context).toDiagnostic events := rejected_trace context
  have result := qualifiedName_eq_reject_of_trace context phase rejection
  refine ⟨lexed, _, rejected_names_lex, result, rfl, ?_, rfl, rfl, rfl, rfl⟩
  simp only [State.diagnostics, input, List.reverse_append, List.reverse_reverse]

/-- Initial rejection consumes nothing, even with a malformed carrier or
window. Context-specific expected/found/span data and every prior event remain. -/
theorem first_rejection_preserves_every_state_field (context : ParseContext) (phase : ParserPhase)
    {input : State} {failure : Failure} (absent : IdentifierAbsentAt input.declarativeRemainder)
    (reported : RejectAtReports input.file.id input.window.endByte { head := .identifier, tail := [] }
      context input.declarativeRemainder failure.toDiagnostic) :
    qualifiedName context phase input = .reject failure input :=
  qualifiedName_eq_reject_of_trace context phase (.firstRejected absent reported)

theorem preceding_name_events_survive_filtering (context : ParseContext)
    (normalizationFile : SourceFile) (lexical : List LexicalDiagnostic) (prior : List ParseDiagnostic) :
    filterParseDiagnostics normalizationFile lexical (prior ++ events) =
      filterParseDiagnostics normalizationFile lexical prior ++ events := by
  rw [filterParseDiagnostics_append]
  exact congrArg (fun suffix => filterParseDiagnostics normalizationFile lexical prior ++ suffix)
    (filterParseDiagnostics_eq_of_cascadeFilters normalizationFile lexical ((rejected_trace context).cascadeFilters _ _))

end Solcore.Test.SyntaxCanonicalQualifiedNameRejectionTraceExamples
