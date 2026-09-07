import Solcore.Syntax.Parser.QualifiedNameTraceCorrespondenceProperties
import Solcore.Syntax.Parser.ParseDiagnosticCascadeStabilityProperties
import Solcore.Syntax.Lexer

/-! Canonical checked qualified names retain forward components, each located
spelling event, arbitrary earlier events, and the unread following identifier. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxQualifiedNameSuccessTraceProperties

open Solcore.Syntax Solcore.Syntax.Parser Solcore.Syntax.DeclarativeGrammar

private def source : SourceId := { origin := .main, path := "qualified-name-trace.sol" }
private def file : SourceFile := { id := source, content := "a-b.c-d.e-f tail" }
private def span (first last : Nat) : SourceSpan := { source, startByte := first, endByte := last }
private def nameA : Identifier := { span := span 0 3, value := "a-b" }
private def nameC : Identifier := { span := span 4 7, value := "c-d" }
private def nameE : Identifier := { span := span 8 11, value := "e-f" }
private def token (name : Identifier) : Token := { span := name.span, value := .identifier name.value }
private def hyphen (name : Identifier) : ParseDiagnostic := { span := name.span, kind := .invalidIdentifierHyphen name.value }
private def tokens : List Token := [token nameA, { span := span 3 4, value := .symbol .dot },
  token nameC, { span := span 7 8, value := .symbol .dot }, token nameE,
  { span := span 12 16, value := .identifier "tail" }]
private def lexed : LexedFile := { source, tokens, comments := [], diagnostics := [] }
private def remaining (cursor : Nat) : Remainder := { tokens := tokens.toArray, endIndex := 6, cursor }
private def value : QualifiedName := {
  span := span 0 11
  value := { components := { head := nameA, tail := [nameC, nameE] } }
}
private def events : List ParseDiagnostic := [hyphen nameA, hyphen nameC, hyphen nameE]

private theorem names_trace : QualifiedNameTraceParses source 16 (remaining 0) value (remaining 5) events := by
  have last : DottedIdentifierTailTraceParses source 16 (remaining 5) [] (remaining 5) [] :=
    .done (by simp [TokenKindAbsentAt, TokenAt, remaining, tokens])
  have second : DottedIdentifierTailTraceParses source 16 (remaining 3) [nameE] (remaining 5) [hyphen nameE] :=
    .next (span 7 8) (afterDot := remaining 4) (afterComponent := remaining 5)
      ⟨⟨by decide, rfl⟩, rfl⟩
      (.parsed ⟨⟨by decide, rfl⟩, rfl, rfl, rfl⟩ (.hyphen (by unfold IdentifierHyphenSpelling nameE; decide))) last
  have rest : DottedIdentifierTailTraceParses source 16 (remaining 1) [nameC, nameE]
      (remaining 5) [hyphen nameC, hyphen nameE] :=
    .next (span 3 4) (afterDot := remaining 2) (afterComponent := remaining 3)
      ⟨⟨by decide, rfl⟩, rfl⟩
      (.parsed ⟨⟨by decide, rfl⟩, rfl, rfl, rfl⟩ (.hyphen (by unfold IdentifierHyphenSpelling nameC; decide))) second
  have first : IdentifierTraceParses (remaining 0) nameA (remaining 1) [hyphen nameA] :=
    .parsed ⟨⟨by decide, rfl⟩, rfl, rfl, rfl⟩ (.hyphen (by unfold IdentifierHyphenSpelling nameA; decide))
  exact .parsed first rest

set_option maxRecDepth 16384 in
set_option maxHeartbeats 1000000 in
theorem canonical_names_lex : Lexer.lex file = .ok lexed := by
  have checked : (Lexer.lex file).toOption = some lexed := by decide +kernel
  cases result : Lexer.lex file with
  | error error => simp only [result, Except.toOption] at checked; contradiction
  | ok actual => simp only [result, Except.toOption] at checked; cases checked; rfl

/-- Every context and phase use the same successful maximal checked path.
The exact output state retains all six tokens and the complete 16-byte window. -/
theorem canonical_names_success (context : ParseContext) (phase : ParserPhase)
    (prior : List ParseDiagnostic) :
    ∃ actualLexed output, Lexer.lex file = .ok actualLexed ∧
      qualifiedName context phase { State.initial file actualLexed with diagnosticsRev := prior.reverse } =
        .ok value output ∧ output.declarativeRemainder = remaining 5 ∧
      output.diagnostics = prior ++ events ∧ output.file = file ∧
      output.window = { endIndex := 6, endByte := 16 } ∧
      output.peek? = some { span := span 12 16, value := .identifier "tail" } := by
  let input : State := { State.initial file lexed with diagnosticsRev := prior.reverse }
  have parsed : QualifiedNameTraceParses input.file.id input.window.endByte input.declarativeRemainder
      value (remaining 5) events := names_trace
  have result := qualifiedName_eq_ok_of_trace context phase parsed
  refine ⟨lexed, _, canonical_names_lex, result, rfl, ?_, rfl, rfl, rfl⟩
  change (events.reverse ++ prior.reverse).reverse = prior ++ events
  simp only [List.reverse_append, List.reverse_reverse]

/-- An absent dot ends the tail without touching any part of the state,
including diagnostics and arbitrary first/last/reversed prefix accumulators. -/
theorem stopped_tail_keeps_arbitrary_accumulator (context : ParseContext) (phase : ParserPhase)
    (first last : Identifier) (tailRev : List Identifier) (input : State) (fuel : Nat)
    (noDot : TokenKindAbsentAt input.tokens input.window.endIndex input.cursor (.symbol .dot)) :
    QualifiedNameInternals.qualifiedNameTail context phase first (fuel + 1) last tailRev input =
      .ok (qualifiedNameFromSuffix first last tailRev.reverse []) input := by
  simp only [QualifiedNameInternals.qualifiedNameTail, DelimitedTraceInternals.symbol_absent .dot noDot,
    Bool.false_eq_true, if_false, QualifiedNameInternals.finishQualifiedName,
    qualifiedNameFromSuffix, finalIdentifier, List.append_nil]

theorem complete_name_events_survive_filtering (normalizationFile : SourceFile)
    (lexical : List LexicalDiagnostic) (prior : List ParseDiagnostic) :
    filterParseDiagnostics normalizationFile lexical (prior ++ events) =
      filterParseDiagnostics normalizationFile lexical prior ++ events := by
  rw [filterParseDiagnostics_append]
  exact congrArg (filterParseDiagnostics normalizationFile lexical prior ++ ·)
    (filterParseDiagnostics_eq_of_cascadeFilters normalizationFile lexical (names_trace.cascadeFilters _ _))

end Solcore.Test.SyntaxQualifiedNameSuccessTraceProperties
