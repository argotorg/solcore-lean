import Solcore.Syntax.Parser.ExactTokenPrimitiveRejectionTraceProperties

/-! Compile-time consumers of grammar-derived token success and exact reports.
All examples permit arbitrary prior diagnostics and parser contexts. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserExactTokenPrimitiveTraceProperties

open Solcore.Syntax
open Solcore.Syntax.Parser
open Solcore.Syntax.DeclarativeGrammar

example := @acceptToken_eq_ok_of_exactTokenParses
example := @acceptToken_success_diagnostics_eq
example := @acceptToken_exactToken_success_iff
example := @keyword_eq_ok_of_exactTokenParses
example := @symbol_eq_ok_of_exactTokenParses
example := @contextual_eq_ok_of_exactTokenParses
example := @keyword_exactToken_success_iff
example := @symbol_exactToken_success_iff
example := @contextual_exactToken_success_iff
example := @keyword_eq_rejectAt_of_tokenKindAbsent
example := @symbol_eq_rejectAt_of_tokenKindAbsent
example := @contextual_eq_rejectAt_of_tokenKindAbsent
example := @keyword_reject_reports_iff
example := @symbol_reject_reports_iff
example := @contextual_reject_reports_iff
example := @acceptToken_reject_reports
example := @keyword_reject_diagnostics_eq
example := @symbol_reject_diagnostics_eq
example := @contextual_reject_diagnostics_eq

private def exampleFile : SourceFile := {
  id := { origin := .main, path := "exact-token-trace.sol" }
  content := "pragma:from"
}

private def exampleSpan (startByte endByte : Nat) : SourceSpan := {
  source := exampleFile.id, startByte, endByte
}

private def exampleInput (cursor : Nat) (priorRev : List ParseDiagnostic) : State := {
  file := exampleFile
  tokens := #[{ span := exampleSpan 0 6, value := .keyword .pragmaKw },
    { span := exampleSpan 6 7, value := .symbol .colon },
    { span := exampleSpan 7 11, value := .identifier "from" }]
  cursor
  window := { endIndex := 3, endByte := 11 }
  diagnosticsRev := priorRev
}

/-- The exact hard-keyword carrier survives unchanged. -/
theorem keyword_success_example (context : ParseContext) (priorRev : List ParseDiagnostic) :
    ∃ output, keyword .pragmaKw context (exampleInput 0 priorRev) =
      .ok { span := exampleSpan 0 6, value := .keyword .pragmaKw } output ∧
      output.declarativeRemainder = (exampleInput 1 priorRev).declarativeRemainder ∧
      output.diagnostics = priorRev.reverse := by
  apply (keyword_exactToken_success_iff .pragmaKw context).mp
  simp [ExactTokenParses, TokenAt, State.declarativeRemainder, exampleInput]

/-- Symbols retain their own exact span and silent raw diagnostic trace. -/
theorem symbol_success_example (context : ParseContext) (priorRev : List ParseDiagnostic) :
    ∃ output, symbol .colon context (exampleInput 1 priorRev) =
      .ok { span := exampleSpan 6 7, value := .symbol .colon } output ∧
      output.declarativeRemainder = (exampleInput 2 priorRev).declarativeRemainder ∧
      output.diagnostics = priorRev.reverse := by
  apply (symbol_exactToken_success_iff .colon context).mp
  simp [ExactTokenParses, TokenAt, State.declarativeRemainder, exampleInput]

/-- A contextual word is still the supplied identifier token. -/
theorem contextual_success_example (context : ParseContext) (priorRev : List ParseDiagnostic) :
    ∃ output, contextual .from context (exampleInput 2 priorRev) =
      .ok { span := exampleSpan 7 11, value := .identifier "from" } output ∧
      output.declarativeRemainder = (exampleInput 3 priorRev).declarativeRemainder ∧
      output.diagnostics = priorRev.reverse := by
  apply (contextual_exactToken_success_iff .from context).mp
  simp [ExactTokenParses, TokenAt, State.declarativeRemainder, exampleInput,
    ContextualKeyword.spelling]

private theorem eofReport (expected : ParseExpectation) (context : ParseContext)
    (priorRev : List ParseDiagnostic) :
    RejectAtReports exampleFile.id 11 { head := expected, tail := [] } context
      (exampleInput 3 priorRev).declarativeRemainder {
        span := exampleSpan 11 11,
        kind := .unexpected none { head := expected, tail := [] } context
      } := by
  apply RejectAtReports.reported
  exact .windowEnd (by simp [State.declarativeRemainder, exampleInput])

/-- EOF failure fixes its expectation/context and keeps the entire input. -/
theorem keyword_rejection_example (context : ParseContext) (priorRev : List ParseDiagnostic) :
    ∃ failure, keyword .pragmaKw context (exampleInput 3 priorRev) =
      .reject failure (exampleInput 3 priorRev) ∧
      failure.toDiagnostic = {
        span := exampleSpan 11 11
        kind := .unexpected none { head := .keyword .pragmaKw, tail := [] } context } := by
  apply (keyword_reject_reports_iff .pragmaKw context).mp
  exact ⟨by simp [TokenKindAbsentAt, TokenAt, exampleInput],
    eofReport (.keyword .pragmaKw) context priorRev⟩

/-- Symbol EOF uses a symbol expectation without altering earlier diagnostics. -/
theorem symbol_rejection_example (context : ParseContext) (priorRev : List ParseDiagnostic) :
    ∃ failure, symbol .semicolon context (exampleInput 3 priorRev) =
      .reject failure (exampleInput 3 priorRev) ∧
      failure.toDiagnostic = {
        span := exampleSpan 11 11
        kind := .unexpected none { head := .symbol .semicolon, tail := [] } context } := by
  apply (symbol_reject_reports_iff .semicolon context).mp
  exact ⟨by simp [TokenKindAbsentAt, TokenAt, exampleInput],
    eofReport (.symbol .semicolon) context priorRev⟩

/-- A hard keyword is not a contextual spelling; the expected category remains
contextual while the actual hard keyword and its original span are preserved. -/
theorem contextual_rejection_example (context : ParseContext) (priorRev : List ParseDiagnostic) :
    ∃ failure, contextual .from context (exampleInput 0 priorRev) =
      .reject failure (exampleInput 0 priorRev) ∧
      failure.toDiagnostic = {
        span := exampleSpan 0 6
        kind := .unexpected (some (.keyword .pragmaKw))
          { head := .contextual .from, tail := [] } context } := by
  apply (contextual_reject_reports_iff .from context).mp
  refine ⟨by simp [TokenKindAbsentAt, TokenAt, exampleInput], ?_⟩
  apply RejectAtReports.reported
  apply CurrentInputAt.token (current := {
    span := exampleSpan 0 6, value := .keyword .pragmaKw })
  simp [TokenAt, State.declarativeRemainder, exampleInput]

end Solcore.Test.SyntaxParserExactTokenPrimitiveTraceProperties
