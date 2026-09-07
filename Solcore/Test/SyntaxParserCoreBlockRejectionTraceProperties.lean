import Solcore.Syntax.Parser.CoreBlockRejectionTraceCompletenessProperties
import Solcore.Test.SyntaxCoreBlockRejectionTraceProperties

/-! Executable consumers with arbitrary statement contracts and existing
diagnostics. Ordinary rejection never starts delayed block-tail validation. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserCoreBlockRejectionTraceProperties

open Solcore.Syntax
open Solcore.Syntax.Parser
open Solcore.Syntax.DeclarativeGrammar

variable {statement : Parser Statement}
  {statementTrace : SourceId → Nat → Remainder → Statement → Remainder →
    List ParseDiagnostic → Prop}
  {statementRejects : SourceId → Nat → Remainder → Remainder →
    ParseDiagnostic → List ParseDiagnostic → Prop}

example := @coreBlockItems_reject_trace_sound
example := @coreBlock_reject_trace_sound
example := @coreBlockItems_trace_reject_complete
example := @coreBlockItems_production_trace_reject_complete
example := @coreBlock_trace_reject_complete
example := @coreBlock_trace_reject_iff
example := @coreBlock_trace_reject_failure_iff

/-- An exhausted subwindow rejects before checking any prefix statement,
even when the selected policy requires its final expression's semicolon. -/
theorem exhausted_window_preserves_all_prior_events
    (successComplete : StatementTraceSuccessComplete statement statementTrace)
    (rejectComplete : StatementTraceRejectComplete statement statementRejects)
    (contextFrame : StatementSuccessContext statement)
    (opening : Token) (bodyRev : List Statement) {input : State}
    (atEnd : input.window.endIndex ≤ input.cursor) :
    ∃ failure rejected, coreBlockItems statement opening .require
      (input.remainingCount + 1) bodyRev input = .reject failure rejected ∧
      rejected.declarativeRemainder = input.declarativeRemainder ∧
      failure.toDiagnostic = {
        span := { source := input.file.id, startByte := input.window.endByte, endByte := input.window.endByte },
        kind := .unexpected none { head := .symbol .rightBrace, tail := [] } .statement } ∧
      rejected.diagnostics = input.diagnostics := by
  simpa only [List.append_nil] using
    coreBlockItems_production_trace_reject_complete successComplete rejectComplete contextFrame
      opening .require bodyRev
      (SyntaxCoreBlockRejectionTraceProperties.missing_close_uses_window_endpoint atEnd)

/-- The original input's diagnostic list can be nonempty; every specified
event from a rejecting statement is appended once, without a final report. -/
theorem rejecting_statement_appends_only_its_events
    (successComplete : StatementTraceSuccessComplete statement statementTrace)
    (rejectComplete : StatementTraceRejectComplete statement statementRejects)
    (contextFrame : StatementSuccessContext statement)
    (opening : Token) (policy : TailExpressionPolicy) (bodyRev : List Statement)
    {input : State} {remainder : Remainder} {diagnostic : ParseDiagnostic}
    {first second : ParseDiagnostic}
    (inside : input.cursor < input.window.endIndex)
    (absent : TokenKindAbsentAt input.tokens input.window.endIndex input.cursor (.symbol .rightBrace))
    (rejection : statementRejects input.file.id input.window.endByte input.declarativeRemainder
      remainder diagnostic [first, second, first]) :
    ∃ failure rejected, coreBlockItems statement opening policy (input.remainingCount + 1)
      bodyRev input = .reject failure rejected ∧ rejected.declarativeRemainder = remainder ∧
      failure.toDiagnostic = diagnostic ∧
      rejected.diagnostics = input.diagnostics ++ [first, second, first] :=
  coreBlockItems_production_trace_reject_complete successComplete rejectComplete contextFrame
    opening policy bodyRev (.statementRejected inside absent rejection)

/-- A raw rejection under one tail policy supplies exactly the same failure,
remainder, and appended diagnostics under the other policy. -/
theorem changing_tail_policy_preserves_rejection
    (successSound : StatementTraceSuccessSound statement statementTrace)
    (rejectSound : StatementTraceRejectSound statement statementRejects)
    (successComplete : StatementTraceSuccessComplete statement statementTrace)
    (rejectComplete : StatementTraceRejectComplete statement statementRejects)
    (contextFrame : StatementSuccessContext statement)
    {input rejected : State} {failure : Failure}
    (result : coreBlock statement .allow input = .reject failure rejected) :
    ∃ required, coreBlock statement .require input = .reject failure required ∧
      required.declarativeRemainder = rejected.declarativeRemainder ∧
      required.diagnostics = rejected.diagnostics := by
  rcases coreBlock_reject_trace_sound successSound rejectSound contextFrame .allow result with
    ⟨trace, rejection, diagnostics⟩
  rcases (coreBlock_trace_reject_failure_iff successSound rejectSound successComplete
      rejectComplete contextFrame .require).mp (rejection.withPolicy .require) with
    ⟨required, requiredResult, remainder, requiredDiagnostics⟩
  exact ⟨required, requiredResult, remainder, requiredDiagnostics.trans diagnostics.symm⟩

end Solcore.Test.SyntaxParserCoreBlockRejectionTraceProperties
