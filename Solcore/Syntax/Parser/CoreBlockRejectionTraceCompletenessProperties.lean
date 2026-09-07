import Solcore.Syntax.Parser.CoreBlockRejectionTraceSoundnessProperties

/-! Exact independent raw Core rejections execute with their specified failure
report and preceding events. Strict statement progress bounds production fuel. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

variable {statement : Parser Statement}
  {statementTrace : SourceId → Nat → DeclarativeGrammar.Remainder → Statement →
    DeclarativeGrammar.Remainder → List ParseDiagnostic → Prop}
  {statementRejects : SourceId → Nat → DeclarativeGrammar.Remainder →
    DeclarativeGrammar.Remainder → ParseDiagnostic → List ParseDiagnostic → Prop}

private theorem closing_absent {input : State}
    (absent : DeclarativeGrammar.TokenKindAbsentAt input.tokens input.window.endIndex
      input.cursor (.symbol .rightBrace)) : isSymbol input .rightBrace = false := by
  apply Bool.eq_false_iff.mpr
  intro present
  rcases symbol_eq_ok_of_isSymbol_eq_true .rightBrace .statement present with ⟨token, result⟩
  exact absent ⟨token.span, (symbol_ok_tokenAt .rightBrace .statement result).1⟩

/-- Remaining-token fuel realizes any independent first-rejection trace.
The incoming reverse prefix never receives delayed tail-validation events. -/
theorem coreBlockItems_trace_reject_complete
    (successComplete : StatementTraceSuccessComplete statement statementTrace)
    (rejectComplete : StatementTraceRejectComplete statement statementRejects)
    (contextFrame : StatementSuccessContext statement)
    (opening : Token) (policy : TailExpressionPolicy)
    (fuel : Nat) (bodyRev : List Statement)
    {input : State} {remainder : DeclarativeGrammar.Remainder}
    {diagnostic : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : DeclarativeGrammar.CoreBlockItemsTraceRejects statementTrace statementRejects
      input.file.id input.window.endByte input.declarativeRemainder remainder diagnostic trace)
    (adequate : input.remainingCount < fuel) :
    ∃ failure rejected, coreBlockItems statement opening policy fuel bodyRev input =
      .reject failure rejected ∧ rejected.declarativeRemainder = remainder ∧
      failure.toDiagnostic = diagnostic ∧ rejected.diagnostics = input.diagnostics ++ trace := by
  induction fuel generalizing bodyRev input remainder diagnostic trace with
  | zero => omega
  | succ fuel ih =>
      cases rejection with
      | missingClose absent atEnd reported =>
          rcases (symbol_reject_reports_iff .rightBrace .statement).mp ⟨absent, reported⟩ with
            ⟨failure, result, reportEq⟩
          have ended : input.atEnd = true := decide_eq_true atEnd
          exact ⟨failure, input, by
            simp only [coreBlockItems, closing_absent absent, Bool.false_eq_true, if_false,
              ended, if_true, result], rfl, reportEq, by simp⟩
      | statementRejected inside absent statementRejected =>
          rcases rejectComplete statementRejected with
            ⟨failure, rejected, result, afterEq, reportEq, diagnostics⟩
          have notEnded : input.atEnd = false := decide_eq_false (Nat.not_le_of_gt inside)
          exact ⟨failure, rejected, by
            simp only [coreBlockItems, closing_absent absent, Bool.false_eq_true, if_false,
              notEnded, result], afterEq, reportEq, diagnostics⟩
      | laterRejected inside absent headParsed progress tailRejected =>
          rename_i afterStatement head headEvents tailEvents
          rcases successComplete headParsed with ⟨next, headResult, afterEq, headEq⟩
          have frame := contextFrame headResult
          have nextProgress : input.cursor < next.cursor := by
            simpa only [← afterEq, State.declarativeRemainder] using progress
          have notEnded : input.atEnd = false := decide_eq_false (Nat.not_le_of_gt inside)
          have tailAtNext : DeclarativeGrammar.CoreBlockItemsTraceRejects statementTrace
              statementRejects next.file.id next.window.endByte next.declarativeRemainder
              remainder diagnostic tailEvents := by
            simpa only [frame.1, frame.2, afterEq] using tailRejected
          have nextAdequate : next.remainingCount < fuel := by
            change input.cursor < input.window.endIndex at inside
            simp only [State.remainingCount, frame.2] at adequate ⊢
            omega
          rcases ih (head :: bodyRev) tailAtNext nextAdequate with
            ⟨failure, rejected, tailResult, outputAfter, reportEq, outputEq⟩
          refine ⟨failure, rejected, ?_, outputAfter, reportEq, ?_⟩
          · simp only [coreBlockItems, closing_absent absent, Bool.false_eq_true, if_false,
              notEnded, headResult, nextProgress, if_true]
            exact tailResult
          · rw [outputEq, headEq, List.append_assoc]

/-- The production bound suffices for exact rejection after any number of
strictly advancing successful statements in the fixed token window. -/
theorem coreBlockItems_production_trace_reject_complete
    (successComplete : StatementTraceSuccessComplete statement statementTrace)
    (rejectComplete : StatementTraceRejectComplete statement statementRejects)
    (contextFrame : StatementSuccessContext statement)
    (opening : Token) (policy : TailExpressionPolicy) (bodyRev : List Statement)
    {input : State} {remainder : DeclarativeGrammar.Remainder}
    {diagnostic : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : DeclarativeGrammar.CoreBlockItemsTraceRejects statementTrace statementRejects
      input.file.id input.window.endByte input.declarativeRemainder remainder diagnostic trace) :
    ∃ failure rejected, coreBlockItems statement opening policy (input.remainingCount + 1)
      bodyRev input = .reject failure rejected ∧ rejected.declarativeRemainder = remainder ∧
      failure.toDiagnostic = diagnostic ∧ rejected.diagnostics = input.diagnostics ++ trace :=
  coreBlockItems_trace_reject_complete successComplete rejectComplete contextFrame opening policy
    (input.remainingCount + 1) bodyRev rejection (by omega)

/-- Raw Core rejection executes with its exact independent report, remainder,
and appended events under explicit statement completeness and context laws. -/
theorem coreBlock_trace_reject_complete
    (successComplete : StatementTraceSuccessComplete statement statementTrace)
    (rejectComplete : StatementTraceRejectComplete statement statementRejects)
    (contextFrame : StatementSuccessContext statement) (policy : TailExpressionPolicy) :
    BlockTraceRejectComplete (coreBlock statement policy)
      (DeclarativeGrammar.CoreBlockTraceRejects statementTrace statementRejects
        policy.declarative) := by
  intro input remainder diagnostic trace rejection
  cases rejection with
  | openingMissing absent reported =>
      rcases (symbol_reject_reports_iff .leftBrace .statement).mp ⟨absent, reported⟩ with
        ⟨failure, result, reportEq⟩
      exact ⟨failure, input, by simp only [coreBlock, result], rfl, reportEq, by simp⟩
  | itemsRejected opening openingParsed itemsRejected =>
      have openingResult := symbol_eq_ok_of_exactTokenParses .leftBrace .statement openingParsed
      rcases openingParsed with ⟨openingToken, rfl⟩
      rcases coreBlockItems_production_trace_reject_complete successComplete rejectComplete
          contextFrame { span := opening, value := .symbol .leftBrace } policy []
          (input := { input with cursor := input.cursor + 1 }) itemsRejected with
        ⟨failure, rejected, result, afterEq, reportEq, diagnostics⟩
      exact ⟨failure, rejected, by simpa only [coreBlock, openingResult] using result,
        afterEq, reportEq, diagnostics⟩

/-- Complete rejection is equivalent to its independent endpoint, full failure
report, and ordered preceding diagnostics, including arbitrary prior events. -/
theorem coreBlock_trace_reject_iff
    (successSound : StatementTraceSuccessSound statement statementTrace)
    (rejectSound : StatementTraceRejectSound statement statementRejects)
    (successComplete : StatementTraceSuccessComplete statement statementTrace)
    (rejectComplete : StatementTraceRejectComplete statement statementRejects)
    (contextFrame : StatementSuccessContext statement) (policy : TailExpressionPolicy)
    {input : State} {remainder : DeclarativeGrammar.Remainder}
    {diagnostic : ParseDiagnostic} {trace : List ParseDiagnostic} :
    DeclarativeGrammar.CoreBlockTraceRejects statementTrace statementRejects policy.declarative
      input.file.id input.window.endByte input.declarativeRemainder remainder diagnostic trace ↔
    ∃ failure rejected, coreBlock statement policy input = .reject failure rejected ∧
      rejected.declarativeRemainder = remainder ∧ failure.toDiagnostic = diagnostic ∧
      rejected.diagnostics = input.diagnostics ++ trace := by
  constructor
  · exact coreBlock_trace_reject_complete successComplete rejectComplete contextFrame policy
  · rintro ⟨failure, rejected, result, afterEq, reportEq, diagnostics⟩
    rcases coreBlock_reject_trace_sound successSound rejectSound contextFrame policy result with
      ⟨actualTrace, rejection, actualEq⟩
    have events : actualTrace = trace := List.append_cancel_left (actualEq.symm.trans diagnostics)
    simpa only [afterEq, reportEq, events] using rejection

/-- Diagnostic injectivity strengthens the same bridge to the entire specified
failure record, without changing the exact remainder or appended events. -/
theorem coreBlock_trace_reject_failure_iff
    (successSound : StatementTraceSuccessSound statement statementTrace)
    (rejectSound : StatementTraceRejectSound statement statementRejects)
    (successComplete : StatementTraceSuccessComplete statement statementTrace)
    (rejectComplete : StatementTraceRejectComplete statement statementRejects)
    (contextFrame : StatementSuccessContext statement) (policy : TailExpressionPolicy)
    {input : State} {remainder : DeclarativeGrammar.Remainder}
    {failure : Failure} {trace : List ParseDiagnostic} :
    DeclarativeGrammar.CoreBlockTraceRejects statementTrace statementRejects policy.declarative
      input.file.id input.window.endByte input.declarativeRemainder remainder failure.toDiagnostic trace ↔
    ∃ rejected, coreBlock statement policy input = .reject failure rejected ∧
      rejected.declarativeRemainder = remainder ∧
      rejected.diagnostics = input.diagnostics ++ trace := by
  rw [coreBlock_trace_reject_iff successSound rejectSound successComplete rejectComplete
    contextFrame policy]
  constructor
  · rintro ⟨actual, rejected, result, afterEq, reportEq, diagnostics⟩
    cases Failure.toDiagnostic_injective reportEq
    exact ⟨rejected, result, afterEq, diagnostics⟩
  · rintro ⟨rejected, result, afterEq, diagnostics⟩
    exact ⟨failure, rejected, result, afterEq, rfl, diagnostics⟩

end Solcore.Syntax.Parser
