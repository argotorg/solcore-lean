import Solcore.Syntax.Parser.StatementRejectionTraceContracts
import Solcore.Syntax.Parser.CoreBlockClosingTraceProperties
import Solcore.Syntax.Parser.DelimitedRejectionPrimitiveProperties

/-! Exact raw Core rejection reports and preceding statement-event traces.
Rejection returns before the delayed whole-body tail validation. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

variable {statement : Parser Statement}
  {statementTrace : SourceId → Nat → DeclarativeGrammar.Remainder → Statement →
    DeclarativeGrammar.Remainder → List ParseDiagnostic → Prop}
  {statementRejects : SourceId → Nat → DeclarativeGrammar.Remainder →
    DeclarativeGrammar.Remainder → ParseDiagnostic → List ParseDiagnostic → Prop}

/-- Any ordinary rejection of the item loop preserves precisely the statement
events emitted before its failure, independently of fuel and reverse prefix. -/
theorem coreBlockItems_reject_trace_sound
    (successSound : StatementTraceSuccessSound statement statementTrace)
    (rejectSound : StatementTraceRejectSound statement statementRejects)
    (contextFrame : StatementSuccessContext statement)
    (opening : Token) (policy : TailExpressionPolicy) :
    ∀ fuel bodyRev input failure rejected,
      coreBlockItems statement opening policy fuel bodyRev input = .reject failure rejected →
      ∃ trace, DeclarativeGrammar.CoreBlockItemsTraceRejects statementTrace statementRejects
        input.file.id input.window.endByte input.declarativeRemainder
        rejected.declarativeRemainder failure.toDiagnostic trace ∧
        rejected.diagnostics = input.diagnostics ++ trace := by
  intro fuel
  induction fuel with
  | zero => intro bodyRev input failure rejected result; simp [coreBlockItems] at result
  | succ fuel ih =>
      intro bodyRev input failure rejected result
      unfold coreBlockItems at result
      cases closingPresent : isSymbol input .rightBrace with
      | true =>
          simp only [closingPresent, if_true] at result
          have missing := (closeCoreBlock_reject_reports opening policy bodyRev result).2.1
          rcases symbol_eq_ok_of_isSymbol_eq_true .rightBrace .statement closingPresent with
            ⟨closing, parsed⟩
          exact False.elim (missing ⟨closing.span,
            (symbol_success_exactTokenParses .rightBrace .statement parsed).1⟩)
      | false =>
          simp only [closingPresent, Bool.false_eq_true, if_false] at result
          have absent := symbolAbsentAt_of_isSymbol_eq_false .rightBrace closingPresent
          cases ended : input.atEnd with
          | true =>
              simp only [ended, if_true] at result
              cases closingResult : symbol .rightBrace .statement input with
              | invariant error => simp [closingResult] at result
              | ok closing afterClosing => simp [closingResult] at result
              | reject closingFailure closingRejected =>
                  have shape := acceptToken_reject_state_shape (.symbol .rightBrace)
                    .statement (· == .symbol .rightBrace) closingResult
                  subst closingRejected
                  simp only [closingResult] at result
                  cases result
                  have reported := (symbol_reject_reports_iff .rightBrace .statement).mpr
                    ⟨failure, closingResult, rfl⟩
                  exact ⟨[], .missingClose absent
                    (by simpa [State.atEnd, State.declarativeRemainder] using ended)
                    reported.2, by simp⟩
          | false =>
              simp only [ended, Bool.false_eq_true, if_false] at result
              have inside : input.cursor < input.window.endIndex := by simpa [State.atEnd] using ended
              cases statementResult : statement input with
              | invariant error => simp [statementResult] at result
              | reject statementFailure statementRejected =>
                  simp only [statementResult] at result
                  cases result
                  rcases rejectSound statementResult with ⟨trace, rejectedTrace, diagnostics⟩
                  exact ⟨trace, .statementRejected inside absent rejectedTrace, diagnostics⟩
              | ok value next =>
                  simp only [statementResult] at result
                  by_cases progress : next.cursor > input.cursor
                  · simp only [progress, if_true] at result
                    rcases ih (value :: bodyRev) next failure rejected result with
                      ⟨tailEvents, tailRejected, tailEq⟩
                    rcases successSound statementResult with ⟨headEvents, headParsed, headEq⟩
                    have frame := contextFrame statementResult
                    have tailAtInput : DeclarativeGrammar.CoreBlockItemsTraceRejects
                        statementTrace statementRejects input.file.id input.window.endByte
                        next.declarativeRemainder rejected.declarativeRemainder
                        failure.toDiagnostic tailEvents := by
                      simpa only [frame.1, frame.2] using tailRejected
                    refine ⟨headEvents ++ tailEvents,
                      .laterRejected inside absent headParsed progress tailAtInput, ?_⟩
                    rw [tailEq, headEq, List.append_assoc]
                  · simp only [progress, if_false] at result
                    contradiction

/-- Raw Core rejection has the exact opening/closing/statement report and
ordered earlier statement events, under explicit abstract statement contracts. -/
theorem coreBlock_reject_trace_sound
    (successSound : StatementTraceSuccessSound statement statementTrace)
    (rejectSound : StatementTraceRejectSound statement statementRejects)
    (contextFrame : StatementSuccessContext statement) (policy : TailExpressionPolicy) :
    BlockTraceRejectSound (coreBlock statement policy)
      (DeclarativeGrammar.CoreBlockTraceRejects statementTrace statementRejects
        policy.declarative) := by
  intro input rejected failure result
  unfold coreBlock at result
  cases openingResult : symbol .leftBrace .statement input with
  | invariant error => simp [openingResult] at result
  | reject openingFailure openingRejected =>
      have shape := acceptToken_reject_state_shape (.symbol .leftBrace)
        .statement (· == .symbol .leftBrace) openingResult
      subst openingRejected
      simp only [openingResult] at result
      cases result
      have reported := (symbol_reject_reports_iff .leftBrace .statement).mpr
        ⟨failure, openingResult, rfl⟩
      exact ⟨[], .openingMissing reported.1 reported.2, by simp⟩
  | ok opening afterOpening =>
      simp only [openingResult] at result
      rcases coreBlockItems_reject_trace_sound successSound rejectSound contextFrame
          opening policy (afterOpening.remainingCount + 1) [] afterOpening failure rejected result with
        ⟨trace, itemsRejected, diagnostics⟩
      have shape := (symbol_ok_tokenAt .leftBrace .statement openingResult).2
      refine ⟨trace, .itemsRejected opening.span
        (symbol_success_exactTokenParses .leftBrace .statement openingResult) ?_, ?_⟩
      · simpa only [shape] using itemsRejected
      · simpa only [shape, State.diagnostics] using diagnostics

end Solcore.Syntax.Parser
