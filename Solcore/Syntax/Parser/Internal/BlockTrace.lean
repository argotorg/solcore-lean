import Solcore.Syntax.Internal.BlockTrace
import Solcore.Syntax.Parser.Internal.DiagnosticTrace
import Solcore.Syntax.Parser.Internal.DelimitedSoundness
import Solcore.Syntax.Parser.Internal.SimpleStatementSoundness
import Solcore.Syntax.Internal.DelimitedOutcomes
import Solcore.Syntax.Parser.Internal.BlockSoundness
import Solcore.Syntax.Parser.Internal.ControlSoundness
import Solcore.Syntax.Parser.Internal.ExportProofs

/-!
Parser side of the traces of blocks, return statements and terminated control: the parsers
produce exactly the events of the trace grammar.
-/

section
-- leanmerge: from Solcore.Syntax.Parser.OptionalReturnValueRejectionTraceProperties
/-! Rejected optional return values preserve semicolon-first priority and the
inner expression's exact failure report and complete preceding event sequence. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.StatementSimpleInternals

variable {expression : Parser Expr}
  {expressionRejects : SourceId → Nat → DeclarativeGrammar.Remainder →
    DeclarativeGrammar.Remainder → ParseDiagnostic → List ParseDiagnostic → Prop}

private theorem semicolon_absent {input : State}
    (absent : DeclarativeGrammar.TokenKindAbsentAt input.tokens input.window.endIndex
      input.cursor (.symbol .semicolon)) : isSymbol input .semicolon = false := by
  apply Bool.eq_false_iff.mpr
  intro present
  rcases symbol_eq_ok_of_isSymbol_eq_true .semicolon .statement present with ⟨token, result⟩
  exact absent ⟨token.span, (symbol_ok_tokenAt .semicolon .statement result).1⟩

theorem optionalReturnValue_reject_trace_sound
    (rejectSound : ExpressionTraceRejectSound expression expressionRejects)
    {input rejected : State} {failure : Failure}
    (result : optionalReturnValue expression input = .reject failure rejected) :
    ∃ trace, DeclarativeGrammar.OptionalReturnValueTraceRejects expressionRejects
      input.file.id input.window.endByte input.declarativeRemainder rejected.declarativeRemainder
      failure.toDiagnostic trace ∧ rejected.diagnostics = input.diagnostics ++ trace := by
  unfold optionalReturnValue getState at result
  simp only [bind] at result
  cases present : isSymbol input .semicolon with
  | true => simp [present, pure] at result
  | false =>
      simp only [present, Bool.false_eq_true, if_false] at result
      cases expressionResult : expression input with
      | invariant error => simp [expressionResult] at result
      | ok value next => simp [expressionResult, pure] at result
      | reject expressionFailure expressionRejected =>
          simp only [expressionResult] at result
          cases result
          rcases rejectSound expressionResult with ⟨trace, rejectedTrace, diagnostics⟩
          exact ⟨trace, .expressionRejected
            (symbolAbsentAt_of_isSymbol_eq_false .semicolon present) rejectedTrace, diagnostics⟩

theorem optionalReturnValue_trace_reject_complete
    (rejectComplete : ExpressionTraceRejectComplete expression expressionRejects)
    {input : State} {remainder : DeclarativeGrammar.Remainder}
    {diagnostic : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : DeclarativeGrammar.OptionalReturnValueTraceRejects expressionRejects
      input.file.id input.window.endByte input.declarativeRemainder remainder diagnostic trace) :
    ∃ failure rejected, optionalReturnValue expression input = .reject failure rejected ∧
      rejected.declarativeRemainder = remainder ∧ failure.toDiagnostic = diagnostic ∧
      rejected.diagnostics = input.diagnostics ++ trace := by
  cases rejection with
  | expressionRejected absent rejectedTrace =>
      rcases rejectComplete rejectedTrace with ⟨failure, rejected, result, afterEq, reportEq, diagnostics⟩
      exact ⟨failure, rejected, by
        simp only [optionalReturnValue, getState, bind, semicolon_absent absent,
          Bool.false_eq_true, if_false, result], afterEq, reportEq, diagnostics⟩

theorem optionalReturnValue_trace_reject_iff
    (rejectSound : ExpressionTraceRejectSound expression expressionRejects)
    (rejectComplete : ExpressionTraceRejectComplete expression expressionRejects)
    {input : State} {remainder : DeclarativeGrammar.Remainder}
    {diagnostic : ParseDiagnostic} {trace : List ParseDiagnostic} :
    DeclarativeGrammar.OptionalReturnValueTraceRejects expressionRejects
      input.file.id input.window.endByte input.declarativeRemainder remainder diagnostic trace ↔
    ∃ failure rejected, optionalReturnValue expression input = .reject failure rejected ∧
      rejected.declarativeRemainder = remainder ∧ failure.toDiagnostic = diagnostic ∧
      rejected.diagnostics = input.diagnostics ++ trace := by
  constructor
  · exact optionalReturnValue_trace_reject_complete rejectComplete
  · rintro ⟨failure, rejected, result, afterEq, reportEq, diagnostics⟩
    rcases optionalReturnValue_reject_trace_sound rejectSound result with
      ⟨actualTrace, rejection, actualEq⟩
    have events : actualTrace = trace := List.append_cancel_left (actualEq.symm.trans diagnostics)
    simpa only [afterEq, reportEq, events] using rejection

end Solcore.Syntax.Parser.StatementSimpleInternals
end

section
-- leanmerge: from Solcore.Syntax.Parser.CoreBlockClosingTraceProperties
/-! Exact brace closing, tail-validation events, and silent closing rejection. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Independently supplied tail checks determine every diagnostic added by closing. -/
theorem closeCoreBlock_success_diagnostics_eq_of_trace
    (opening : Token) (policy : TailExpressionPolicy) (bodyRev : List Statement)
    {input output : State} {body : Block} {trace : List ParseDiagnostic}
    (result : closeCoreBlock opening policy bodyRev input = .ok body output)
    (checked : DeclarativeGrammar.CoreBlockTailsDiagnosticTrace
      policy.declarative bodyRev.reverse trace) :
    output.diagnostics = input.diagnostics ++ trace := by
  rcases closeCoreBlock_success_trace_sound opening policy bodyRev result with
    ⟨actualTrace, actual, diagnostics⟩
  simpa only [actual.output_unique checked] using diagnostics

/-- The exact independent brace, source-order AST, remainder, and tail events
are equivalent to execution. The brace span stays existential because covering
it with the opening span need not retain enough information to recover it. -/
theorem closeCoreBlock_trace_success_iff
    (opening : Token) (policy : TailExpressionPolicy) (bodyRev : List Statement)
    {input : State} {body : Block} {remainder : DeclarativeGrammar.Remainder}
    {trace : List ParseDiagnostic} :
    ((∃ closingSpan,
      DeclarativeGrammar.ExactTokenParses (.symbol .rightBrace)
        input.declarativeRemainder closingSpan remainder ∧
      body = { span := SourceSpan.cover opening.span closingSpan, value := bodyRev.reverse }) ∧
      DeclarativeGrammar.CoreBlockTailsDiagnosticTrace policy.declarative bodyRev.reverse trace) ↔
    ∃ output, closeCoreBlock opening policy bodyRev input = .ok body output ∧
      output.declarativeRemainder = remainder ∧
      output.diagnostics = input.diagnostics ++ trace := by
  constructor
  · rintro ⟨⟨closingSpan, closingParsed, rfl⟩, checked⟩
    have closingResult := symbol_eq_ok_of_exactTokenParses .rightBrace .statement closingParsed
    have succeeds : ∃ output, closeCoreBlock opening policy bodyRev input = .ok
        { span := SourceSpan.cover opening.span closingSpan, value := bodyRev.reverse } output := by
      simp only [closeCoreBlock, bind, closingResult, modifyState, pure]
      exact ⟨_, rfl⟩
    rcases succeeds with ⟨output, result⟩
    rcases closeCoreBlock_success_ordinary_sound opening policy bodyRev result with
      ⟨actualSpan, _, actualClosing⟩
    exact ⟨output, result, actualClosing.output_unique closingParsed,
      closeCoreBlock_success_diagnostics_eq_of_trace opening policy bodyRev result checked⟩
  · rintro ⟨output, result, after, diagnostics⟩
    rcases closeCoreBlock_success_ordinary_sound opening policy bodyRev result with
      ⟨closingSpan, bodyEq, closingParsed⟩
    rcases closeCoreBlock_success_trace_sound opening policy bodyRev result with
      ⟨actualTrace, checked, actualDiagnostics⟩
    have events : actualTrace = trace :=
      List.append_cancel_left (actualDiagnostics.symm.trans diagnostics)
    exact ⟨⟨closingSpan, after ▸ closingParsed, bodyEq⟩, events ▸ checked⟩

/-- A missing closing brace rejects before tail validation can run. -/
theorem closeCoreBlock_reject_iff_symbol
    (opening : Token) (policy : TailExpressionPolicy) (bodyRev : List Statement)
    {input rejected : State} {failure : Failure} :
    closeCoreBlock opening policy bodyRev input = .reject failure rejected ↔
      symbol .rightBrace .statement input = .reject failure rejected := by
  cases closingResult : symbol .rightBrace .statement input <;>
    simp only [closeCoreBlock, bind, closingResult, modifyState, pure,
      reduceCtorEq, Reply.reject.injEq, iff_self]

/-- Closing rejection retains the whole input and every prior event, and its
complete uncommitted report is exactly that of the required right brace. -/
theorem closeCoreBlock_reject_reports
    (opening : Token) (policy : TailExpressionPolicy) (bodyRev : List Statement)
    {input rejected : State} {failure : Failure}
    (result : closeCoreBlock opening policy bodyRev input = .reject failure rejected) :
    rejected = input ∧
      DeclarativeGrammar.TokenKindAbsentAt input.tokens input.window.endIndex input.cursor
        (.symbol .rightBrace) ∧
      DeclarativeGrammar.RejectAtReports input.file.id input.window.endByte
        { head := .symbol .rightBrace, tail := [] } .statement
        input.declarativeRemainder failure.toDiagnostic ∧
      rejected.diagnostics = input.diagnostics := by
  have primitive := (closeCoreBlock_reject_iff_symbol opening policy bodyRev).mp result
  have stateEq := acceptToken_reject_state_shape (.symbol .rightBrace) .statement
    (· == .symbol .rightBrace) primitive
  subst rejected
  have reported := (symbol_reject_reports_iff .rightBrace .statement).mpr ⟨failure, primitive, rfl⟩
  exact ⟨rfl, reported.1, reported.2, rfl⟩

/-- Independent brace absence and its diagnostic report characterize exact
silent rejection, with no validity or prior-diagnostic assumptions. -/
theorem closeCoreBlock_reject_reports_iff
    (opening : Token) (policy : TailExpressionPolicy) (bodyRev : List Statement)
    {input : State} {diagnostic : ParseDiagnostic} :
    (DeclarativeGrammar.TokenKindAbsentAt input.tokens input.window.endIndex input.cursor
        (.symbol .rightBrace) ∧
      DeclarativeGrammar.RejectAtReports input.file.id input.window.endByte
        { head := .symbol .rightBrace, tail := [] } .statement
        input.declarativeRemainder diagnostic) ↔
      ∃ failure, closeCoreBlock opening policy bodyRev input = .reject failure input ∧
        failure.toDiagnostic = diagnostic := by
  rw [symbol_reject_reports_iff .rightBrace .statement]
  constructor
  · rintro ⟨failure, result, report⟩
    exact ⟨failure, (closeCoreBlock_reject_iff_symbol opening policy bodyRev).mpr result, report⟩
  · rintro ⟨failure, result, report⟩
    exact ⟨failure, (closeCoreBlock_reject_iff_symbol opening policy bodyRev).mp result, report⟩

/-- The independent report also fixes all fields of the uncommitted failure. -/
theorem closeCoreBlock_reject_failure_iff
    (opening : Token) (policy : TailExpressionPolicy) (bodyRev : List Statement)
    {input : State} {failure : Failure} :
    (DeclarativeGrammar.TokenKindAbsentAt input.tokens input.window.endIndex input.cursor
        (.symbol .rightBrace) ∧
      DeclarativeGrammar.RejectAtReports input.file.id input.window.endByte
        { head := .symbol .rightBrace, tail := [] } .statement
        input.declarativeRemainder failure.toDiagnostic) ↔
      closeCoreBlock opening policy bodyRev input = .reject failure input := by
  constructor
  · intro reported
    rcases (closeCoreBlock_reject_reports_iff opening policy bodyRev).mp reported with
      ⟨actual, result, report⟩
    exact Failure.toDiagnostic_injective report ▸ result
  · intro result
    exact (closeCoreBlock_reject_reports_iff opening policy bodyRev).mpr ⟨failure, result, rfl⟩

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.CoreBlockRejectionTraceSoundnessProperties
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
end

section
-- leanmerge: from Solcore.Syntax.Parser.CoreBlockRejectionTraceCompletenessProperties
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
end

section
-- leanmerge: from Solcore.Syntax.Parser.CoreBlockTraceSoundnessProperties
/-! Raw Core success traces from explicit statement soundness and context laws.
All statement events precede the single final whole-body validation pass. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

variable {statement : Parser Statement}
  {statementTrace : SourceId → Nat → DeclarativeGrammar.Remainder → Statement →
    DeclarativeGrammar.Remainder → List ParseDiagnostic → Prop}

/-- An arbitrary-fuel successful item loop preserves its reverse prefix and
records only fresh statement events, followed by validation of the entire body. -/
theorem coreBlockItems_success_trace_sound
    (successSound : StatementTraceSuccessSound statement statementTrace)
    (contextFrame : StatementSuccessContext statement)
    (opening : Token) (policy : TailExpressionPolicy) :
    ∀ fuel bodyRev input body output,
      coreBlockItems statement opening policy fuel bodyRev input = .ok body output →
      ∃ closingSpan suffix statementEvents validationEvents,
        body = { span := SourceSpan.cover opening.span closingSpan, value := bodyRev.reverse ++ suffix } ∧
        DeclarativeGrammar.CoreBlockItemsTraceParses statementTrace input.file.id input.window.endByte
          input.declarativeRemainder suffix closingSpan output.declarativeRemainder statementEvents ∧
        DeclarativeGrammar.CoreBlockTailsDiagnosticTrace policy.declarative
          (bodyRev.reverse ++ suffix) validationEvents ∧
        output.diagnostics = input.diagnostics ++ (statementEvents ++ validationEvents) := by
  intro fuel
  induction fuel with
  | zero => intro bodyRev input body output result; simp [coreBlockItems] at result
  | succ fuel ih =>
      intro bodyRev input body output result
      unfold coreBlockItems at result
      cases closingPresent : isSymbol input .rightBrace with
      | true =>
          simp only [closingPresent, if_true] at result
          rcases closeCoreBlock_success_ordinary_sound opening policy bodyRev result with
            ⟨closingSpan, bodyEq, closingParsed⟩
          rcases closeCoreBlock_success_trace_sound opening policy bodyRev result with
            ⟨validationEvents, validated, diagnostics⟩
          refine ⟨closingSpan, [], [], validationEvents, ?_, .close closingSpan closingParsed, ?_, ?_⟩
          · simpa only [List.append_nil] using bodyEq
          · simpa only [List.append_nil] using validated
          · simpa only [List.nil_append] using diagnostics
      | false =>
          simp only [closingPresent, Bool.false_eq_true, if_false] at result
          cases ended : input.atEnd with
          | true =>
              simp only [ended, if_true] at result
              cases closingResult : symbol .rightBrace .statement input <;> simp [closingResult] at result
          | false =>
              simp only [ended, Bool.false_eq_true, if_false] at result
              cases statementResult : statement input with
              | invariant error => simp [statementResult] at result
              | reject failure rejected => simp [statementResult] at result
              | ok value next =>
                  simp only [statementResult] at result
                  by_cases progress : next.cursor > input.cursor
                  · simp only [progress, if_true] at result
                    rcases ih (value :: bodyRev) next body output result with
                      ⟨closingSpan, suffix, tailEvents, validationEvents, bodyEq,
                        tailParsed, validated, tailEq⟩
                    rcases successSound statementResult with ⟨headEvents, headParsed, headEq⟩
                    have frame := contextFrame statementResult
                    have tailAtInput : DeclarativeGrammar.CoreBlockItemsTraceParses
                        statementTrace input.file.id input.window.endByte next.declarativeRemainder
                        suffix closingSpan output.declarativeRemainder tailEvents := by
                      simpa only [frame.1, frame.2] using tailParsed
                    refine ⟨closingSpan, value :: suffix, headEvents ++ tailEvents,
                      validationEvents, ?_, .next (by
                        simpa [State.atEnd, State.declarativeRemainder] using ended)
                        (symbolAbsentAt_of_isSymbol_eq_false .rightBrace closingPresent)
                        headParsed progress tailAtInput, ?_, ?_⟩
                    · simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using bodyEq
                    · simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using validated
                    · rw [tailEq, headEq]
                      simp only [List.append_assoc]
                  · simp only [progress, if_false] at result
                    contradiction

/-- Raw Core success has an independent exact block trace under abstract
statement contracts; no statement or block rejection premise is necessary. -/
theorem coreBlock_success_trace_sound
    (successSound : StatementTraceSuccessSound statement statementTrace)
    (contextFrame : StatementSuccessContext statement) (policy : TailExpressionPolicy) :
    BlockTraceSuccessSound (coreBlock statement policy)
      (DeclarativeGrammar.CoreBlockTraceParses statementTrace policy.declarative) := by
  intro input output body result
  unfold coreBlock at result
  cases openingResult : symbol .leftBrace .statement input with
  | invariant error => simp [openingResult] at result
  | reject failure rejected => simp [openingResult] at result
  | ok opening afterOpening =>
      simp only [openingResult] at result
      rcases coreBlockItems_success_trace_sound successSound contextFrame opening policy
          (afterOpening.remainingCount + 1) [] afterOpening body output result with
        ⟨closingSpan, suffix, statementEvents, validationEvents, bodyEq,
          itemsParsed, validated, diagnostics⟩
      have openingShape := (symbol_ok_tokenAt .leftBrace .statement openingResult).2
      have openingParsed := symbol_success_exactTokenParses .leftBrace .statement openingResult
      simp only [List.reverse_nil, List.nil_append] at bodyEq validated
      subst body
      refine ⟨statementEvents ++ validationEvents, .parsed opening.span closingSpan openingParsed ?_
        validated, ?_⟩
      · simpa only [openingShape] using itemsParsed
      · simpa only [openingShape, State.diagnostics] using diagnostics

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.CoreBlockTraceCompletenessProperties
/-! Exact raw Core success traces from explicit statement completeness and
context laws. Production fuel suffices by strict cursor progress alone. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

variable {statement : Parser Statement}
  {statementTrace : SourceId → Nat → DeclarativeGrammar.Remainder → Statement →
    DeclarativeGrammar.Remainder → List ParseDiagnostic → Prop}

private theorem closing_present {input : State} {span : SourceSpan}
    {after : DeclarativeGrammar.Remainder}
    (parsed : DeclarativeGrammar.ExactTokenParses (.symbol .rightBrace)
      input.declarativeRemainder span after) : isSymbol input .rightBrace = true := by
  have token : DeclarativeGrammar.TokenAt input.tokens input.window.endIndex
      input.cursor { span, value := .symbol .rightBrace } := parsed.1
  unfold isSymbol State.peekKind? State.peek?
  simp only [token.1, ↓reduceIte, token.2, Option.map_some]
  rfl

/-- Sufficient remaining-token fuel executes any independent successful suffix.
The existing reverse prefix participates once in the final whole-body check. -/
theorem coreBlockItems_trace_success_complete
    (successComplete : StatementTraceSuccessComplete statement statementTrace)
    (contextFrame : StatementSuccessContext statement)
    (opening : Token) (policy : TailExpressionPolicy)
    (fuel : Nat) (bodyRev : List Statement)
    {input : State} {suffix : List Statement} {closingSpan : SourceSpan}
    {remainder : DeclarativeGrammar.Remainder}
    {statementEvents validationEvents : List ParseDiagnostic}
    (parsed : DeclarativeGrammar.CoreBlockItemsTraceParses statementTrace
      input.file.id input.window.endByte input.declarativeRemainder suffix
      closingSpan remainder statementEvents)
    (validated : DeclarativeGrammar.CoreBlockTailsDiagnosticTrace
      policy.declarative (bodyRev.reverse ++ suffix) validationEvents)
    (adequate : input.remainingCount < fuel) :
    ∃ output, coreBlockItems statement opening policy fuel bodyRev input = .ok {
        span := SourceSpan.cover opening.span closingSpan, value := bodyRev.reverse ++ suffix
      } output ∧ output.declarativeRemainder = remainder ∧
      output.diagnostics = input.diagnostics ++ (statementEvents ++ validationEvents) := by
  induction fuel generalizing bodyRev input suffix closingSpan remainder
      statementEvents validationEvents with
  | zero => omega
  | succ fuel ih =>
      cases parsed with
      | close span closing =>
          rcases (closeCoreBlock_trace_success_iff opening policy bodyRev).mp
              ⟨⟨closingSpan, closing, rfl⟩, by simpa only [List.append_nil] using validated⟩ with
            ⟨output, result, after, diagnostics⟩
          refine ⟨output, ?_, after, ?_⟩
          · simpa only [coreBlockItems, closing_present closing, if_true, List.append_nil]
              using result
          · simpa only [List.nil_append] using diagnostics
      | next inside absent headParsed progress tailParsed =>
          rename_i afterStatement head tail headEvents tailEvents
          rcases successComplete headParsed with ⟨next, headResult, afterEq, headEq⟩
          have frame := contextFrame headResult
          have nextProgress : input.cursor < next.cursor := by
            simpa only [← afterEq, State.declarativeRemainder] using progress
          have notEnded : input.atEnd = false :=
            decide_eq_false (Nat.not_le_of_gt inside)
          have tailAtNext : DeclarativeGrammar.CoreBlockItemsTraceParses statementTrace
              next.file.id next.window.endByte next.declarativeRemainder tail
              closingSpan remainder tailEvents := by
            simpa only [frame.1, frame.2, afterEq] using tailParsed
          have nextAdequate : next.remainingCount < fuel := by
            change input.cursor < input.window.endIndex at inside
            simp only [State.remainingCount, frame.2] at adequate ⊢
            omega
          have tailValidated : DeclarativeGrammar.CoreBlockTailsDiagnosticTrace
              policy.declarative ((head :: bodyRev).reverse ++ tail) validationEvents := by
            simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using validated
          rcases ih (head :: bodyRev) tailAtNext tailValidated nextAdequate with
            ⟨output, tailResult, outputAfter, outputEq⟩
          refine ⟨output, ?_, outputAfter, ?_⟩
          · simp only [coreBlockItems, closing_absent absent, Bool.false_eq_true, if_false,
              notEnded, headResult, nextProgress, if_true]
            simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using tailResult
          · rw [outputEq, headEq]
            simp only [List.append_assoc]

/-- The production loop bound suffices without valid-state or initially empty
diagnostic assumptions, and retains every appended event in its written order. -/
theorem coreBlockItems_production_trace_success_complete
    (successComplete : StatementTraceSuccessComplete statement statementTrace)
    (contextFrame : StatementSuccessContext statement)
    (opening : Token) (policy : TailExpressionPolicy) (bodyRev : List Statement)
    {input : State} {suffix : List Statement} {closingSpan : SourceSpan}
    {remainder : DeclarativeGrammar.Remainder}
    {statementEvents validationEvents : List ParseDiagnostic}
    (parsed : DeclarativeGrammar.CoreBlockItemsTraceParses statementTrace
      input.file.id input.window.endByte input.declarativeRemainder suffix
      closingSpan remainder statementEvents)
    (validated : DeclarativeGrammar.CoreBlockTailsDiagnosticTrace
      policy.declarative (bodyRev.reverse ++ suffix) validationEvents) :
    ∃ output, coreBlockItems statement opening policy (input.remainingCount + 1) bodyRev input =
      .ok { span := SourceSpan.cover opening.span closingSpan, value := bodyRev.reverse ++ suffix }
        output ∧ output.declarativeRemainder = remainder ∧
      output.diagnostics = input.diagnostics ++ (statementEvents ++ validationEvents) :=
  coreBlockItems_trace_success_complete successComplete contextFrame opening policy
    (input.remainingCount + 1) bodyRev parsed validated (by omega)

/-- Independent raw-block traces execute exactly under the explicit inner
statement completeness and source/full-window context contracts. -/
theorem coreBlock_trace_success_complete
    (successComplete : StatementTraceSuccessComplete statement statementTrace)
    (contextFrame : StatementSuccessContext statement) (policy : TailExpressionPolicy) :
    BlockTraceSuccessComplete (coreBlock statement policy)
      (DeclarativeGrammar.CoreBlockTraceParses statementTrace policy.declarative) := by
  intro input body remainder trace parsed
  cases parsed with
  | parsed opening closing openingParsed itemsParsed validated =>
      have openingResult := symbol_eq_ok_of_exactTokenParses .leftBrace .statement openingParsed
      rcases openingParsed with ⟨openingToken, rfl⟩
      rcases coreBlockItems_production_trace_success_complete successComplete contextFrame
          { span := opening, value := .symbol .leftBrace } policy []
          (input := { input with cursor := input.cursor + 1 })
          itemsParsed (by simpa only [List.reverse_nil, List.nil_append] using validated) with
        ⟨output, result, afterEq, diagnostics⟩
      refine ⟨output, ?_, afterEq, ?_⟩
      · simpa only [coreBlock, openingResult, List.reverse_nil, List.nil_append] using result
      · exact diagnostics

/-- Complete raw Core success is equivalent to its independent AST, remainder,
and appended trace. All assumptions are explicit abstract statement contracts. -/
theorem coreBlock_trace_success_iff
    (successSound : StatementTraceSuccessSound statement statementTrace)
    (successComplete : StatementTraceSuccessComplete statement statementTrace)
    (contextFrame : StatementSuccessContext statement) (policy : TailExpressionPolicy)
    {input : State} {body : Block} {remainder : DeclarativeGrammar.Remainder}
    {trace : List ParseDiagnostic} :
    DeclarativeGrammar.CoreBlockTraceParses statementTrace policy.declarative
      input.file.id input.window.endByte input.declarativeRemainder body remainder trace ↔
    ∃ output, coreBlock statement policy input = .ok body output ∧
      output.declarativeRemainder = remainder ∧ output.diagnostics = input.diagnostics ++ trace := by
  constructor
  · exact coreBlock_trace_success_complete successComplete contextFrame policy
  · rintro ⟨output, result, afterEq, diagnostics⟩
    rcases coreBlock_success_trace_sound successSound contextFrame policy result with
      ⟨actualTrace, parsed, actualEq⟩
    have events : actualTrace = trace := List.append_cancel_left (actualEq.symm.trans diagnostics)
    simpa only [afterEq, events] using parsed

/-- The item loop also has an exact production-fuel equivalence, retaining its
arbitrary reverse prefix and the split between fresh and final-check events. -/
theorem coreBlockItems_production_trace_success_iff
    (successSound : StatementTraceSuccessSound statement statementTrace)
    (successComplete : StatementTraceSuccessComplete statement statementTrace)
    (contextFrame : StatementSuccessContext statement)
    (opening : Token) (policy : TailExpressionPolicy) (bodyRev : List Statement)
    {input : State} {body : Block} {remainder : DeclarativeGrammar.Remainder}
    {trace : List ParseDiagnostic} :
    (∃ closingSpan suffix statementEvents validationEvents,
      body = { span := SourceSpan.cover opening.span closingSpan, value := bodyRev.reverse ++ suffix } ∧
      DeclarativeGrammar.CoreBlockItemsTraceParses statementTrace input.file.id input.window.endByte
        input.declarativeRemainder suffix closingSpan remainder statementEvents ∧
      DeclarativeGrammar.CoreBlockTailsDiagnosticTrace policy.declarative
        (bodyRev.reverse ++ suffix) validationEvents ∧ trace = statementEvents ++ validationEvents) ↔
    ∃ output, coreBlockItems statement opening policy (input.remainingCount + 1) bodyRev input =
      .ok body output ∧ output.declarativeRemainder = remainder ∧
        output.diagnostics = input.diagnostics ++ trace := by
  constructor
  · rintro ⟨closingSpan, suffix, statementEvents, validationEvents, rfl, parsed, validated, rfl⟩
    exact coreBlockItems_production_trace_success_complete successComplete contextFrame
      opening policy bodyRev parsed validated
  · rintro ⟨output, result, afterEq, diagnostics⟩
    rcases coreBlockItems_success_trace_sound successSound contextFrame opening policy
        (input.remainingCount + 1) bodyRev input body output result with
      ⟨closingSpan, suffix, statementEvents, validationEvents, bodyEq, parsed, validated, actualEq⟩
    exact ⟨closingSpan, suffix, statementEvents, validationEvents, bodyEq,
      afterEq ▸ parsed, validated, List.append_cancel_left (diagnostics.symm.trans actualEq)⟩

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.OptionalReturnValueTraceProperties
/-! Exact optional-return success with semicolon-first priority. Expression
events are retained unchanged, and the empty-value branch never invokes it. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.StatementSimpleInternals

variable {expression : Parser Expr}
  {expressionTrace : SourceId → Nat → DeclarativeGrammar.Remainder → Expr →
    DeclarativeGrammar.Remainder → List ParseDiagnostic → Prop}

theorem optionalReturnValue_eq_ok_none_of_tokenAt
    (expression : Parser Expr) {input : State} {span : SourceSpan}
    (current : DeclarativeGrammar.TokenAt input.tokens input.window.endIndex input.cursor
      { span, value := .symbol .semicolon }) :
    optionalReturnValue expression input = .ok none input := by
  have present : isSymbol input .semicolon = true := by
    unfold isSymbol State.peekKind? State.peek?
    simp only [current.1, ↓reduceIte, current.2, Option.map_some]
    rfl
  simp only [optionalReturnValue, getState, bind, present, if_true, pure]

/-- Absent semicolon delegates precisely one expression, propagating either
ordinary failure or success without changing any events or state fields. -/
theorem optionalReturnValue_eq_of_semicolonAbsent
    (expression : Parser Expr) {input : State}
    (absent : DeclarativeGrammar.TokenKindAbsentAt input.tokens input.window.endIndex
      input.cursor (.symbol .semicolon)) :
    optionalReturnValue expression input = match expression input with
      | .ok value output => .ok (some value) output
      | .reject failure rejected => .reject failure rejected
      | .invariant error => .invariant error := by
  have notPresent : isSymbol input .semicolon = false := by
    apply Bool.eq_false_iff.mpr
    intro present
    rcases symbol_eq_ok_of_isSymbol_eq_true .semicolon .statement present with ⟨token, result⟩
    exact absent ⟨token.span, (symbol_ok_tokenAt .semicolon .statement result).1⟩
  simp only [optionalReturnValue, getState, bind, notPresent, Bool.false_eq_true, if_false, pure]
  cases expression input <;> rfl

theorem optionalReturnValue_success_trace_sound
    (sound : ExpressionTraceSuccessSound expression expressionTrace)
    {input output : State} {value : Option Expr}
    (result : optionalReturnValue expression input = .ok value output) :
    ∃ trace, DeclarativeGrammar.OptionalReturnValueTraceParses expressionTrace
      input.file.id input.window.endByte input.declarativeRemainder value output.declarativeRemainder trace ∧
      output.diagnostics = input.diagnostics ++ trace := by
  by_cases present : isSymbol input .semicolon = true
  · rcases symbol_eq_ok_of_isSymbol_eq_true .semicolon .statement present with ⟨token, tokenResult⟩
    have current := (symbol_ok_tokenAt .semicolon .statement tokenResult).1
    rw [optionalReturnValue_eq_ok_none_of_tokenAt expression current] at result
    cases result
    exact ⟨[], .absent token.span current, by simp only [List.append_nil]⟩
  · have absent := symbolAbsentAt_of_isSymbol_eq_false .semicolon (Bool.eq_false_iff.mpr present)
    rw [optionalReturnValue_eq_of_semicolonAbsent expression absent] at result
    cases valueResult : expression input with
    | invariant error => simp [valueResult] at result
    | reject failure rejected => simp [valueResult] at result
    | ok expressionValue next =>
        simp only [valueResult] at result
        cases result
        rcases sound valueResult with ⟨trace, parsed, events⟩
        exact ⟨trace, .present absent parsed, events⟩

theorem optionalReturnValue_trace_success_complete
    (complete : ExpressionTraceSuccessComplete expression expressionTrace)
    {input : State} {value : Option Expr} {after : DeclarativeGrammar.Remainder}
    {trace : List ParseDiagnostic}
    (parsed : DeclarativeGrammar.OptionalReturnValueTraceParses expressionTrace
      input.file.id input.window.endByte input.declarativeRemainder value after trace) :
    ∃ output, optionalReturnValue expression input = .ok value output ∧
      output.declarativeRemainder = after ∧ output.diagnostics = input.diagnostics ++ trace := by
  cases parsed with
  | absent span current =>
      exact ⟨input, optionalReturnValue_eq_ok_none_of_tokenAt expression current, rfl,
        by simp only [List.append_nil]⟩
  | present absent valueParsed =>
      rcases complete valueParsed with ⟨output, result, afterEq, events⟩
      exact ⟨output, by rw [optionalReturnValue_eq_of_semicolonAbsent expression absent, result],
        afterEq, events⟩

theorem optionalReturnValue_success_context_eq
    (contextFrame : ExpressionSuccessContext expression)
    {input output : State} {value : Option Expr}
    (result : optionalReturnValue expression input = .ok value output) :
    output.file = input.file ∧ output.window = input.window := by
  unfold optionalReturnValue getState at result
  simp only [bind] at result
  cases present : isSymbol input .semicolon with
  | true => simp only [present, if_true, pure] at result; cases result; exact ⟨rfl, rfl⟩
  | false =>
      simp only [present, Bool.false_eq_true, if_false] at result
      cases valueResult : expression input with
      | invariant error => simp [valueResult] at result
      | reject failure rejected => simp [valueResult] at result
      | ok expressionValue next =>
          simp only [valueResult, pure] at result
          cases result
          exact contextFrame valueResult

theorem optionalReturnValue_trace_success_iff
    (sound : ExpressionTraceSuccessSound expression expressionTrace)
    (complete : ExpressionTraceSuccessComplete expression expressionTrace)
    {input : State} {value : Option Expr} {after : DeclarativeGrammar.Remainder}
    {trace : List ParseDiagnostic} :
    DeclarativeGrammar.OptionalReturnValueTraceParses expressionTrace
      input.file.id input.window.endByte input.declarativeRemainder value after trace ↔
    ∃ output, optionalReturnValue expression input = .ok value output ∧
      output.declarativeRemainder = after ∧ output.diagnostics = input.diagnostics ++ trace := by
  constructor
  · exact optionalReturnValue_trace_success_complete complete
  · rintro ⟨output, result, afterEq, diagnostics⟩
    rcases optionalReturnValue_success_trace_sound sound result with ⟨actualTrace, parsed, actualEq⟩
    have events : actualTrace = trace := List.append_cancel_left (actualEq.symm.trans diagnostics)
    simpa only [afterEq, events] using parsed

end Solcore.Syntax.Parser.StatementSimpleInternals
end

section
-- leanmerge: from Solcore.Syntax.Parser.ReturnStatementRejectionTraceSoundnessProperties
/-! Exact return-statement rejection keeps all expression events before the
first failure and leaves its full report uncommitted. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

variable {expression : Parser Expr}
  {expressionTrace : SourceId → Nat → DeclarativeGrammar.Remainder → Expr →
    DeclarativeGrammar.Remainder → List ParseDiagnostic → Prop}
  {expressionRejects : SourceId → Nat → DeclarativeGrammar.Remainder →
    DeclarativeGrammar.Remainder → ParseDiagnostic → List ParseDiagnostic → Prop}

/-- The failure is exactly keyword, value, or mandatory-semicolon rejection.
Expression success retains source and byte context for the final report. -/
theorem returnStatement_reject_trace_sound
    (successSound : ExpressionTraceSuccessSound expression expressionTrace)
    (rejectSound : ExpressionTraceRejectSound expression expressionRejects)
    (contextFrame : ExpressionSuccessContext expression) :
    StatementTraceRejectSound (returnStatement expression)
      (DeclarativeGrammar.ReturnStatementTraceRejects expressionTrace expressionRejects) := by
  intro input rejected failure result
  unfold returnStatement at result
  cases markerResult : keyword .returnKw .statement input with
  | invariant error => simp [bind, markerResult] at result
  | reject markerFailure markerRejected =>
      have shape := acceptToken_reject_state_shape (.keyword .returnKw) .statement
        (· == .keyword .returnKw) markerResult
      subst markerRejected
      simp only [bind, markerResult] at result
      cases result
      have reported := (keyword_reject_reports_iff .returnKw .statement).mpr
        ⟨failure, markerResult, rfl⟩
      exact ⟨[], .markerRejected reported.1 reported.2, by simp⟩
  | ok marker afterMarker =>
      simp only [bind, markerResult] at result
      have markerParsed := keyword_success_exactTokenParses .returnKw .statement markerResult
      have markerShape := (keyword_ok_tokenAt .returnKw .statement markerResult).2
      cases valueResult : StatementSimpleInternals.optionalReturnValue expression afterMarker with
      | invariant error => simp [valueResult] at result
      | reject valueFailure valueRejected =>
          simp only [valueResult] at result
          cases result
          rcases StatementSimpleInternals.optionalReturnValue_reject_trace_sound rejectSound valueResult with
            ⟨trace, rejection, diagnostics⟩
          refine ⟨trace, .valueRejected marker.span markerParsed ?_, ?_⟩
          · simpa only [markerShape] using rejection
          · simpa only [markerShape, State.diagnostics] using diagnostics
      | ok value afterValue =>
          simp only [valueResult] at result
          cases semicolonResult : symbol .semicolon .statement afterValue with
          | invariant error => simp [semicolonResult] at result
          | ok semicolon output => simp [semicolonResult, pure] at result
          | reject semicolonFailure semicolonRejected =>
              have shape := acceptToken_reject_state_shape (.symbol .semicolon) .statement
                (· == .symbol .semicolon) semicolonResult
              subst semicolonRejected
              simp only [semicolonResult] at result
              cases result
              rcases StatementSimpleInternals.optionalReturnValue_success_trace_sound successSound valueResult with
                ⟨trace, valueParsed, diagnostics⟩
              have frame := StatementSimpleInternals.optionalReturnValue_success_context_eq contextFrame valueResult
              have reported := (symbol_reject_reports_iff .semicolon .statement).mpr
                ⟨failure, semicolonResult, rfl⟩
              refine ⟨trace, .semicolonRejected (value := value)
                marker.span markerParsed ?_ reported.1 ?_, ?_⟩
              · simpa only [markerShape] using valueParsed
              · simpa only [frame.1, frame.2, markerShape] using reported.2
              · simpa only [markerShape, State.diagnostics] using diagnostics

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.ReturnStatementRejectionTraceCompletenessProperties
/-! Complete return rejection correspondence under expression contracts.
Semicolon rejection preserves successful value events before its exact report. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

variable {expression : Parser Expr}
  {expressionTrace : SourceId → Nat → DeclarativeGrammar.Remainder → Expr →
    DeclarativeGrammar.Remainder → List ParseDiagnostic → Prop}
  {expressionRejects : SourceId → Nat → DeclarativeGrammar.Remainder →
    DeclarativeGrammar.Remainder → ParseDiagnostic → List ParseDiagnostic → Prop}

theorem returnStatement_trace_reject_complete
    (successComplete : ExpressionTraceSuccessComplete expression expressionTrace)
    (rejectComplete : ExpressionTraceRejectComplete expression expressionRejects)
    (contextFrame : ExpressionSuccessContext expression) :
    StatementTraceRejectComplete (returnStatement expression)
      (DeclarativeGrammar.ReturnStatementTraceRejects expressionTrace expressionRejects) := by
  intro input remainder diagnostic trace rejection
  cases rejection with
  | markerRejected absent reported =>
      rcases (keyword_reject_reports_iff .returnKw .statement).mp ⟨absent, reported⟩ with
        ⟨failure, result, reportEq⟩
      exact ⟨failure, input, by simp only [returnStatement, bind, result], rfl, reportEq, by simp⟩
  | valueRejected marker markerParsed valueRejected =>
      have markerResult := keyword_eq_ok_of_exactTokenParses .returnKw .statement markerParsed
      rcases markerParsed with ⟨markerToken, rfl⟩
      rcases StatementSimpleInternals.optionalReturnValue_trace_reject_complete rejectComplete
          (input := { input with cursor := input.cursor + 1 }) valueRejected with
        ⟨failure, rejected, result, afterEq, reportEq, diagnostics⟩
      exact ⟨failure, rejected, by simp only [returnStatement, bind, markerResult, result],
        afterEq, reportEq, diagnostics⟩
  | semicolonRejected marker markerParsed valueParsed absent reported =>
      have markerResult := keyword_eq_ok_of_exactTokenParses .returnKw .statement markerParsed
      rcases markerParsed with ⟨markerToken, rfl⟩
      rcases StatementSimpleInternals.optionalReturnValue_trace_success_complete successComplete
          (input := { input with cursor := input.cursor + 1 }) valueParsed with
        ⟨afterValue, valueResult, afterEq, diagnostics⟩
      have frame := StatementSimpleInternals.optionalReturnValue_success_context_eq contextFrame valueResult
      have absentAtValue : DeclarativeGrammar.TokenKindAbsentAt afterValue.tokens
          afterValue.window.endIndex afterValue.cursor (.symbol .semicolon) := by
        simpa only [← afterEq, State.declarativeRemainder] using absent
      have reportedAtValue : DeclarativeGrammar.RejectAtReports afterValue.file.id afterValue.window.endByte
          { head := .symbol .semicolon, tail := [] } .statement afterValue.declarativeRemainder diagnostic := by
        simpa only [frame.1, frame.2, afterEq] using reported
      rcases (symbol_reject_reports_iff .semicolon .statement).mp ⟨absentAtValue, reportedAtValue⟩ with
        ⟨failure, semicolonResult, reportEq⟩
      exact ⟨failure, afterValue, by
        simp only [returnStatement, bind, markerResult, valueResult, semicolonResult],
        afterEq, reportEq, diagnostics⟩

theorem returnStatement_trace_reject_iff
    (successSound : ExpressionTraceSuccessSound expression expressionTrace)
    (rejectSound : ExpressionTraceRejectSound expression expressionRejects)
    (successComplete : ExpressionTraceSuccessComplete expression expressionTrace)
    (rejectComplete : ExpressionTraceRejectComplete expression expressionRejects)
    (contextFrame : ExpressionSuccessContext expression)
    {input : State} {remainder : DeclarativeGrammar.Remainder}
    {diagnostic : ParseDiagnostic} {trace : List ParseDiagnostic} :
    DeclarativeGrammar.ReturnStatementTraceRejects expressionTrace expressionRejects
      input.file.id input.window.endByte input.declarativeRemainder remainder diagnostic trace ↔
    ∃ failure rejected, returnStatement expression input = .reject failure rejected ∧
      rejected.declarativeRemainder = remainder ∧ failure.toDiagnostic = diagnostic ∧
      rejected.diagnostics = input.diagnostics ++ trace := by
  constructor
  · exact returnStatement_trace_reject_complete successComplete rejectComplete contextFrame
  · rintro ⟨failure, rejected, result, afterEq, reportEq, diagnostics⟩
    rcases returnStatement_reject_trace_sound successSound rejectSound contextFrame result with
      ⟨actualTrace, rejection, actualEq⟩
    have events : actualTrace = trace := List.append_cancel_left (actualEq.symm.trans diagnostics)
    simpa only [afterEq, reportEq, events] using rejection

/-- The independent diagnostic fixes every field of the uncommitted failure,
while preserving the complete remainder and preceding diagnostic suffix. -/
theorem returnStatement_trace_reject_failure_iff
    (successSound : ExpressionTraceSuccessSound expression expressionTrace)
    (rejectSound : ExpressionTraceRejectSound expression expressionRejects)
    (successComplete : ExpressionTraceSuccessComplete expression expressionTrace)
    (rejectComplete : ExpressionTraceRejectComplete expression expressionRejects)
    (contextFrame : ExpressionSuccessContext expression)
    {input : State} {remainder : DeclarativeGrammar.Remainder}
    {failure : Failure} {trace : List ParseDiagnostic} :
    DeclarativeGrammar.ReturnStatementTraceRejects expressionTrace expressionRejects
      input.file.id input.window.endByte input.declarativeRemainder remainder failure.toDiagnostic trace ↔
    ∃ rejected, returnStatement expression input = .reject failure rejected ∧
      rejected.declarativeRemainder = remainder ∧ rejected.diagnostics = input.diagnostics ++ trace := by
  rw [returnStatement_trace_reject_iff successSound rejectSound successComplete rejectComplete contextFrame]
  constructor
  · rintro ⟨actual, rejected, result, afterEq, reportEq, diagnostics⟩
    cases Failure.toDiagnostic_injective reportEq
    exact ⟨rejected, result, afterEq, diagnostics⟩
  · rintro ⟨rejected, result, afterEq, diagnostics⟩
    exact ⟨failure, rejected, result, afterEq, rfl, diagnostics⟩

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.ReturnStatementSuccessTraceProperties
/-! Exact successful return statements from explicit expression trace laws.
The keyword and semicolon are silent; only the optional expression adds events. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

variable {expression : Parser Expr}
  {expressionTrace : SourceId → Nat → DeclarativeGrammar.Remainder → Expr →
    DeclarativeGrammar.Remainder → List ParseDiagnostic → Prop}

private theorem bind_ok_components {alpha beta : Type}
    {first : Parser alpha} {next : alpha → Parser beta}
    {input output : State} {value : beta}
    (result : (first >>= next) input = .ok value output) :
    ∃ firstValue afterFirst, first input = .ok firstValue afterFirst ∧
      next firstValue afterFirst = .ok value output := by
  change (match first input with
    | .ok firstValue afterFirst => next firstValue afterFirst
    | .reject failure rejected => .reject failure rejected
    | .invariant error => .invariant error) = .ok value output at result
  cases firstResult : first input with
  | ok firstValue afterFirst =>
      rw [firstResult] at result
      exact ⟨firstValue, afterFirst, rfl, result⟩
  | reject failure rejected => rw [firstResult] at result; contradiction
  | invariant error => rw [firstResult] at result; contradiction

/-- `return;` never invokes the supplied expression parser. Its unconditional
execution changes only the cursor, even if that parser would fail or emit events. -/
theorem returnStatement_eq_ok_none_of_exactTokens
    (expression : Parser Expr) {input : State} {afterMarker after : DeclarativeGrammar.Remainder}
    {markerSpan semicolonSpan : SourceSpan}
    (marker : DeclarativeGrammar.ExactTokenParses (.keyword .returnKw)
      input.declarativeRemainder markerSpan afterMarker)
    (semicolon : DeclarativeGrammar.ExactTokenParses (.symbol .semicolon)
      afterMarker semicolonSpan after) :
    returnStatement expression input = .ok {
      span := SourceSpan.cover markerSpan semicolonSpan, value := .returnStmt none
    } { input with cursor := input.cursor + 2 } := by
  have markerResult := keyword_eq_ok_of_exactTokenParses .returnKw .statement marker
  rcases marker with ⟨_, rfl⟩
  have valueResult := StatementSimpleInternals.optionalReturnValue_eq_ok_none_of_tokenAt
    expression (input := { input with cursor := input.cursor + 1 }) semicolon.1
  have semicolonResult := symbol_eq_ok_of_exactTokenParses .semicolon .statement
    (input := { input with cursor := input.cursor + 1 }) semicolon
  simp only [returnStatement, bind, markerResult, valueResult, semicolonResult, pure]

theorem returnStatement_trace_success_sound
    (sound : ExpressionTraceSuccessSound expression expressionTrace) :
    StatementTraceSuccessSound (returnStatement expression)
      (DeclarativeGrammar.ReturnStatementTraceParses expressionTrace) := by
  intro input output statement result
  unfold returnStatement at result
  rcases bind_ok_components result with ⟨marker, afterMarker, markerResult, valueStage⟩
  rcases bind_ok_components valueStage with ⟨value, afterValue, valueResult, semicolonStage⟩
  rcases bind_ok_components semicolonStage with ⟨semicolon, next, semicolonResult, finished⟩
  cases finished
  rcases StatementSimpleInternals.optionalReturnValue_success_trace_sound sound valueResult with
    ⟨trace, valueParsed, events⟩
  have markerShape := (keyword_ok_tokenAt .returnKw .statement markerResult).2
  have semicolonShape := (symbol_ok_tokenAt .semicolon .statement semicolonResult).2
  refine ⟨trace, .parsed marker.span semicolon.span
    (keyword_success_exactTokenParses .returnKw .statement markerResult) ?_
    (symbol_success_exactTokenParses .semicolon .statement semicolonResult), ?_⟩
  · simpa only [markerShape] using valueParsed
  · rw [semicolonShape]
    simpa only [markerShape, State.diagnostics] using events

theorem returnStatement_trace_success_complete
    (complete : ExpressionTraceSuccessComplete expression expressionTrace) :
    StatementTraceSuccessComplete (returnStatement expression)
      (DeclarativeGrammar.ReturnStatementTraceParses expressionTrace) := by
  intro input statement after trace parsed
  cases parsed with
  | parsed marker semicolon markerParsed valueParsed semicolonParsed =>
      have markerResult := keyword_eq_ok_of_exactTokenParses .returnKw .statement markerParsed
      rcases markerParsed with ⟨_, rfl⟩
      rcases StatementSimpleInternals.optionalReturnValue_trace_success_complete complete
          (input := { input with cursor := input.cursor + 1 }) valueParsed with
        ⟨afterValue, valueResult, valueAfter, events⟩
      rw [← valueAfter] at semicolonParsed
      have semicolonResult := symbol_eq_ok_of_exactTokenParses .semicolon .statement semicolonParsed
      refine ⟨{ afterValue with cursor := afterValue.cursor + 1 }, ?_, semicolonParsed.2.symm, ?_⟩
      · simp only [returnStatement, bind, markerResult, valueResult, semicolonResult, pure]
      · simpa only [State.diagnostics] using events

theorem returnStatement_success_context
    (contextFrame : ExpressionSuccessContext expression) :
    StatementSuccessContext (returnStatement expression) := by
  intro input output statement result
  unfold returnStatement at result
  rcases bind_ok_components result with ⟨marker, afterMarker, markerResult, valueStage⟩
  rcases bind_ok_components valueStage with ⟨value, afterValue, valueResult, semicolonStage⟩
  rcases bind_ok_components semicolonStage with ⟨semicolon, next, semicolonResult, finished⟩
  cases finished
  have markerShape := (keyword_ok_tokenAt .returnKw .statement markerResult).2
  have semicolonShape := (symbol_ok_tokenAt .semicolon .statement semicolonResult).2
  have frame := StatementSimpleInternals.optionalReturnValue_success_context_eq contextFrame valueResult
  simpa only [semicolonShape, markerShape] using frame

/-- Return success retains the complete optional-value AST, token remainder,
and expression trace. General expressions remain an explicit conditional input. -/
theorem returnStatement_trace_success_iff
    (sound : ExpressionTraceSuccessSound expression expressionTrace)
    (complete : ExpressionTraceSuccessComplete expression expressionTrace)
    {input : State} {statement : Statement} {after : DeclarativeGrammar.Remainder}
    {trace : List ParseDiagnostic} :
    DeclarativeGrammar.ReturnStatementTraceParses expressionTrace
      input.file.id input.window.endByte input.declarativeRemainder statement after trace ↔
    ∃ output, returnStatement expression input = .ok statement output ∧
      output.declarativeRemainder = after ∧ output.diagnostics = input.diagnostics ++ trace := by
  constructor
  · exact returnStatement_trace_success_complete complete
  · rintro ⟨output, result, afterEq, diagnostics⟩
    rcases returnStatement_trace_success_sound sound result with ⟨actualTrace, parsed, actualEq⟩
    have events : actualTrace = trace := List.append_cancel_left (actualEq.symm.trans diagnostics)
    simpa only [afterEq, events] using parsed

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.CoreBlockContextProperties
/-! Successful raw Core blocks preserve source and the complete token/byte
window under the corresponding inner statement frame law, for arbitrary events. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

theorem coreBlockItems_success_context_eq
    {statement : Parser Statement} (contextFrame : StatementSuccessContext statement)
    (opening : Token) (policy : TailExpressionPolicy) :
    ∀ fuel bodyRev input body output,
      coreBlockItems statement opening policy fuel bodyRev input = .ok body output →
        output.file = input.file ∧ output.window = input.window := by
  intro fuel
  induction fuel with
  | zero => intro bodyRev input body output result; simp [coreBlockItems] at result
  | succ fuel ih =>
      intro bodyRev input body output result
      unfold coreBlockItems at result
      cases closingPresent : isSymbol input .rightBrace with
      | true =>
          simp only [closingPresent, if_true] at result
          exact closeCoreBlock_success_context_eq opening policy bodyRev result
      | false =>
          simp only [closingPresent, Bool.false_eq_true, if_false] at result
          cases ended : input.atEnd with
          | true =>
              simp only [ended, if_true] at result
              cases closingResult : symbol .rightBrace .statement input <;> simp [closingResult] at result
          | false =>
              simp only [ended, Bool.false_eq_true, if_false] at result
              cases statementResult : statement input with
              | invariant error => simp [statementResult] at result
              | reject failure rejected => simp [statementResult] at result
              | ok value next =>
                  simp only [statementResult] at result
                  by_cases progress : next.cursor > input.cursor
                  · simp only [progress, if_true] at result
                    have tail := ih (value :: bodyRev) next body output result
                    have head := contextFrame statementResult
                    exact ⟨tail.1.trans head.1, tail.2.trans head.2⟩
                  · simp only [progress, if_false] at result
                    contradiction

theorem coreBlock_success_context_eq
    {statement : Parser Statement} (contextFrame : StatementSuccessContext statement)
    (policy : TailExpressionPolicy) {input output : State} {body : Block}
    (result : coreBlock statement policy input = .ok body output) :
    output.file = input.file ∧ output.window = input.window := by
  unfold coreBlock at result
  cases openingResult : symbol .leftBrace .statement input with
  | invariant error => simp [openingResult] at result
  | reject failure rejected => simp [openingResult] at result
  | ok opening afterOpening =>
      simp only [openingResult] at result
      have frame := coreBlockItems_success_context_eq contextFrame opening policy
        (afterOpening.remainingCount + 1) [] afterOpening body output result
      have shape := (symbol_ok_tokenAt .leftBrace .statement openingResult).2
      simpa only [shape] using frame

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.BlockStatementTraceProperties
/-! Exact block-statement traces map the required-policy raw Core block.
Ordinary failures escape unchanged; no isolation or recovery occurs here. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

variable {statement : Parser Statement}
  {statementTrace : SourceId → Nat → DeclarativeGrammar.Remainder → Statement →
    DeclarativeGrammar.Remainder → List ParseDiagnostic → Prop}
  {statementRejects : SourceId → Nat → DeclarativeGrammar.Remainder →
    DeclarativeGrammar.Remainder → ParseDiagnostic → List ParseDiagnostic → Prop}

/-- The AST map is the only successful effect of the statement wrapper. -/
theorem blockStatement_success_iff_raw
    {input output : State} {value : Statement} :
    blockStatement statement input = .ok value output ↔
      ∃ body, coreBlock statement .require input = .ok body output ∧
        value = { span := body.span, value := .block body.value } := by
  cases result : coreBlock statement .require input <;>
    simp only [blockStatement, bind, result, pure, reduceCtorEq, Reply.ok.injEq]
  case ok body next =>
    constructor
    · rintro ⟨rfl, rfl⟩; exact ⟨body, ⟨rfl, rfl⟩, rfl⟩
    · rintro ⟨other, ⟨rfl, rfl⟩, rfl⟩; exact ⟨rfl, rfl⟩
  case reject => simp
  case invariant => simp

/-- The whole failure and rejected state are propagated directly from the
raw block. In particular, the wrapper does not commit a recovery report. -/
theorem blockStatement_reject_iff_raw
    {input rejected : State} {failure : Failure} :
    blockStatement statement input = .reject failure rejected ↔
      coreBlock statement .require input = .reject failure rejected := by
  cases result : coreBlock statement .require input <;>
    simp only [blockStatement, bind, result, pure, reduceCtorEq, Reply.reject.injEq, iff_self]

theorem blockStatement_trace_success_sound
    (successSound : StatementTraceSuccessSound statement statementTrace)
    (contextFrame : StatementSuccessContext statement) :
    StatementTraceSuccessSound (blockStatement statement)
      (DeclarativeGrammar.BlockStatementTraceParses statementTrace) := by
  intro input output value result
  rcases blockStatement_success_iff_raw.mp result with ⟨body, raw, rfl⟩
  rcases coreBlock_success_trace_sound successSound contextFrame .require raw with
    ⟨trace, parsed, diagnostics⟩
  exact ⟨trace, .parsed parsed, diagnostics⟩

theorem blockStatement_trace_reject_sound
    (successSound : StatementTraceSuccessSound statement statementTrace)
    (rejectSound : StatementTraceRejectSound statement statementRejects)
    (contextFrame : StatementSuccessContext statement) :
    StatementTraceRejectSound (blockStatement statement)
      (DeclarativeGrammar.BlockStatementTraceRejects statementTrace statementRejects) := by
  intro input rejected failure result
  rcases coreBlock_reject_trace_sound successSound rejectSound contextFrame .require
      (blockStatement_reject_iff_raw.mp result) with ⟨trace, rejection, diagnostics⟩
  exact ⟨trace, .rejected rejection, diagnostics⟩

theorem blockStatement_trace_success_complete
    (successComplete : StatementTraceSuccessComplete statement statementTrace)
    (contextFrame : StatementSuccessContext statement) :
    StatementTraceSuccessComplete (blockStatement statement)
      (DeclarativeGrammar.BlockStatementTraceParses statementTrace) := by
  intro input value remainder trace parsed
  cases parsed with
  | parsed bodyParsed =>
      rcases coreBlock_trace_success_complete successComplete contextFrame .require bodyParsed with
        ⟨output, result, afterEq, diagnostics⟩
      exact ⟨output, blockStatement_success_iff_raw.mpr ⟨_, result, rfl⟩, afterEq, diagnostics⟩

theorem blockStatement_trace_reject_complete
    (successComplete : StatementTraceSuccessComplete statement statementTrace)
    (rejectComplete : StatementTraceRejectComplete statement statementRejects)
    (contextFrame : StatementSuccessContext statement) :
    StatementTraceRejectComplete (blockStatement statement)
      (DeclarativeGrammar.BlockStatementTraceRejects statementTrace statementRejects) := by
  intro input remainder diagnostic trace rejection
  cases rejection with
  | rejected bodyRejected =>
      rcases coreBlock_trace_reject_complete successComplete rejectComplete contextFrame .require
          bodyRejected with ⟨failure, rejected, result, afterEq, reportEq, diagnostics⟩
      exact ⟨failure, rejected, blockStatement_reject_iff_raw.mpr result, afterEq, reportEq, diagnostics⟩

theorem blockStatement_success_context
    (contextFrame : StatementSuccessContext statement) :
    StatementSuccessContext (blockStatement statement) := by
  intro input output value result
  rcases blockStatement_success_iff_raw.mp result with ⟨body, raw, _⟩
  exact coreBlock_success_context_eq contextFrame .require raw

theorem blockStatement_trace_success_iff
    (successSound : StatementTraceSuccessSound statement statementTrace)
    (successComplete : StatementTraceSuccessComplete statement statementTrace)
    (contextFrame : StatementSuccessContext statement)
    {input : State} {value : Statement} {remainder : DeclarativeGrammar.Remainder}
    {trace : List ParseDiagnostic} :
    DeclarativeGrammar.BlockStatementTraceParses statementTrace input.file.id input.window.endByte
      input.declarativeRemainder value remainder trace ↔
    ∃ output, blockStatement statement input = .ok value output ∧
      output.declarativeRemainder = remainder ∧ output.diagnostics = input.diagnostics ++ trace := by
  constructor
  · exact blockStatement_trace_success_complete successComplete contextFrame
  · rintro ⟨output, result, afterEq, diagnostics⟩
    rcases blockStatement_trace_success_sound successSound contextFrame result with
      ⟨actualTrace, parsed, actualEq⟩
    have events : actualTrace = trace := List.append_cancel_left (actualEq.symm.trans diagnostics)
    simpa only [afterEq, events] using parsed

theorem blockStatement_trace_reject_iff
    (successSound : StatementTraceSuccessSound statement statementTrace)
    (rejectSound : StatementTraceRejectSound statement statementRejects)
    (successComplete : StatementTraceSuccessComplete statement statementTrace)
    (rejectComplete : StatementTraceRejectComplete statement statementRejects)
    (contextFrame : StatementSuccessContext statement)
    {input : State} {remainder : DeclarativeGrammar.Remainder}
    {diagnostic : ParseDiagnostic} {trace : List ParseDiagnostic} :
    DeclarativeGrammar.BlockStatementTraceRejects statementTrace statementRejects
      input.file.id input.window.endByte input.declarativeRemainder remainder diagnostic trace ↔
    ∃ failure rejected, blockStatement statement input = .reject failure rejected ∧
      rejected.declarativeRemainder = remainder ∧ failure.toDiagnostic = diagnostic ∧
      rejected.diagnostics = input.diagnostics ++ trace := by
  constructor
  · exact blockStatement_trace_reject_complete successComplete rejectComplete contextFrame
  · rintro ⟨failure, rejected, result, afterEq, reportEq, diagnostics⟩
    rcases blockStatement_trace_reject_sound successSound rejectSound contextFrame result with
      ⟨actualTrace, rejection, actualEq⟩
    have events : actualTrace = trace := List.append_cancel_left (actualEq.symm.trans diagnostics)
    simpa only [afterEq, reportEq, events] using rejection

theorem blockStatement_trace_reject_failure_iff
    (successSound : StatementTraceSuccessSound statement statementTrace)
    (rejectSound : StatementTraceRejectSound statement statementRejects)
    (successComplete : StatementTraceSuccessComplete statement statementTrace)
    (rejectComplete : StatementTraceRejectComplete statement statementRejects)
    (contextFrame : StatementSuccessContext statement)
    {input : State} {remainder : DeclarativeGrammar.Remainder}
    {failure : Failure} {trace : List ParseDiagnostic} :
    DeclarativeGrammar.BlockStatementTraceRejects statementTrace statementRejects
      input.file.id input.window.endByte input.declarativeRemainder remainder failure.toDiagnostic trace ↔
    ∃ rejected, blockStatement statement input = .reject failure rejected ∧
      rejected.declarativeRemainder = remainder ∧ rejected.diagnostics = input.diagnostics ++ trace := by
  rw [blockStatement_trace_reject_iff successSound rejectSound successComplete rejectComplete contextFrame]
  constructor
  · rintro ⟨actual, rejected, result, afterEq, reportEq, diagnostics⟩
    cases Failure.toDiagnostic_injective reportEq
    exact ⟨rejected, result, afterEq, diagnostics⟩
  · rintro ⟨rejected, result, afterEq, diagnostics⟩
    exact ⟨failure, rejected, result, afterEq, rfl, diagnostics⟩

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.IsolatedBlockDiagnosticTraceProperties
/-! Compositional laws from executable child outcomes, not independent grammar
judgments. Balanced isolation resets child diagnostics and restores the parent. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Entering any child window starts a fresh diagnostic sequence. -/
theorem State.enterWindow_diagnostics_eq_nil
    (input : State) (startIndex : Nat) (window : TokenWindow) :
    (input.enterWindow startIndex window).diagnostics = [] := rfl

/-- Merging preserves every event, including duplicates, in parent-child order. -/
theorem State.mergeDiagnostics_diagnostics_eq_append (parent child : State) :
    (parent.mergeDiagnostics child).diagnostics = parent.diagnostics ++ child.diagnostics := by
  simp only [State.mergeDiagnostics, State.diagnostics, List.reverse_append]

/-- Without a balanced capture, isolation is exactly the underlying parser,
including its successful value, rejected state, or invariant failure. -/
theorem isolateBlock_eq_of_no_capture (parser : Parser Block) {input : State}
    (notCaptured : BlockInternals.captureBlock? input = none) :
    isolateBlock parser input = parser input := by
  simp only [isolateBlock, notCaptured]

/-- Captured success retains the child AST but restores the parent carrier
and cursor boundary, merging the complete child trace after the parent's. -/
theorem isolateBlock_captured_success_trace
    {parser : Parser Block} {input childAfter : State} {body : Block}
    {captured : BlockInternals.CapturedBlock}
    (capture : BlockInternals.captureBlock? input = some captured)
    (childResult : parser (input.enterWindow input.cursor captured.window) = .ok body childAfter) :
    isolateBlock parser input = .ok body
        (({ input with cursor := captured.window.endIndex } : State).mergeDiagnostics childAfter) ∧
      (({ input with cursor := captured.window.endIndex } : State).mergeDiagnostics childAfter).diagnostics =
        input.diagnostics ++ childAfter.diagnostics := by
  refine ⟨by simp only [isolateBlock, capture, childResult], ?_⟩
  exact State.mergeDiagnostics_diagnostics_eq_append _ _

/-- Captured ordinary rejection recovers an empty body at the captured span.
Its exact failure report is committed once, after parent and child events. -/
theorem isolateBlock_captured_reject_trace
    {parser : Parser Block} {input childAfter : State} {failure : Failure}
    {captured : BlockInternals.CapturedBlock}
    (capture : BlockInternals.captureBlock? input = some captured)
    (childResult : parser (input.enterWindow input.cursor captured.window) = .reject failure childAfter) :
    isolateBlock parser input = .ok { span := captured.span, value := [] }
        ((({ input with cursor := captured.window.endIndex } : State).mergeDiagnostics childAfter).emit
          failure.toDiagnostic) ∧
      ((({ input with cursor := captured.window.endIndex } : State).mergeDiagnostics childAfter).emit
        failure.toDiagnostic).diagnostics =
        input.diagnostics ++ childAfter.diagnostics ++ [failure.toDiagnostic] := by
  refine ⟨by simp only [isolateBlock, capture, childResult], ?_⟩
  simp only [State.emit, State.mergeDiagnostics, State.diagnostics,
    List.reverse_cons, List.reverse_append]

/-- Invariants remain invariants; they do not become empty-body recovery. -/
theorem isolateBlock_captured_invariant_iff
    {parser : Parser Block} {input : State} {error : ParserInvariantError}
    {captured : BlockInternals.CapturedBlock}
    (capture : BlockInternals.captureBlock? input = some captured) :
    isolateBlock parser input = .invariant error ↔
      parser (input.enterWindow input.cursor captured.window) = .invariant error := by
  simp only [isolateBlock, capture]
  cases childResult : parser (input.enterWindow input.cursor captured.window) <;> simp

/-- Exact captured-success classification separates ordinary child success
from recovered child rejection; the two cases retain their exact states. -/
theorem isolateBlock_captured_success_iff
    {parser : Parser Block} {input output : State} {body : Block}
    {captured : BlockInternals.CapturedBlock}
    (capture : BlockInternals.captureBlock? input = some captured) :
    isolateBlock parser input = .ok body output ↔
      (∃ childAfter,
        parser (input.enterWindow input.cursor captured.window) = .ok body childAfter ∧
        output = ({ input with cursor := captured.window.endIndex } : State).mergeDiagnostics childAfter) ∨
      (∃ failure childAfter,
        parser (input.enterWindow input.cursor captured.window) = .reject failure childAfter ∧
        body = { span := captured.span, value := [] } ∧
        output = (({ input with cursor := captured.window.endIndex } : State).mergeDiagnostics
          childAfter).emit failure.toDiagnostic) := by
  constructor
  · intro result
    simp only [isolateBlock, capture] at result
    cases childResult : parser (input.enterWindow input.cursor captured.window) with
    | invariant error => simp [childResult] at result
    | ok childBody childAfter =>
        simp only [childResult] at result
        cases result
        exact .inl ⟨childAfter, rfl, rfl⟩
    | reject failure childAfter =>
        simp only [childResult] at result
        cases result
        exact .inr ⟨failure, childAfter, rfl, rfl, rfl⟩
  · rintro (⟨childAfter, childResult, rfl⟩ | ⟨failure, childAfter, childResult, rfl, rfl⟩)
    · exact (isolateBlock_captured_success_trace capture childResult).1
    · exact (isolateBlock_captured_reject_trace capture childResult).1

/-- Every captured success restores the parent's complete source context and
resumes precisely after the closing brace, regardless of the child's cursor. -/
theorem isolateBlock_captured_success_frame
    {parser : Parser Block} {input output : State} {body : Block}
    {captured : BlockInternals.CapturedBlock}
    (capture : BlockInternals.captureBlock? input = some captured)
    (result : isolateBlock parser input = .ok body output) :
    output.file = input.file ∧ output.tokens = input.tokens ∧
      output.window = input.window ∧ output.cursor = captured.window.endIndex := by
  rcases (isolateBlock_captured_success_iff capture).mp result with
    ⟨childAfter, childResult, rfl⟩ | ⟨failure, childAfter, childResult, rfl, rfl⟩
  all_goals exact ⟨rfl, rfl, rfl, rfl⟩

/-- Forward diagnostic classification retains both branches' exact event order,
without claiming that either executable child outcome is an independent grammar. -/
theorem isolateBlock_captured_success_trace_cases
    {parser : Parser Block} {input output : State} {body : Block}
    {captured : BlockInternals.CapturedBlock}
    (capture : BlockInternals.captureBlock? input = some captured)
    (result : isolateBlock parser input = .ok body output) :
    (∃ childAfter,
      parser (input.enterWindow input.cursor captured.window) = .ok body childAfter ∧
      output.diagnostics = input.diagnostics ++ childAfter.diagnostics) ∨
    (∃ failure childAfter,
      parser (input.enterWindow input.cursor captured.window) = .reject failure childAfter ∧
      body = { span := captured.span, value := [] } ∧
      output.diagnostics = input.diagnostics ++ childAfter.diagnostics ++ [failure.toDiagnostic]) := by
  rcases (isolateBlock_captured_success_iff capture).mp result with
    ⟨childAfter, childResult, rfl⟩ | ⟨failure, childAfter, childResult, rfl, rfl⟩
  · exact .inl ⟨childAfter, childResult, (isolateBlock_captured_success_trace capture childResult).2⟩
  · exact .inr ⟨failure, childAfter, childResult, rfl,
      (isolateBlock_captured_reject_trace capture childResult).2⟩

/-- Balanced isolation never returns an ordinary rejection to its parent. -/
theorem isolateBlock_captured_ne_reject
    {parser : Parser Block} {input rejected : State} {failure : Failure}
    {captured : BlockInternals.CapturedBlock}
    (capture : BlockInternals.captureBlock? input = some captured) :
    isolateBlock parser input ≠ .reject failure rejected := by
  simp only [isolateBlock, capture]
  cases parser (input.enterWindow input.cursor captured.window) <;> simp

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.IsolatedBlockTraceSoundnessProperties
/-! Independent isolation traces from executable results, conditional on
explicit inner-parser trace soundness, including existence of every suffix. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

variable {parser : Parser Block}
  {blockParses : SourceId → Nat → DeclarativeGrammar.Remainder → Block →
    DeclarativeGrammar.Remainder → List ParseDiagnostic → Prop}
  {blockRejects : SourceId → Nat → DeclarativeGrammar.Remainder →
    DeclarativeGrammar.Remainder → ParseDiagnostic → List ParseDiagnostic → Prop}

/-- Every isolation success is a direct success, captured success, or recovered
ordinary rejection. The child starts with no prior diagnostic events. -/
theorem isolateBlock_success_trace_sound
    (successSound : BlockTraceSuccessSound parser blockParses)
    (rejectSound : BlockTraceRejectSound parser blockRejects)
    {input output : State} {body : Block}
    (result : isolateBlock parser input = .ok body output) :
    ∃ trace, DeclarativeGrammar.IsolatedBlockTraceParses blockParses blockRejects
      input.file.id input.window.endByte input.declarativeRemainder body
      output.declarativeRemainder trace ∧ output.diagnostics = input.diagnostics ++ trace := by
  cases capturedResult : BlockInternals.captureBlock? input with
  | none =>
      rw [isolateBlock_eq_of_no_capture parser capturedResult] at result
      rcases successSound result with ⟨trace, bodyParsed, traceEq⟩
      exact ⟨trace, .direct (BlockInternals.captureBlock?_none_absent capturedResult)
        bodyParsed, traceEq⟩
  | some captured =>
      rcases BlockInternals.captureBlock?_success_sound capturedResult with
        ⟨capture, captureParsed, spanEq, endIndexEq, endByteEq⟩
      rcases (isolateBlock_captured_success_iff capturedResult).mp result with
        ⟨childAfter, childResult, rfl⟩ | ⟨failure, childAfter, childResult, rfl, rfl⟩
      · rcases successSound childResult with ⟨trace, bodyParsed, traceEq⟩
        have childParsed : blockParses input.file.id capture.endByte
            (capture.childRemainder input.declarativeRemainder) body
            childAfter.declarativeRemainder trace := by
          simpa only [State.enterWindow, State.declarativeRemainder,
            DeclarativeGrammar.BalancedBlockCapture.childRemainder,
            endIndexEq, endByteEq] using bodyParsed
        refine ⟨trace, ?_, ?_⟩
        · simpa only [State.mergeDiagnostics, State.declarativeRemainder,
            DeclarativeGrammar.BalancedBlockCapture.parentRemainder, endIndexEq]
            using DeclarativeGrammar.IsolatedBlockTraceParses.captured captureParsed childParsed
        · rw [(isolateBlock_captured_success_trace capturedResult childResult).2, traceEq]
          simp only [State.enterWindow_diagnostics_eq_nil, List.nil_append]
      · rcases rejectSound childResult with ⟨trace, bodyRejected, traceEq⟩
        have childRejected : blockRejects input.file.id capture.endByte
            (capture.childRemainder input.declarativeRemainder)
            childAfter.declarativeRemainder failure.toDiagnostic trace := by
          simpa only [State.enterWindow, State.declarativeRemainder,
            DeclarativeGrammar.BalancedBlockCapture.childRemainder,
            endIndexEq, endByteEq] using bodyRejected
        refine ⟨trace ++ [failure.toDiagnostic], ?_, ?_⟩
        · simpa only [State.mergeDiagnostics, State.emit, State.declarativeRemainder,
            DeclarativeGrammar.BalancedBlockCapture.parentRemainder, spanEq, endIndexEq]
            using DeclarativeGrammar.IsolatedBlockTraceParses.recovered captureParsed childRejected
        · rw [(isolateBlock_captured_reject_trace capturedResult childResult).2, traceEq]
          simp only [State.enterWindow_diagnostics_eq_nil, List.nil_append, List.append_assoc]

/-- Only the no-capture branch can reject. Its report remains uncommitted and
its original preceding trace is appended unchanged to the parent diagnostics. -/
theorem isolateBlock_reject_trace_sound
    (rejectSound : BlockTraceRejectSound parser blockRejects)
    {input rejected : State} {failure : Failure}
    (result : isolateBlock parser input = .reject failure rejected) :
    ∃ trace, DeclarativeGrammar.IsolatedBlockTraceRejects blockRejects
      input.file.id input.window.endByte input.declarativeRemainder
      rejected.declarativeRemainder failure.toDiagnostic trace ∧
      rejected.diagnostics = input.diagnostics ++ trace := by
  cases capturedResult : BlockInternals.captureBlock? input with
  | none =>
      rw [isolateBlock_eq_of_no_capture parser capturedResult] at result
      rcases rejectSound result with ⟨trace, bodyRejected, traceEq⟩
      exact ⟨trace, .direct (BlockInternals.captureBlock?_none_absent capturedResult)
        bodyRejected, traceEq⟩
  | some captured =>
      exact False.elim (isolateBlock_captured_ne_reject capturedResult result)

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.IsolatedBlockTraceCompletenessProperties
/-! Independent isolation traces execute under explicit inner trace contracts.
The final correspondences retain source context, AST/report, remainder, and the
complete appended trace, without claiming concrete Core trace completeness. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

variable {parser : Parser Block}
  {blockParses : SourceId → Nat → DeclarativeGrammar.Remainder → Block →
    DeclarativeGrammar.Remainder → List ParseDiagnostic → Prop}
  {blockRejects : SourceId → Nat → DeclarativeGrammar.Remainder →
    DeclarativeGrammar.Remainder → ParseDiagnostic → List ParseDiagnostic → Prop}

private theorem captureBlock?_eq_none_of_absent {input : State}
    (absent : DeclarativeGrammar.BalancedBlockCaptureAbsentAt input.declarativeRemainder) :
    BlockInternals.captureBlock? input = none := by
  cases found : BlockInternals.captureBlock? input with
  | none => rfl
  | some captured =>
      rcases BlockInternals.captureBlock?_success_sound found with
        ⟨capture, captured, _, _, _⟩
      exact False.elim (absent ⟨capture, captured⟩)

/-- Every independent isolated success executes. Captured rejection restores
the parent remainder and emits its uncommitted report after the child trace. -/
theorem isolateBlock_success_trace_complete
    (successComplete : BlockTraceSuccessComplete parser blockParses)
    (rejectComplete : BlockTraceRejectComplete parser blockRejects)
    {input : State} {body : Block} {after : DeclarativeGrammar.Remainder}
    {trace : List ParseDiagnostic}
    (parsed : DeclarativeGrammar.IsolatedBlockTraceParses blockParses blockRejects
      input.file.id input.window.endByte input.declarativeRemainder body after trace) :
    ∃ output, isolateBlock parser input = .ok body output ∧
      output.declarativeRemainder = after ∧ output.diagnostics = input.diagnostics ++ trace := by
  cases parsed with
  | direct absent bodyParsed =>
      rw [isolateBlock_eq_of_no_capture parser (captureBlock?_eq_none_of_absent absent)]
      exact successComplete bodyParsed
  | captured captureParsed bodyParsed =>
      rename_i childOutput capture
      rcases BlockInternals.captureBlock?_complete captureParsed with
        ⟨captured, capturedResult, _spanEq, endIndexEq, endByteEq⟩
      have childParsed : blockParses
          (input.enterWindow input.cursor captured.window).file.id
          (input.enterWindow input.cursor captured.window).window.endByte
          (input.enterWindow input.cursor captured.window).declarativeRemainder
          body childOutput trace := by
        simpa only [State.enterWindow, State.declarativeRemainder,
          DeclarativeGrammar.BalancedBlockCapture.childRemainder, endIndexEq, endByteEq]
          using bodyParsed
      rcases successComplete childParsed with ⟨childAfter, childResult, _, traceEq⟩
      refine ⟨_, (isolateBlock_captured_success_trace capturedResult childResult).1, ?_, ?_⟩
      · simp only [State.mergeDiagnostics, State.declarativeRemainder,
          DeclarativeGrammar.BalancedBlockCapture.parentRemainder, endIndexEq]
      · rw [(isolateBlock_captured_success_trace capturedResult childResult).2, traceEq]
        simp only [State.enterWindow_diagnostics_eq_nil, List.nil_append]
  | recovered captureParsed bodyRejected =>
      rename_i childRejected capture diagnostic childTrace
      rcases BlockInternals.captureBlock?_complete captureParsed with
        ⟨captured, capturedResult, spanEq, endIndexEq, endByteEq⟩
      have childTraceRejected : blockRejects
          (input.enterWindow input.cursor captured.window).file.id
          (input.enterWindow input.cursor captured.window).window.endByte
          (input.enterWindow input.cursor captured.window).declarativeRemainder
          childRejected diagnostic childTrace := by
        simpa only [State.enterWindow, State.declarativeRemainder,
          DeclarativeGrammar.BalancedBlockCapture.childRemainder, endIndexEq, endByteEq]
          using bodyRejected
      rcases rejectComplete childTraceRejected with
        ⟨failure, childAfter, childResult, _, reportEq, traceEq⟩
      refine ⟨((({ input with cursor := captured.window.endIndex } : State).mergeDiagnostics
        childAfter).emit failure.toDiagnostic), ?_, ?_, ?_⟩
      · simpa only [spanEq] using
          (isolateBlock_captured_reject_trace capturedResult childResult).1
      · simp only [State.mergeDiagnostics, State.emit, State.declarativeRemainder,
          DeclarativeGrammar.BalancedBlockCapture.parentRemainder, endIndexEq]
      · rw [(isolateBlock_captured_reject_trace capturedResult childResult).2, traceEq, reportEq]
        simp only [State.enterWindow_diagnostics_eq_nil, List.nil_append, List.append_assoc]

/-- Uncaptured independent rejection escapes unchanged, with the same report
and remainder and without prematurely committing the final diagnostic. -/
theorem isolateBlock_reject_trace_complete
    (rejectComplete : BlockTraceRejectComplete parser blockRejects)
    {input : State} {after : DeclarativeGrammar.Remainder}
    {diagnostic : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejected : DeclarativeGrammar.IsolatedBlockTraceRejects blockRejects
      input.file.id input.window.endByte input.declarativeRemainder after diagnostic trace) :
    ∃ failure output, isolateBlock parser input = .reject failure output ∧
      output.declarativeRemainder = after ∧ failure.toDiagnostic = diagnostic ∧
      output.diagnostics = input.diagnostics ++ trace := by
  cases rejected with
  | direct absent bodyRejected =>
      rw [isolateBlock_eq_of_no_capture parser (captureBlock?_eq_none_of_absent absent)]
      exact rejectComplete bodyRejected

/-- Exact success correspondence requires both directions of both inner
ordinary outcomes, since captured rejection is an outer success. Soundness
supplies a suffix for every result; append cancellation identifies that suffix. -/
theorem isolateBlock_trace_success_iff
    (successSound : BlockTraceSuccessSound parser blockParses)
    (rejectSound : BlockTraceRejectSound parser blockRejects)
    (successComplete : BlockTraceSuccessComplete parser blockParses)
    (rejectComplete : BlockTraceRejectComplete parser blockRejects)
    {input : State} {body : Block} {after : DeclarativeGrammar.Remainder}
    {trace : List ParseDiagnostic} :
    DeclarativeGrammar.IsolatedBlockTraceParses blockParses blockRejects
      input.file.id input.window.endByte input.declarativeRemainder body after trace ↔
      ∃ output, isolateBlock parser input = .ok body output ∧
        output.declarativeRemainder = after ∧ output.diagnostics = input.diagnostics ++ trace := by
  constructor
  · exact isolateBlock_success_trace_complete successComplete rejectComplete
  · rintro ⟨output, result, remainderEq, traceEq⟩
    rcases isolateBlock_success_trace_sound successSound rejectSound result with
      ⟨actual, parsed, actualEq⟩
    have same : actual = trace := List.append_cancel_left (actualEq.symm.trans traceEq)
    simpa only [remainderEq, same] using parsed

/-- Escaping rejection needs only the two inner rejection contracts. Failure
records are compared through their complete diagnostic, never by assumption. -/
theorem isolateBlock_trace_reject_iff
    (rejectSound : BlockTraceRejectSound parser blockRejects)
    (rejectComplete : BlockTraceRejectComplete parser blockRejects)
    {input : State} {after : DeclarativeGrammar.Remainder}
    {diagnostic : ParseDiagnostic} {trace : List ParseDiagnostic} :
    DeclarativeGrammar.IsolatedBlockTraceRejects blockRejects
      input.file.id input.window.endByte input.declarativeRemainder after diagnostic trace ↔
      ∃ failure output, isolateBlock parser input = .reject failure output ∧
        output.declarativeRemainder = after ∧ failure.toDiagnostic = diagnostic ∧
        output.diagnostics = input.diagnostics ++ trace := by
  constructor
  · exact isolateBlock_reject_trace_complete rejectComplete
  · rintro ⟨failure, output, result, remainderEq, reportEq, traceEq⟩
    rcases isolateBlock_reject_trace_sound rejectSound result with
      ⟨actual, rejected, actualEq⟩
    have same : actual = trace := List.append_cancel_left (actualEq.symm.trans traceEq)
    simpa only [remainderEq, reportEq, same] using rejected

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.CoreBlockIsolationTraceProperties
/-! Exact isolated Core block traces under explicit statement contracts.
Raw success performs delayed tail validation; raw rejection skips that pass.
The isolation wrapper then commits a recovered report after the raw child trace. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

variable {statement : Parser Statement}
  {statementTrace : SourceId → Nat → DeclarativeGrammar.Remainder → Statement →
    DeclarativeGrammar.Remainder → List ParseDiagnostic → Prop}
  {statementRejects : SourceId → Nat → DeclarativeGrammar.Remainder →
    DeclarativeGrammar.Remainder → ParseDiagnostic → List ParseDiagnostic → Prop}

/-- Statement soundness supplies an independent suffix for every isolated
success, including an empty recovered body after raw statement rejection. -/
theorem isolatedCoreBlock_success_trace_sound
    (successSound : StatementTraceSuccessSound statement statementTrace)
    (rejectSound : StatementTraceRejectSound statement statementRejects)
    (contextFrame : StatementSuccessContext statement) (policy : TailExpressionPolicy) :
    BlockTraceSuccessSound (isolateBlock (coreBlock statement policy))
      (DeclarativeGrammar.IsolatedBlockTraceParses
        (DeclarativeGrammar.CoreBlockTraceParses statementTrace policy.declarative)
        (DeclarativeGrammar.CoreBlockTraceRejects statementTrace statementRejects policy.declarative)) :=
  isolateBlock_success_trace_sound (coreBlock_success_trace_sound successSound contextFrame policy)
    (coreBlock_reject_trace_sound successSound rejectSound contextFrame policy)

/-- An escaping failure has no balanced capture and retains its uncommitted
report and preceding events, as supplied by the raw block rejection grammar. -/
theorem isolatedCoreBlock_reject_trace_sound
    (successSound : StatementTraceSuccessSound statement statementTrace)
    (rejectSound : StatementTraceRejectSound statement statementRejects)
    (contextFrame : StatementSuccessContext statement) (policy : TailExpressionPolicy) :
    BlockTraceRejectSound (isolateBlock (coreBlock statement policy))
      (DeclarativeGrammar.IsolatedBlockTraceRejects
        (DeclarativeGrammar.CoreBlockTraceRejects statementTrace statementRejects policy.declarative)) :=
  isolateBlock_reject_trace_sound
    (coreBlock_reject_trace_sound successSound rejectSound contextFrame policy)

/-- Every independently described isolated success executes with its exact
AST, parent remainder, and appended diagnostics under statement completeness. -/
theorem isolatedCoreBlock_success_trace_complete
    (successComplete : StatementTraceSuccessComplete statement statementTrace)
    (rejectComplete : StatementTraceRejectComplete statement statementRejects)
    (contextFrame : StatementSuccessContext statement) (policy : TailExpressionPolicy) :
    BlockTraceSuccessComplete (isolateBlock (coreBlock statement policy))
      (DeclarativeGrammar.IsolatedBlockTraceParses
        (DeclarativeGrammar.CoreBlockTraceParses statementTrace policy.declarative)
        (DeclarativeGrammar.CoreBlockTraceRejects statementTrace statementRejects policy.declarative)) :=
  isolateBlock_success_trace_complete
    (coreBlock_trace_success_complete successComplete contextFrame policy)
    (coreBlock_trace_reject_complete successComplete rejectComplete contextFrame policy)

/-- Independent uncaptured raw rejection executes without recovery or tail
validation, preserving the exact report and prior diagnostic suffix. -/
theorem isolatedCoreBlock_reject_trace_complete
    (successComplete : StatementTraceSuccessComplete statement statementTrace)
    (rejectComplete : StatementTraceRejectComplete statement statementRejects)
    (contextFrame : StatementSuccessContext statement) (policy : TailExpressionPolicy) :
    BlockTraceRejectComplete (isolateBlock (coreBlock statement policy))
      (DeclarativeGrammar.IsolatedBlockTraceRejects
        (DeclarativeGrammar.CoreBlockTraceRejects statementTrace statementRejects policy.declarative)) :=
  isolateBlock_reject_trace_complete
    (coreBlock_trace_reject_complete successComplete rejectComplete contextFrame policy)

/-- Complete isolated success correspondence is obtained directly from
statement contracts; no raw block parser outcome is assumed by the caller. -/
theorem isolatedCoreBlock_trace_success_iff
    (successSound : StatementTraceSuccessSound statement statementTrace)
    (rejectSound : StatementTraceRejectSound statement statementRejects)
    (successComplete : StatementTraceSuccessComplete statement statementTrace)
    (rejectComplete : StatementTraceRejectComplete statement statementRejects)
    (contextFrame : StatementSuccessContext statement) (policy : TailExpressionPolicy)
    {input : State} {body : Block} {after : DeclarativeGrammar.Remainder}
    {trace : List ParseDiagnostic} :
    DeclarativeGrammar.IsolatedBlockTraceParses
      (DeclarativeGrammar.CoreBlockTraceParses statementTrace policy.declarative)
      (DeclarativeGrammar.CoreBlockTraceRejects statementTrace statementRejects policy.declarative)
      input.file.id input.window.endByte input.declarativeRemainder body after trace ↔
      ∃ output, isolateBlock (coreBlock statement policy) input = .ok body output ∧
        output.declarativeRemainder = after ∧ output.diagnostics = input.diagnostics ++ trace :=
  isolateBlock_trace_success_iff (coreBlock_success_trace_sound successSound contextFrame policy)
    (coreBlock_reject_trace_sound successSound rejectSound contextFrame policy)
    (coreBlock_trace_success_complete successComplete contextFrame policy)
    (coreBlock_trace_reject_complete successComplete rejectComplete contextFrame policy)

/-- Complete escaping rejection correspondence includes the full report and
every earlier event, with no final report committed by the isolation wrapper. -/
theorem isolatedCoreBlock_trace_reject_iff
    (successSound : StatementTraceSuccessSound statement statementTrace)
    (rejectSound : StatementTraceRejectSound statement statementRejects)
    (successComplete : StatementTraceSuccessComplete statement statementTrace)
    (rejectComplete : StatementTraceRejectComplete statement statementRejects)
    (contextFrame : StatementSuccessContext statement) (policy : TailExpressionPolicy)
    {input : State} {after : DeclarativeGrammar.Remainder}
    {diagnostic : ParseDiagnostic} {trace : List ParseDiagnostic} :
    DeclarativeGrammar.IsolatedBlockTraceRejects
      (DeclarativeGrammar.CoreBlockTraceRejects statementTrace statementRejects policy.declarative)
      input.file.id input.window.endByte input.declarativeRemainder after diagnostic trace ↔
      ∃ failure output, isolateBlock (coreBlock statement policy) input = .reject failure output ∧
        output.declarativeRemainder = after ∧ failure.toDiagnostic = diagnostic ∧
        output.diagnostics = input.diagnostics ++ trace :=
  isolateBlock_trace_reject_iff
    (coreBlock_reject_trace_sound successSound rejectSound contextFrame policy)
    (coreBlock_trace_reject_complete successComplete rejectComplete contextFrame policy)

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.PragmaItemsContextProperties
/-! Unconditional source-file and full-window frame laws for pragma items.
Cursor changes and emitted diagnostics do not alter diagnostic report context. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Successful checked names retain the complete file and window, including
the window end byte, whether or not a hyphen diagnostic was emitted. -/
theorem identifier_success_context_eq (context : ParseContext)
    {input output : State} {name : Identifier}
    (result : identifier context input = .ok name output) :
    output.file = input.file ∧ output.window = input.window := by
  unfold identifier at result
  cases raw : rawIdentifier context input with
  | reject failure rejected => simp [raw] at result
  | invariant error => simp [raw] at result
  | ok parsed afterName =>
      have shape := rawIdentifier_ok_state_shape context raw
      simp only [raw] at result
      split at result <;> cases result <;> rw [shape] <;> exact ⟨rfl, rfl⟩

/-- Rejected checked names retain the original file and full input window. -/
theorem identifier_reject_context_eq (context : ParseContext)
    {input rejected : State} {failure : Failure}
    (result : identifier context input = .reject failure rejected) :
    rejected.file = input.file ∧ rejected.window = input.window := by
  rw [identifier_reject_state_eq context result]
  exact ⟨rfl, rfl⟩

private def replyContextEq {alpha : Type} (input : State) : Reply alpha → Prop
  | .ok _ output | .reject _ output =>
      output.file = input.file ∧ output.window = input.window
  | .invariant _ => True

private theorem replyContextEq_trans {alpha : Type}
    {input middle : State} {reply : Reply alpha}
    (outer : replyContextEq middle reply)
    (inner : middle.file = input.file ∧ middle.window = input.window) :
    replyContextEq input reply := by
  cases reply with
  | ok _ _ | reject _ _ => exact ⟨outer.1.trans inner.1, outer.2.trans inner.2⟩
  | invariant => trivial

namespace PragmaInternals

private theorem pragmaItemsTail_context_frame :
    ∀ fuel itemsRev input, replyContextEq input (pragmaItemsTail fuel itemsRev input) := by
  intro fuel
  induction fuel with
  | zero => intro itemsRev input; trivial
  | succ fuel ih =>
      intro itemsRev input
      unfold pragmaItemsTail
      split
      · cases commaResult : symbol .comma .pragmaDecl input with
        | invariant => trivial
        | reject failure rejected =>
            have stateEq := acceptToken_reject_state_shape (.symbol .comma) .pragmaDecl
              (· == .symbol .comma) commaResult
            exact ⟨congrArg State.file stateEq, congrArg State.window stateEq⟩
        | ok comma afterComma =>
            have commaShape := (symbol_ok_state_shape .comma .pragmaDecl commaResult).2
            have commaContext : afterComma.file = input.file ∧
                afterComma.window = input.window := by
              rw [commaShape]
              exact ⟨rfl, rfl⟩
            simp only
            split
            · exact commaContext
            · cases itemResult : identifier .pragmaDecl afterComma with
              | invariant => trivial
              | reject failure rejected =>
                  have context := identifier_reject_context_eq .pragmaDecl itemResult
                  exact ⟨context.1.trans commaContext.1, context.2.trans commaContext.2⟩
              | ok item next =>
                  have context := identifier_success_context_eq .pragmaDecl itemResult
                  exact replyContextEq_trans (ih (item :: itemsRev) next)
                    ⟨context.1.trans commaContext.1, context.2.trans commaContext.2⟩
      · exact ⟨rfl, rfl⟩

private theorem pragmaItems_context_frame (input : State) :
    replyContextEq input (pragmaItems input) := by
  unfold pragmaItems
  split
  · exact ⟨rfl, rfl⟩
  · cases itemResult : identifier .pragmaDecl input with
    | invariant => trivial
    | reject failure rejected => exact identifier_reject_context_eq .pragmaDecl itemResult
    | ok item next =>
        exact replyContextEq_trans
          (pragmaItemsTail_context_frame (next.remainingCount + 1) [item] next)
          (identifier_success_context_eq .pragmaDecl itemResult)

/-- Successful tail scanning preserves the file and full window for every
fuel and reverse prefix, independently of input/diagnostic validity. -/
theorem pragmaItemsTail_success_context_eq (fuel : Nat) (itemsRev : List Identifier)
    {input output : State} {items : List Identifier}
    (result : pragmaItemsTail fuel itemsRev input = .ok items output) :
    output.file = input.file ∧ output.window = input.window := by
  have frame := pragmaItemsTail_context_frame fuel itemsRev input
  rw [result] at frame
  exact frame

/-- Ordinary tail rejection retains the original source and end-byte context,
even after successful earlier items have emitted diagnostics. -/
theorem pragmaItemsTail_reject_context_eq (fuel : Nat) (itemsRev : List Identifier)
    {input rejected : State} {failure : Failure}
    (result : pragmaItemsTail fuel itemsRev input = .reject failure rejected) :
    rejected.file = input.file ∧ rejected.window = input.window := by
  have frame := pragmaItemsTail_context_frame fuel itemsRev input
  rw [result] at frame
  exact frame

/-- Full successful item scanning retains both report-context carriers. -/
theorem pragmaItems_success_context_eq
    {input output : State} {items : List Identifier}
    (result : pragmaItems input = .ok items output) :
    output.file = input.file ∧ output.window = input.window := by
  have frame := pragmaItems_context_frame input
  rw [result] at frame
  exact frame

/-- Full item rejection retains the input file and complete active window. -/
theorem pragmaItems_reject_context_eq
    {input rejected : State} {failure : Failure}
    (result : pragmaItems input = .reject failure rejected) :
    rejected.file = input.file ∧ rejected.window = input.window := by
  have frame := pragmaItems_context_frame input
  rw [result] at frame
  exact frame

end PragmaInternals
end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.TerminatedControlSuccessTraceProperties
/-! Exact silent success for the real keyword-plus-semicolon statement parser. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ControlInternals

/-- A successful leaf changes only the cursor, advancing exactly two tokens. -/
theorem terminatedControl_success_state_shape
    (keywordValue : HardKeyword) (statementValue : StatementValue)
    {input output : State} {statement : Statement}
    (result : terminatedControl keywordValue statementValue input = .ok statement output) :
    output = { input with cursor := input.cursor + 2 } := by
  unfold terminatedControl at result
  cases markerResult : keyword keywordValue .statement input with
  | invariant error => simp [bind, markerResult] at result
  | reject failure rejected => simp [bind, markerResult] at result
  | ok marker afterMarker =>
      cases semicolonResult : symbol .semicolon .statement afterMarker with
      | invariant error => simp [bind, markerResult, semicolonResult] at result
      | reject failure rejected => simp [bind, markerResult, semicolonResult] at result
      | ok semicolon next =>
          simp only [bind, markerResult, semicolonResult, pure] at result
          cases result
          rw [(symbol_ok_tokenAt .semicolon .statement semicolonResult).2,
            (keyword_ok_tokenAt keywordValue .statement markerResult).2]

/-- Exact tokens determine the complete AST and cursor update, without source
validity, empty prior diagnostics, or any child-parser assumption. -/
theorem terminatedControl_eq_ok_of_ordinary
    (keywordValue : HardKeyword) (statementValue : StatementValue)
    {input : State} {statement : Statement} {after : DeclarativeGrammar.Remainder}
    (parsed : DeclarativeGrammar.TerminatedControlStatementOrdinaryParses
      keywordValue statementValue input.declarativeRemainder statement after) :
    terminatedControl keywordValue statementValue input = .ok statement
      { input with cursor := input.cursor + 2 } := by
  cases parsed with
  | parsed marker semicolon markerParsed semicolonParsed =>
      have markerResult := keyword_eq_ok_of_exactTokenParses keywordValue .statement markerParsed
      rcases markerParsed with ⟨_, rfl⟩
      have semicolonResult := symbol_eq_ok_of_exactTokenParses .semicolon .statement
        (input := { input with cursor := input.cursor + 1 }) semicolonParsed
      simp only [terminatedControl, bind, markerResult, semicolonResult, pure]

theorem terminatedControl_trace_success_sound
    (keywordValue : HardKeyword) (statementValue : StatementValue) :
    StatementTraceSuccessSound (terminatedControl keywordValue statementValue)
      (DeclarativeGrammar.TerminatedControlStatementTraceParses keywordValue statementValue) := by
  intro input output statement result
  refine ⟨[], ⟨terminatedControl_success_sound keywordValue statementValue result, rfl⟩, ?_⟩
  rw [terminatedControl_success_state_shape keywordValue statementValue result]
  simp only [List.append_nil, State.diagnostics]

theorem terminatedControl_trace_success_complete
    (keywordValue : HardKeyword) (statementValue : StatementValue) :
    StatementTraceSuccessComplete (terminatedControl keywordValue statementValue)
      (DeclarativeGrammar.TerminatedControlStatementTraceParses keywordValue statementValue) := by
  intro input statement after trace parsed
  rcases parsed with ⟨parsed, rfl⟩
  have result := terminatedControl_eq_ok_of_ordinary keywordValue statementValue parsed
  refine ⟨_, result, ?_, by simp only [List.append_nil, State.diagnostics]⟩
  cases parsed with
  | parsed marker semicolon markerParsed semicolonParsed =>
      rcases markerParsed with ⟨_, rfl⟩
      exact semicolonParsed.2.symm

theorem terminatedControl_success_context
    (keywordValue : HardKeyword) (statementValue : StatementValue) :
    StatementSuccessContext (terminatedControl keywordValue statementValue) := by
  intro input output statement result
  rw [terminatedControl_success_state_shape keywordValue statementValue result]
  exact ⟨rfl, rfl⟩

/-- The complete independent success trace is equivalent to actual execution. -/
theorem terminatedControl_trace_success_iff
    (keywordValue : HardKeyword) (statementValue : StatementValue)
    {input : State} {statement : Statement} {after : DeclarativeGrammar.Remainder}
    {trace : List ParseDiagnostic} :
    DeclarativeGrammar.TerminatedControlStatementTraceParses keywordValue statementValue
      input.file.id input.window.endByte input.declarativeRemainder statement after trace ↔
    ∃ output, terminatedControl keywordValue statementValue input = .ok statement output ∧
      output.declarativeRemainder = after ∧ output.diagnostics = input.diagnostics ++ trace := by
  constructor
  · exact terminatedControl_trace_success_complete keywordValue statementValue
  · rintro ⟨output, result, afterEq, diagnostics⟩
    rcases terminatedControl_trace_success_sound keywordValue statementValue result with
      ⟨actualTrace, parsed, actualEq⟩
    have events : actualTrace = trace := List.append_cancel_left (actualEq.symm.trans diagnostics)
    simpa only [afterEq, events] using parsed

end Solcore.Syntax.Parser.ControlInternals
end

section
-- leanmerge: from Solcore.Syntax.Parser.TerminatedControlRejectionTraceProperties
/-! Exact first-failure reports for real terminated control statements.
Neither successful token consumption nor rejection commits a diagnostic. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ControlInternals

/-- Every rejection keeps earlier events and reports precisely the first
missing required token, at the exact current-token or window-end location. -/
theorem terminatedControl_reject_reports
    (keywordValue : HardKeyword) (statementValue : StatementValue)
    {input rejected : State} {failure : Failure}
    (result : terminatedControl keywordValue statementValue input = .reject failure rejected) :
    DeclarativeGrammar.TerminatedControlStatementTraceRejects keywordValue
      input.file.id input.window.endByte input.declarativeRemainder
      rejected.declarativeRemainder failure.toDiagnostic [] ∧
      rejected.diagnostics = input.diagnostics := by
  unfold terminatedControl at result
  cases markerResult : keyword keywordValue .statement input with
  | invariant error => simp [bind, markerResult] at result
  | reject markerFailure markerRejected =>
      have shape := acceptToken_reject_state_shape (.keyword keywordValue) .statement
        (· == .keyword keywordValue) markerResult
      subst markerRejected
      simp only [bind, markerResult] at result
      cases result
      have reported := (keyword_reject_reports_iff keywordValue .statement).mpr
        ⟨failure, markerResult, rfl⟩
      exact ⟨.markerMissing reported.1 reported.2, rfl⟩
  | ok marker afterMarker =>
      have markerParsed := keyword_success_exactTokenParses keywordValue .statement markerResult
      have markerShape := (keyword_ok_tokenAt keywordValue .statement markerResult).2
      subst afterMarker
      cases semicolonResult : symbol .semicolon .statement
          { input with cursor := input.cursor + 1 } with
      | invariant error => simp [bind, markerResult, semicolonResult] at result
      | ok semicolon next => simp [bind, markerResult, semicolonResult, pure] at result
      | reject semicolonFailure semicolonRejected =>
          have shape := acceptToken_reject_state_shape (.symbol .semicolon) .statement
            (· == .symbol .semicolon) semicolonResult
          subst semicolonRejected
          simp only [bind, markerResult, semicolonResult] at result
          cases result
          have reported := (symbol_reject_reports_iff .semicolon .statement).mpr
            ⟨failure, semicolonResult, rfl⟩
          exact ⟨.semicolonMissing marker.span markerParsed reported.1 reported.2, rfl⟩

theorem terminatedControl_trace_reject_sound
    (keywordValue : HardKeyword) (statementValue : StatementValue) :
    StatementTraceRejectSound (terminatedControl keywordValue statementValue)
      (DeclarativeGrammar.TerminatedControlStatementTraceRejects keywordValue) := by
  intro input rejected failure result
  have reported := terminatedControl_reject_reports keywordValue statementValue result
  exact ⟨[], reported.1, by simpa only [List.append_nil] using reported.2⟩

/-- Each independently specified first failure executes with the same report
and retained remainder, for arbitrary incoming state and diagnostic metadata. -/
theorem terminatedControl_trace_reject_complete
    (keywordValue : HardKeyword) (statementValue : StatementValue) :
    StatementTraceRejectComplete (terminatedControl keywordValue statementValue)
      (DeclarativeGrammar.TerminatedControlStatementTraceRejects keywordValue) := by
  intro input after diagnostic trace traced
  cases traced with
  | markerMissing absent reported =>
      rcases (keyword_reject_reports_iff keywordValue .statement).mp ⟨absent, reported⟩ with
        ⟨failure, result, reportEq⟩
      exact ⟨failure, input, by simp only [terminatedControl, bind, result], rfl,
        reportEq, by simp only [List.append_nil]⟩
  | semicolonMissing marker markerParsed absent reported =>
      have markerResult := keyword_eq_ok_of_exactTokenParses keywordValue .statement markerParsed
      rcases markerParsed with ⟨_, rfl⟩
      rcases (symbol_reject_reports_iff .semicolon .statement
          (input := { input with cursor := input.cursor + 1 })).mp ⟨absent, reported⟩ with
        ⟨failure, result, reportEq⟩
      exact ⟨failure, { input with cursor := input.cursor + 1 },
        by simp only [terminatedControl, bind, markerResult, result], rfl,
        reportEq, by simp only [List.append_nil, State.diagnostics]⟩

theorem terminatedControl_trace_reject_iff
    (keywordValue : HardKeyword) (statementValue : StatementValue)
    {input : State} {after : DeclarativeGrammar.Remainder}
    {diagnostic : ParseDiagnostic} {trace : List ParseDiagnostic} :
    DeclarativeGrammar.TerminatedControlStatementTraceRejects keywordValue
      input.file.id input.window.endByte input.declarativeRemainder after diagnostic trace ↔
    ∃ failure rejected, terminatedControl keywordValue statementValue input = .reject failure rejected ∧
      rejected.declarativeRemainder = after ∧ failure.toDiagnostic = diagnostic ∧
      rejected.diagnostics = input.diagnostics ++ trace := by
  constructor
  · exact terminatedControl_trace_reject_complete keywordValue statementValue
  · rintro ⟨failure, rejected, result, afterEq, reportEq, diagnostics⟩
    rcases terminatedControl_trace_reject_sound keywordValue statementValue result with
      ⟨actualTrace, traced, actualEq⟩
    have events : actualTrace = trace := List.append_cancel_left (actualEq.symm.trans diagnostics)
    simpa only [afterEq, reportEq, events] using traced

/-- Every failure field, rather than only the rendered diagnostic, is fixed by
the independent report. The failure itself remains outside the retained trace. -/
theorem terminatedControl_trace_reject_failure_iff
    (keywordValue : HardKeyword) (statementValue : StatementValue)
    {input : State} {after : DeclarativeGrammar.Remainder}
    {failure : Failure} {trace : List ParseDiagnostic} :
    DeclarativeGrammar.TerminatedControlStatementTraceRejects keywordValue
      input.file.id input.window.endByte input.declarativeRemainder after failure.toDiagnostic trace ↔
    ∃ rejected, terminatedControl keywordValue statementValue input = .reject failure rejected ∧
      rejected.declarativeRemainder = after ∧ rejected.diagnostics = input.diagnostics ++ trace := by
  constructor
  · intro traced
    rcases (terminatedControl_trace_reject_iff keywordValue statementValue).mp traced with
      ⟨actual, rejected, result, afterEq, reportEq, diagnostics⟩
    have same := Failure.toDiagnostic_injective reportEq
    subst actual
    exact ⟨rejected, result, afterEq, diagnostics⟩
  · rintro ⟨rejected, result, afterEq, diagnostics⟩
    exact (terminatedControl_trace_reject_iff keywordValue statementValue).mpr
      ⟨failure, rejected, result, afterEq, rfl, diagnostics⟩

end Solcore.Syntax.Parser.ControlInternals
end
