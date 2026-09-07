import Solcore.Syntax.DeclarativeBlockStatementTraceProperties
import Solcore.Syntax.Parser.CoreBlockContextProperties
import Solcore.Syntax.Parser.CoreBlockTraceCompletenessProperties
import Solcore.Syntax.Parser.CoreBlockRejectionTraceCompletenessProperties
import Solcore.Syntax.Parser.Statement.Control

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
