import Solcore.Syntax.Parser.CoreBlockTraceCompletenessProperties
import Solcore.Syntax.Parser.CoreBlockRejectionTraceCompletenessProperties
import Solcore.Syntax.Parser.IsolatedBlockTraceCompletenessProperties

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
