import Solcore.Syntax.DeclarativeTupleTypeRejectionTraceGrammar
import Solcore.Syntax.Parser.DelimitedTrailingRejectionTraceCorrespondenceProperties
import Solcore.Syntax.Parser.Type

/-! Raw tuple failure is the exact failure of its trailing-enabled list. Mapping
the successful AST never commits a report or changes the rejected state. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

variable {nested : Parser TypeExpr}
  {typeTrace : SourceId → Nat → DeclarativeGrammar.Remainder → TypeExpr →
    DeclarativeGrammar.Remainder → List ParseDiagnostic → Prop}
  {typeRejects : SourceId → Nat → DeclarativeGrammar.Remainder →
    DeclarativeGrammar.Remainder → ParseDiagnostic → List ParseDiagnostic → Prop}

theorem parseTupleType_reject_iff_list {input rejected : State} {failure : Failure} :
    parseTupleType nested input = .reject failure rejected ↔
    delimited .leftParen .rightParen true nested .typeExpr .typeExpr input =
      .reject failure rejected := by
  cases result : delimited .leftParen .rightParen true nested .typeExpr .typeExpr input <;>
    simp [parseTupleType, bind, pure, result]

theorem parseTupleType_reject_trace_sound
    (successSound : ParserTraceSuccessSound nested typeTrace)
    (rejectSound : ParserTraceRejectSound nested typeRejects)
    (contextFrame : ParserSuccessContext nested) :
    ParserTraceRejectSound (parseTupleType nested)
      (DeclarativeGrammar.TupleTypeTraceRejects typeTrace typeRejects) := by
  intro input rejected failure result
  exact delimited_reject_trace_sound successSound rejectSound contextFrame
    .leftParen .rightParen true .typeExpr .typeExpr (parseTupleType_reject_iff_list.mp result)

theorem parseTupleType_trace_reject_complete
    (successComplete : ParserTraceSuccessComplete nested typeTrace)
    (rejectComplete : ParserTraceRejectComplete nested typeRejects)
    (contextFrame : ParserSuccessContext nested) :
    ParserTraceRejectComplete (parseTupleType nested)
      (DeclarativeGrammar.TupleTypeTraceRejects typeTrace typeRejects) := by
  intro input after report trace rejection
  rcases delimited_trace_reject_complete successComplete rejectComplete contextFrame
      .leftParen .rightParen true .typeExpr .typeExpr rejection with
    ⟨failure, rejected, result, afterEq, reportEq, events⟩
  exact ⟨failure, rejected, parseTupleType_reject_iff_list.mpr result, afterEq, reportEq, events⟩

theorem parseTupleType_trace_reject_iff
    (successSound : ParserTraceSuccessSound nested typeTrace)
    (rejectSound : ParserTraceRejectSound nested typeRejects)
    (successComplete : ParserTraceSuccessComplete nested typeTrace)
    (rejectComplete : ParserTraceRejectComplete nested typeRejects)
    (contextFrame : ParserSuccessContext nested)
    {input : State} {after : DeclarativeGrammar.Remainder}
    {report : ParseDiagnostic} {trace : List ParseDiagnostic} :
    DeclarativeGrammar.TupleTypeTraceRejects typeTrace typeRejects input.file.id input.window.endByte
      input.declarativeRemainder after report trace ↔
    ∃ failure rejected, parseTupleType nested input = .reject failure rejected ∧
      rejected.declarativeRemainder = after ∧ failure.toDiagnostic = report ∧
      rejected.diagnostics = input.diagnostics ++ trace := by
  simpa only [parseTupleType_reject_iff_list] using
    delimited_trace_reject_iff successSound rejectSound successComplete rejectComplete contextFrame
      .leftParen .rightParen true .typeExpr .typeExpr

theorem parseTupleType_trace_reject_failure_iff
    (successSound : ParserTraceSuccessSound nested typeTrace)
    (rejectSound : ParserTraceRejectSound nested typeRejects)
    (successComplete : ParserTraceSuccessComplete nested typeTrace)
    (rejectComplete : ParserTraceRejectComplete nested typeRejects)
    (contextFrame : ParserSuccessContext nested)
    {input : State} {after : DeclarativeGrammar.Remainder}
    {failure : Failure} {trace : List ParseDiagnostic} :
    DeclarativeGrammar.TupleTypeTraceRejects typeTrace typeRejects input.file.id input.window.endByte
      input.declarativeRemainder after failure.toDiagnostic trace ↔
    ∃ rejected, parseTupleType nested input = .reject failure rejected ∧
      rejected.declarativeRemainder = after ∧ rejected.diagnostics = input.diagnostics ++ trace := by
  simpa only [parseTupleType_reject_iff_list] using
    delimited_trace_reject_failure_iff successSound rejectSound successComplete rejectComplete contextFrame
      .leftParen .rightParen true .typeExpr .typeExpr

end Solcore.Syntax.Parser
