import Solcore.Syntax.Parser.CoreBlockIsolationTraceProperties

/-! Isolated Core consumers expose only statement contracts and independent
block syntax. Captured recovery skips raw tail validation and commits once. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserCoreBlockIsolationTraceProperties

open Solcore.Syntax
open Solcore.Syntax.Parser
open Solcore.Syntax.DeclarativeGrammar

example := @isolatedCoreBlock_success_trace_sound
example := @isolatedCoreBlock_reject_trace_sound
example := @isolatedCoreBlock_success_trace_complete
example := @isolatedCoreBlock_reject_trace_complete
example := @isolatedCoreBlock_trace_success_iff
example := @isolatedCoreBlock_trace_reject_iff

variable {statement : Parser Statement}
  {statementTrace : SourceId → Nat → Remainder → Statement → Remainder →
    List ParseDiagnostic → Prop}
  {statementRejects : SourceId → Nat → Remainder → Remainder →
    ParseDiagnostic → List ParseDiagnostic → Prop}
  (successComplete : StatementTraceSuccessComplete statement statementTrace)
  (rejectComplete : StatementTraceRejectComplete statement statementRejects)
  (contextFrame : StatementSuccessContext statement) (policy : TailExpressionPolicy)

include successComplete rejectComplete contextFrame in
/-- A captured raw rejection restores the parent endpoint and retains all
earlier events before one committed report, under either raw tail policy. -/
theorem captured_raw_rejection_has_exact_trace
    {input : State} {capture : BalancedBlockCapture} {childRejected : Remainder}
    {report : ParseDiagnostic} {events : List ParseDiagnostic}
    (captured : BalancedBlockCaptures input.declarativeRemainder capture)
    (rejected : CoreBlockTraceRejects statementTrace statementRejects policy.declarative
      input.file.id capture.endByte (capture.childRemainder input.declarativeRemainder)
      childRejected report events) :
    ∃ output, isolateBlock (coreBlock statement policy) input =
        .ok { span := capture.span, value := [] } output ∧
      output.declarativeRemainder = capture.parentRemainder input.declarativeRemainder ∧
      output.diagnostics = input.diagnostics ++ (events ++ [report]) :=
  isolatedCoreBlock_success_trace_complete successComplete rejectComplete contextFrame policy
    (.recovered captured rejected)

include successComplete rejectComplete contextFrame in
/-- A successful captured block preserves its independently described total
trace, including validation reports already appended by raw block closing. -/
theorem captured_raw_success_retains_complete_trace
    {input : State} {capture : BalancedBlockCapture} {childAfter : Remainder}
    {body : Block} {events : List ParseDiagnostic}
    (captured : BalancedBlockCaptures input.declarativeRemainder capture)
    (parsed : CoreBlockTraceParses statementTrace policy.declarative input.file.id
      capture.endByte (capture.childRemainder input.declarativeRemainder) body childAfter events) :
    ∃ output, isolateBlock (coreBlock statement policy) input = .ok body output ∧
      output.declarativeRemainder = capture.parentRemainder input.declarativeRemainder ∧
      output.diagnostics = input.diagnostics ++ events :=
  isolatedCoreBlock_success_trace_complete successComplete rejectComplete contextFrame policy
    (.captured captured parsed)

include successComplete rejectComplete contextFrame in
/-- Without a capture, raw rejection escapes with the report still separate
from its trace. No recovered report is introduced at this boundary. -/
theorem uncaptured_raw_rejection_keeps_report_separate
    {input : State} {after : Remainder} {report : ParseDiagnostic}
    {events : List ParseDiagnostic}
    (absent : BalancedBlockCaptureAbsentAt input.declarativeRemainder)
    (rejected : CoreBlockTraceRejects statementTrace statementRejects policy.declarative
      input.file.id input.window.endByte input.declarativeRemainder after report events) :
    ∃ failure output, isolateBlock (coreBlock statement policy) input = .reject failure output ∧
      output.declarativeRemainder = after ∧ failure.toDiagnostic = report ∧
      output.diagnostics = input.diagnostics ++ events :=
  isolatedCoreBlock_reject_trace_complete successComplete rejectComplete contextFrame policy
    (.direct absent rejected)

end Solcore.Test.SyntaxParserCoreBlockIsolationTraceProperties
