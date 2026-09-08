import Solcore.Syntax.DeclarativeExpressionAtomLayerTraceProperties
import Solcore.Syntax.Parser.ExpressionAtomDispatchTraceCorrespondenceProperties
import Solcore.Syntax.Parser.ExpressionAtomDispatchRejectionContextProperties
import Solcore.Syntax.Parser.ExpressionAtomTraceStateProperties

/-! Public atom traces instantiate the actual selected core and recovery.
Only recursive expression/body contracts remain supplied. Rejected child
frames preserve file/endByte, not the token carrier or numeric endIndex. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

open DeclarativeGrammar ExpressionAtomInternals

variable {nested : Parser Expr} {block : Parser Block}
  {nestedTrace : SourceId → Nat → Remainder → Expr → Remainder → List ParseDiagnostic → Prop}
  {nestedRejects : SourceId → Nat → Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop}
  {blockTrace : SourceId → Nat → Remainder → Block → Remainder → List ParseDiagnostic → Prop}
  {blockRejects : SourceId → Nat → Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop}

theorem expressionAtom_layer_trace_success_sound
    (successSound : ParserTraceSuccessSound nested nestedTrace)
    (rejectSound : ParserTraceRejectSound nested nestedRejects)
    (contextFrame : ParserSuccessContext nested)
    (blockSuccessSound : ParserTraceSuccessSound block blockTrace)
    (blockRejectSound : ParserTraceRejectSound block blockRejects)
    (nestedRejectFrame : ∀ {input rejected failure}, nested input = .reject failure rejected →
      rejected.file = input.file ∧ rejected.window.endByte = input.window.endByte)
    (blockRejectFrame : ∀ {input rejected failure}, block input = .reject failure rejected →
      rejected.file = input.file ∧ rejected.window.endByte = input.window.endByte) :
    ParserTraceSuccessSound (expressionAtom nested block)
      (ExpressionAtomLayerTraceParses nestedTrace nestedRejects blockTrace blockRejects) :=
  expressionAtom_trace_success_sound
    (expressionAtomCore_trace_success_sound successSound contextFrame blockSuccessSound)
    (expressionAtomCore_reject_trace_sound successSound rejectSound contextFrame blockRejectSound)
    (expressionAtomCore_reject_source_endByte contextFrame nestedRejectFrame blockRejectFrame)

theorem expressionAtom_layer_reject_trace_sound
    (successSound : ParserTraceSuccessSound nested nestedTrace)
    (rejectSound : ParserTraceRejectSound nested nestedRejects)
    (contextFrame : ParserSuccessContext nested)
    (blockRejectSound : ParserTraceRejectSound block blockRejects)
    (nestedRejectFrame : ∀ {input rejected failure}, nested input = .reject failure rejected →
      rejected.file = input.file ∧ rejected.window.endByte = input.window.endByte)
    (blockRejectFrame : ∀ {input rejected failure}, block input = .reject failure rejected →
      rejected.file = input.file ∧ rejected.window.endByte = input.window.endByte) :
    ParserTraceRejectSound (expressionAtom nested block)
      (ExpressionAtomLayerTraceRejects nestedTrace nestedRejects blockRejects) :=
  expressionAtom_reject_trace_sound
    (expressionAtomCore_reject_trace_sound successSound rejectSound contextFrame blockRejectSound)
    (expressionAtomCore_reject_source_endByte contextFrame nestedRejectFrame blockRejectFrame)

theorem expressionAtom_layer_trace_success_complete
    (successComplete : ParserTraceSuccessComplete nested nestedTrace)
    (rejectComplete : ParserTraceRejectComplete nested nestedRejects)
    (contextFrame : ParserSuccessContext nested)
    (blockSuccessComplete : ParserTraceSuccessComplete block blockTrace)
    (blockRejectComplete : ParserTraceRejectComplete block blockRejects)
    (nestedRejectFrame : ∀ {input rejected failure}, nested input = .reject failure rejected →
      rejected.file = input.file ∧ rejected.window.endByte = input.window.endByte)
    (blockRejectFrame : ∀ {input rejected failure}, block input = .reject failure rejected →
      rejected.file = input.file ∧ rejected.window.endByte = input.window.endByte) :
    ParserTraceSuccessComplete (expressionAtom nested block)
      (ExpressionAtomLayerTraceParses nestedTrace nestedRejects blockTrace blockRejects) :=
  expressionAtom_trace_success_complete
    (expressionAtomCore_trace_success_complete successComplete contextFrame blockSuccessComplete)
    (expressionAtomCore_trace_reject_complete successComplete rejectComplete contextFrame blockRejectComplete)
    (expressionAtomCore_reject_source_endByte contextFrame nestedRejectFrame blockRejectFrame)

theorem expressionAtom_layer_trace_reject_complete
    (successComplete : ParserTraceSuccessComplete nested nestedTrace)
    (rejectComplete : ParserTraceRejectComplete nested nestedRejects)
    (contextFrame : ParserSuccessContext nested)
    (blockRejectComplete : ParserTraceRejectComplete block blockRejects)
    (nestedRejectFrame : ∀ {input rejected failure}, nested input = .reject failure rejected →
      rejected.file = input.file ∧ rejected.window.endByte = input.window.endByte)
    (blockRejectFrame : ∀ {input rejected failure}, block input = .reject failure rejected →
      rejected.file = input.file ∧ rejected.window.endByte = input.window.endByte) :
    ParserTraceRejectComplete (expressionAtom nested block)
      (ExpressionAtomLayerTraceRejects nestedTrace nestedRejects blockRejects) :=
  expressionAtom_trace_reject_complete
    (expressionAtomCore_trace_reject_complete successComplete rejectComplete contextFrame blockRejectComplete)
    (expressionAtomCore_reject_source_endByte contextFrame nestedRejectFrame blockRejectFrame)

/-- Full-window success context has stronger rejection premises than the trace
laws: recovery is allowed to succeed on the carrier/window returned by a child. -/
theorem expressionAtom_layer_success_context
    (contextFrame : ParserSuccessContext nested) (blockFrame : ParserSuccessContext block)
    (nestedRejectFrame : ∀ {input rejected failure}, nested input = .reject failure rejected →
      rejected.file = input.file ∧ rejected.window = input.window)
    (blockRejectFrame : ∀ {input rejected failure}, block input = .reject failure rejected →
      rejected.file = input.file ∧ rejected.window = input.window) :
    ParserSuccessContext (expressionAtom nested block) :=
  expressionAtom_success_context (expressionAtomCore_trace_success_context contextFrame blockFrame)
    (expressionAtomCore_reject_context contextFrame nestedRejectFrame blockRejectFrame)

end Solcore.Syntax.Parser
