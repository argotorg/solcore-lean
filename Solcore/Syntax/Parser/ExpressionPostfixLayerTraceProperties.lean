import Solcore.Syntax.DeclarativeExpressionPostfixLayerTraceProperties
import Solcore.Syntax.Parser.ExpressionPostfixTraceSoundnessProperties
import Solcore.Syntax.Parser.ExpressionAtomLayerTraceProperties

/-! Actual selected-core/recovery/postfix trace soundness with only recursive
expression/body contracts left supplied. Successful atom framing is explicit:
the full rejected child windows used here also frame recovered atom successes.
No completeness, totality, or recursive closure is inferred from these laws. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

open DeclarativeGrammar

variable {nested : Parser Expr} {block : Parser Block}
  {nestedTrace : SourceId → Nat → Remainder → Expr → Remainder → List ParseDiagnostic → Prop}
  {nestedRejects : SourceId → Nat → Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop}
  {blockTrace : SourceId → Nat → Remainder → Block → Remainder → List ParseDiagnostic → Prop}
  {blockRejects : SourceId → Nat → Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop}

variable (successSound : ParserTraceSuccessSound nested nestedTrace)
  (rejectSound : ParserTraceRejectSound nested nestedRejects)
  (contextFrame : ParserSuccessContext nested)
  (blockSuccessSound : ParserTraceSuccessSound block blockTrace)
  (blockRejectSound : ParserTraceRejectSound block blockRejects)
  (blockContext : ParserSuccessContext block)
  (nestedRejectFrame : ∀ {input rejected failure}, nested input = .reject failure rejected →
    rejected.file = input.file ∧ rejected.window = input.window)
  (blockRejectFrame : ∀ {input rejected failure}, block input = .reject failure rejected →
    rejected.file = input.file ∧ rejected.window = input.window)

include successSound rejectSound contextFrame blockSuccessSound blockRejectSound blockContext
  nestedRejectFrame blockRejectFrame

theorem expressionPostfix_layer_trace_success_sound :
    ParserTraceSuccessSound (expressionPostfix nested block)
      (ExpressionPostfixLayerTraceParses nestedTrace nestedRejects blockTrace blockRejects) :=
  expressionPostfix_trace_success_sound
    (expressionAtom_layer_trace_success_sound successSound rejectSound contextFrame blockSuccessSound blockRejectSound
      (fun result => ⟨(nestedRejectFrame result).1, congrArg TokenWindow.endByte (nestedRejectFrame result).2⟩)
      (fun result => ⟨(blockRejectFrame result).1, congrArg TokenWindow.endByte (blockRejectFrame result).2⟩))
    (expressionAtom_layer_success_context contextFrame blockContext nestedRejectFrame blockRejectFrame)
    successSound contextFrame

theorem expressionPostfix_layer_reject_trace_sound :
    ParserTraceRejectSound (expressionPostfix nested block)
      (ExpressionPostfixLayerTraceRejects nestedTrace nestedRejects blockTrace blockRejects) :=
  expressionPostfix_reject_trace_sound
    (expressionAtom_layer_trace_success_sound successSound rejectSound contextFrame blockSuccessSound blockRejectSound
      (fun result => ⟨(nestedRejectFrame result).1, congrArg TokenWindow.endByte (nestedRejectFrame result).2⟩)
      (fun result => ⟨(blockRejectFrame result).1, congrArg TokenWindow.endByte (blockRejectFrame result).2⟩))
    (expressionAtom_layer_reject_trace_sound successSound rejectSound contextFrame blockRejectSound
      (fun result => ⟨(nestedRejectFrame result).1, congrArg TokenWindow.endByte (nestedRejectFrame result).2⟩)
      (fun result => ⟨(blockRejectFrame result).1, congrArg TokenWindow.endByte (blockRejectFrame result).2⟩))
    (expressionAtom_layer_success_context contextFrame blockContext nestedRejectFrame blockRejectFrame)
    successSound rejectSound contextFrame

end Solcore.Syntax.Parser
