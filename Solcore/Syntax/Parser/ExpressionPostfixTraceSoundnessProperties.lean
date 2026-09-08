import Solcore.Syntax.DeclarativeExpressionPostfixTraceGrammar
import Solcore.Syntax.Parser.PostfixTailSuccessTraceSoundnessProperties
import Solcore.Syntax.Parser.PostfixTailRejectionTraceSoundnessProperties

/-! The actual atom-plus-postfix parser retains atom events before every
maximal suffix event. Its production tail budget does not need adequacy for
soundness of observed ordinary replies. Atom and nested contracts stay explicit. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

open DeclarativeGrammar ExpressionAtomInternals

variable {nested : Parser Expr} {block : Parser Block}
  {atomTrace nestedTrace : SourceId → Nat → Remainder → Expr → Remainder → List ParseDiagnostic → Prop}
  {atomRejects nestedRejects : SourceId → Nat → Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop}

theorem expressionPostfix_trace_success_sound
    (atomSound : ParserTraceSuccessSound (expressionAtom nested block) atomTrace)
    (atomContext : ParserSuccessContext (expressionAtom nested block))
    (nestedSound : ParserTraceSuccessSound nested nestedTrace)
    (nestedContext : ParserSuccessContext nested) :
    ParserTraceSuccessSound (expressionPostfix nested block)
      (ExpressionPostfixTraceParses atomTrace nestedTrace) := by
  intro input output value result
  unfold expressionPostfix at result
  cases atomResult : expressionAtom nested block input with
  | invariant error => simp [atomResult] at result
  | reject failure rejected => simp [atomResult] at result
  | ok base next =>
      simp only [atomResult] at result
      rcases atomSound atomResult with ⟨atomEvents, atomParsed, atomEq⟩
      have frame := atomContext atomResult
      rcases postfixTail_trace_success_sound nestedSound nestedContext block
          (next.remainingCount + 1) base next value output result with
        ⟨tailEvents, tailParsed, tailEq⟩
      refine ⟨atomEvents ++ tailEvents, .parsed atomParsed ?_, ?_⟩
      · simpa only [frame.1, frame.2] using tailParsed
      · rw [tailEq, atomEq]; exact List.append_assoc _ _ _

theorem expressionPostfix_reject_trace_sound
    (atomSound : ParserTraceSuccessSound (expressionAtom nested block) atomTrace)
    (atomRejectSound : ParserTraceRejectSound (expressionAtom nested block) atomRejects)
    (atomContext : ParserSuccessContext (expressionAtom nested block))
    (nestedSound : ParserTraceSuccessSound nested nestedTrace)
    (nestedRejectSound : ParserTraceRejectSound nested nestedRejects)
    (nestedContext : ParserSuccessContext nested) :
    ParserTraceRejectSound (expressionPostfix nested block)
      (ExpressionPostfixTraceRejects atomTrace nestedTrace atomRejects nestedRejects) := by
  intro input rejected failure result
  unfold expressionPostfix at result
  cases atomResult : expressionAtom nested block input with
  | invariant error => simp [atomResult] at result
  | reject actual next =>
      simp only [atomResult] at result; cases result
      rcases atomRejectSound atomResult with ⟨trace, rejection, events⟩
      exact ⟨trace, .atomRejected rejection, events⟩
  | ok base next =>
      simp only [atomResult] at result
      rcases atomSound atomResult with ⟨atomEvents, atomParsed, atomEq⟩
      have frame := atomContext atomResult
      rcases postfixTail_reject_trace_sound nestedSound nestedRejectSound nestedContext block
          (next.remainingCount + 1) base next failure rejected result with
        ⟨tailEvents, tailRejected, tailEq⟩
      refine ⟨atomEvents ++ tailEvents, .tailRejected atomParsed ?_, ?_⟩
      · simpa only [frame.1, frame.2] using tailRejected
      · rw [tailEq, atomEq]; exact List.append_assoc _ _ _

end Solcore.Syntax.Parser
