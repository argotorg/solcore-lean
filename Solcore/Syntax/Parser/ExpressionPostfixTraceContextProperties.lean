import Solcore.Syntax.Parser.PostfixTailTraceContextProperties

/-! Separate source/window frames for atom-plus-postfix composition. Rejected
token carriers need not be preserved; a caller chooses the window observation.
No trace, progress, validity, or ordinary-execution premise is introduced. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

open ExpressionAtomInternals

variable {nested : Parser Expr} {block : Parser Block}

theorem expressionPostfix_trace_success_context
    (atomContext : ParserSuccessContext (expressionAtom nested block))
    (nestedContext : ParserSuccessContext nested) :
    ParserSuccessContext (expressionPostfix nested block) := by
  intro input output value result
  unfold expressionPostfix at result
  cases atomResult : expressionAtom nested block input with
  | invariant error => simp [atomResult] at result
  | reject failure rejected => simp [atomResult] at result
  | ok base next =>
      simp only [atomResult] at result
      have atomFrame := atomContext atomResult
      have tailFrame := postfixTail_success_context nestedContext block _ base result
      exact ⟨tailFrame.1.trans atomFrame.1, tailFrame.2.trans atomFrame.2⟩

theorem expressionPostfix_reject_context_of_windowProjection {β : Type} {view : TokenWindow → β}
    (atomContext : ParserSuccessContext (expressionAtom nested block))
    (nestedContext : ParserSuccessContext nested)
    (atomReject : ∀ {input rejected failure}, expressionAtom nested block input = .reject failure rejected →
      rejected.file = input.file ∧ view rejected.window = view input.window)
    (nestedReject : ∀ {input rejected failure}, nested input = .reject failure rejected →
      rejected.file = input.file ∧ view rejected.window = view input.window)
    {input rejected : State} {failure : Failure}
    (result : expressionPostfix nested block input = .reject failure rejected) :
    rejected.file = input.file ∧ view rejected.window = view input.window := by
  unfold expressionPostfix at result
  cases atomResult : expressionAtom nested block input with
  | invariant error => simp [atomResult] at result
  | reject actual next => simp only [atomResult] at result; cases result; exact atomReject atomResult
  | ok base next =>
      simp only [atomResult] at result
      have atomFrame := atomContext atomResult
      have tailFrame := postfixTail_reject_context_of_windowProjection nestedContext nestedReject block _ base result
      exact ⟨tailFrame.1.trans atomFrame.1, tailFrame.2.trans (congrArg view atomFrame.2)⟩

end Solcore.Syntax.Parser
