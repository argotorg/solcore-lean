import Solcore.Syntax.DeclarativeExpressionAtomDispatchTraceGrammar
import Solcore.Syntax.Parser.ExpressionAtomDispatchSelectionTraceProperties
import Solcore.Syntax.Parser.LiteralExpressionTraceProperties
import Solcore.Syntax.Parser.IdentifierExpressionTraceProperties
import Solcore.Syntax.Parser.DotConstructorRejectionTraceProperties
import Solcore.Syntax.Parser.ParenthesizedRejectionTraceCorrespondenceProperties
import Solcore.Syntax.Parser.ArrayLiteralTraceProperties
import Solcore.Syntax.Parser.ProxyExpressionTypeTraceProperties
import Solcore.Syntax.Parser.LambdaExpressionRejectionTraceProperties

/-! Exact rejection of one selected atom-core layer. Only executed nested
successes require a context frame; the final lambda body forwards its rejection
directly. No rejection-frame, progress, validity, or ordinary premise is hidden. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

open DeclarativeGrammar ExpressionAtomInternals

variable {nested : Parser Expr} {block : Parser Block}
  {elementTrace : SourceId → Nat → Remainder → Expr → Remainder → List ParseDiagnostic → Prop}
  {elementRejects : SourceId → Nat → Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop}
  {blockRejects : SourceId → Nat → Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop}

namespace ExpressionAtomDispatchTraceInternals

theorem raw_reject_trace_sound
    (successSound : ParserTraceSuccessSound nested elementTrace)
    (rejectSound : ParserTraceRejectSound nested elementRejects)
    (contextFrame : ParserSuccessContext nested)
    (blockSound : ParserTraceRejectSound block blockRejects) (branch : ExpressionAtomDispatchBranch) :
    ParserTraceRejectSound (rawParser nested block branch)
      (ExpressionAtomDispatchRawTraceRejects elementTrace elementRejects blockRejects branch) := by
  cases branch with
  | literal => exact literalExpression_trace_reject_sound
  | name => exact identifierExpression_trace_reject_sound
  | dotConstructor => exact dotConstructor_reject_trace_sound successSound rejectSound contextFrame
  | proxy => exact proxyExpression_concrete_reject_trace_sound
  | parenthesized => exact parenthesized_reject_trace_sound successSound rejectSound contextFrame
  | array => exact arrayLiteral_trace_reject_sound successSound rejectSound contextFrame
  | lambda => exact lambdaExpression_reject_trace_sound blockSound
  | final =>
      intro input rejected failure result
      have reported := rejectAt_reject_reports { head := .expression, tail := [] } .expression result
      have same : rejected = input := by unfold rawParser rejectAt at result; cases result; rfl
      subst rejected
      exact ⟨[], .rejected reported.1, by simp only [List.append_nil]⟩

theorem raw_trace_reject_complete
    (successComplete : ParserTraceSuccessComplete nested elementTrace)
    (rejectComplete : ParserTraceRejectComplete nested elementRejects)
    (contextFrame : ParserSuccessContext nested)
    (blockComplete : ParserTraceRejectComplete block blockRejects) (branch : ExpressionAtomDispatchBranch) :
    ParserTraceRejectComplete (rawParser nested block branch)
      (ExpressionAtomDispatchRawTraceRejects elementTrace elementRejects blockRejects branch) := by
  cases branch with
  | literal => exact literalExpression_trace_reject_complete
  | name => exact identifierExpression_trace_reject_complete
  | dotConstructor => exact dotConstructor_trace_reject_complete successComplete rejectComplete contextFrame
  | proxy => exact proxyExpression_concrete_trace_reject_complete
  | parenthesized => exact parenthesized_trace_reject_complete successComplete rejectComplete contextFrame
  | array => exact arrayLiteral_trace_reject_complete successComplete rejectComplete contextFrame
  | lambda => exact lambdaExpression_trace_reject_complete blockComplete
  | final =>
      intro input after report trace rejection
      cases rejection with
      | rejected reported =>
          rcases (rejectAt_reports_iff (alpha := Expr)).mp reported with ⟨failure, result, reportEq⟩
          exact ⟨failure, input, result, rfl, reportEq, by simp only [List.append_nil]⟩

end ExpressionAtomDispatchTraceInternals

open ExpressionAtomDispatchTraceInternals

theorem ExpressionAtomInternals.expressionAtomCore_reject_trace_sound
    (successSound : ParserTraceSuccessSound nested elementTrace)
    (rejectSound : ParserTraceRejectSound nested elementRejects)
    (contextFrame : ParserSuccessContext nested)
    (blockSound : ParserTraceRejectSound block blockRejects) :
    ParserTraceRejectSound (expressionAtomCore nested block)
      (ExpressionAtomDispatchTraceRejects elementTrace elementRejects blockRejects) := by
  intro input rejected failure result
  rw [expressionAtomCore_eq_selected_raw] at result
  rcases raw_reject_trace_sound successSound rejectSound contextFrame blockSound (selectedBranch input) result with
    ⟨trace, rejection, events⟩
  exact ⟨trace, .selected (selectedBranch input) (selectedBranch_selects input) rejection, events⟩

theorem ExpressionAtomInternals.expressionAtomCore_trace_reject_complete
    (successComplete : ParserTraceSuccessComplete nested elementTrace)
    (rejectComplete : ParserTraceRejectComplete nested elementRejects)
    (contextFrame : ParserSuccessContext nested)
    (blockComplete : ParserTraceRejectComplete block blockRejects) :
    ParserTraceRejectComplete (expressionAtomCore nested block)
      (ExpressionAtomDispatchTraceRejects elementTrace elementRejects blockRejects) := by
  intro input after report trace rejection
  cases rejection with
  | selected branch selection raw =>
      rcases raw_trace_reject_complete successComplete rejectComplete contextFrame blockComplete branch raw with
        ⟨failure, rejected, result, afterEq, reportEq, events⟩
      exact ⟨failure, rejected, (expressionAtomCore_eq_raw_of_selection nested block selection).trans result,
        afterEq, reportEq, events⟩

end Solcore.Syntax.Parser
