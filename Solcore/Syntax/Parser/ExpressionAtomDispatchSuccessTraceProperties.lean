import Solcore.Syntax.DeclarativeExpressionAtomDispatchTraceGrammar
import Solcore.Syntax.Parser.ExpressionAtomDispatchSelectionTraceProperties
import Solcore.Syntax.Parser.LiteralExpressionTraceProperties
import Solcore.Syntax.Parser.IdentifierExpressionTraceProperties
import Solcore.Syntax.Parser.DotConstructorSuccessTraceProperties
import Solcore.Syntax.Parser.ParenthesizedTraceContextProperties
import Solcore.Syntax.Parser.ArrayLiteralTraceProperties
import Solcore.Syntax.Parser.ProxyExpressionTypeTraceProperties
import Solcore.Syntax.Parser.LambdaExpressionSuccessTraceProperties

/-! One atom-core layer composes exact raw successes. Nested-expression
success frames remain explicit; the final lambda body needs only its own
success contract. These laws do not assert recursive outcome existence. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

open DeclarativeGrammar ExpressionAtomInternals

variable {nested : Parser Expr} {block : Parser Block}
  {elementTrace : SourceId → Nat → Remainder → Expr → Remainder → List ParseDiagnostic → Prop}
  {blockTrace : SourceId → Nat → Remainder → Block → Remainder → List ParseDiagnostic → Prop}

namespace ExpressionAtomDispatchTraceInternals

theorem raw_trace_success_sound
    (successSound : ParserTraceSuccessSound nested elementTrace)
    (contextFrame : ParserSuccessContext nested)
    (blockSound : ParserTraceSuccessSound block blockTrace) (branch : ExpressionAtomDispatchBranch) :
    ParserTraceSuccessSound (rawParser nested block branch)
      (ExpressionAtomDispatchRawTraceParses elementTrace blockTrace branch) := by
  cases branch with
  | literal => exact literalExpression_trace_success_sound
  | name => exact identifierExpression_trace_success_sound
  | dotConstructor => exact dotConstructor_trace_success_sound successSound contextFrame
  | proxy => exact proxyExpression_concrete_trace_success_sound
  | parenthesized => exact parenthesized_trace_success_sound successSound contextFrame
  | array => exact arrayLiteral_trace_success_sound successSound contextFrame
  | lambda => exact lambdaExpression_trace_success_sound blockSound
  | final => intro input output value result; simp [rawParser, rejectAt] at result

theorem raw_trace_success_complete
    (successComplete : ParserTraceSuccessComplete nested elementTrace)
    (contextFrame : ParserSuccessContext nested)
    (blockComplete : ParserTraceSuccessComplete block blockTrace) (branch : ExpressionAtomDispatchBranch) :
    ParserTraceSuccessComplete (rawParser nested block branch)
      (ExpressionAtomDispatchRawTraceParses elementTrace blockTrace branch) := by
  cases branch with
  | literal => exact literalExpression_trace_success_complete
  | name => exact identifierExpression_trace_success_complete
  | dotConstructor => exact dotConstructor_trace_success_complete successComplete contextFrame
  | proxy => exact proxyExpression_concrete_trace_success_complete
  | parenthesized => exact parenthesized_trace_success_complete successComplete contextFrame
  | array => exact arrayLiteral_trace_success_complete successComplete contextFrame
  | lambda => exact lambdaExpression_trace_success_complete blockComplete
  | final => intro input value after trace parsed; exact False.elim parsed

theorem raw_success_context (contextFrame : ParserSuccessContext nested)
    (blockFrame : ParserSuccessContext block) (branch : ExpressionAtomDispatchBranch) :
    ParserSuccessContext (rawParser nested block branch) := by
  cases branch with
  | literal => exact literalExpression_success_context
  | name => exact identifierExpression_success_context
  | dotConstructor => exact dotConstructor_success_context contextFrame
  | proxy => exact proxyExpression_concrete_success_context
  | parenthesized => exact parenthesized_success_context contextFrame
  | array => exact arrayLiteral_success_context contextFrame
  | lambda => exact lambdaExpression_success_context blockFrame
  | final => intro input output value result; simp [rawParser, rejectAt] at result

end ExpressionAtomDispatchTraceInternals

open ExpressionAtomDispatchTraceInternals

theorem ExpressionAtomInternals.expressionAtomCore_trace_success_sound
    (successSound : ParserTraceSuccessSound nested elementTrace)
    (contextFrame : ParserSuccessContext nested)
    (blockSound : ParserTraceSuccessSound block blockTrace) :
    ParserTraceSuccessSound (expressionAtomCore nested block) (ExpressionAtomDispatchTraceParses elementTrace blockTrace) := by
  intro input output value result
  rw [expressionAtomCore_eq_selected_raw] at result
  rcases raw_trace_success_sound successSound contextFrame blockSound (selectedBranch input) result with
    ⟨trace, parsed, events⟩
  exact ⟨trace, .selected (selectedBranch input) (selectedBranch_selects input) parsed, events⟩

theorem ExpressionAtomInternals.expressionAtomCore_trace_success_complete
    (successComplete : ParserTraceSuccessComplete nested elementTrace)
    (contextFrame : ParserSuccessContext nested)
    (blockComplete : ParserTraceSuccessComplete block blockTrace) :
    ParserTraceSuccessComplete (expressionAtomCore nested block) (ExpressionAtomDispatchTraceParses elementTrace blockTrace) := by
  intro input value after trace parsed
  cases parsed with
  | selected branch selection raw =>
      rcases raw_trace_success_complete successComplete contextFrame blockComplete branch raw with
        ⟨output, result, afterEq, events⟩
      exact ⟨output, (expressionAtomCore_eq_raw_of_selection nested block selection).trans result, afterEq, events⟩

theorem ExpressionAtomInternals.expressionAtomCore_trace_success_context
    (contextFrame : ParserSuccessContext nested) (blockFrame : ParserSuccessContext block) :
    ParserSuccessContext (expressionAtomCore nested block) := by
  intro input output value result
  rw [expressionAtomCore_eq_selected_raw] at result
  exact raw_success_context contextFrame blockFrame (selectedBranch input) result

end Solcore.Syntax.Parser
