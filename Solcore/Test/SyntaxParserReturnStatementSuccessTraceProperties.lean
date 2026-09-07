import Solcore.Syntax.Parser.ReturnStatementSuccessTraceProperties

/-! Return-value priority, exact optional ASTs, and duplicate expression events. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserReturnStatementSuccessTraceProperties

open Solcore.Syntax
open Solcore.Syntax.Parser
open Solcore.Syntax.DeclarativeGrammar

variable {expression : Parser Expr}
  {expressionTrace : SourceId → Nat → Remainder → Expr → Remainder → List ParseDiagnostic → Prop}

example := @OptionalReturnValueTraceParses.ordinary
example := @ReturnStatementTraceParses.ordinary
example := @OptionalReturnValueTraceParses.result_unique
example := @ReturnStatementTraceParses.result_unique
example := @returnStatement_success_context

/-- A semicolon suppresses expression evaluation regardless of the supplied
parser and is left in place for the required final-token consumer. -/
theorem current_semicolon_never_invokes_expression
    (expression : Parser Expr) {input : State} {span : SourceSpan}
    (current : TokenAt input.tokens input.window.endIndex input.cursor
      { span, value := .symbol .semicolon }) :
    StatementSimpleInternals.optionalReturnValue expression input = .ok none input :=
  StatementSimpleInternals.optionalReturnValue_eq_ok_none_of_tokenAt expression current

/-- The independent empty-return judgment itself needs no expression premise. -/
theorem empty_return_independent_trace
    {input afterMarker after : Remainder} {source : SourceId} {endByte : Nat}
    {markerSpan semicolonSpan : SourceSpan}
    (marker : ExactTokenParses (.keyword .returnKw) input markerSpan afterMarker)
    (semicolon : ExactTokenParses (.symbol .semicolon) afterMarker semicolonSpan after) :
    ReturnStatementTraceParses expressionTrace source endByte input {
      span := SourceSpan.cover markerSpan semicolonSpan, value := .returnStmt none
    } after [] :=
  .parsed markerSpan semicolonSpan marker (.absent semicolonSpan semicolon.1) semicolon

/-- Empty-return execution is likewise unconditional and retains every prior
event, with exact covering spans and a two-token cursor advance. -/
theorem empty_return_retains_prior_without_expression_contracts
    (expression : Parser Expr) {input : State} {afterMarker after : Remainder}
    {markerSpan semicolonSpan : SourceSpan}
    (marker : ExactTokenParses (.keyword .returnKw) input.declarativeRemainder markerSpan afterMarker)
    (semicolon : ExactTokenParses (.symbol .semicolon) afterMarker semicolonSpan after) :
    ∃ output, returnStatement expression input = .ok {
        span := SourceSpan.cover markerSpan semicolonSpan, value := .returnStmt none
      } output ∧ output.declarativeRemainder = after ∧ output.diagnostics = input.diagnostics := by
  refine ⟨{ input with cursor := input.cursor + 2 },
    returnStatement_eq_ok_none_of_exactTokens expression marker semicolon, ?_, rfl⟩
  rcases marker with ⟨_, rfl⟩
  exact semicolon.2.symm

/-- Nonempty returns preserve the expression AST and repeated event payloads
exactly; the keyword and terminating semicolon add no further diagnostic. -/
theorem present_return_keeps_duplicate_expression_events
    (complete : ExpressionTraceSuccessComplete expression expressionTrace)
    {input : State} {afterMarker afterValue after : Remainder} {value : Expr}
    {markerSpan semicolonSpan : SourceSpan} (event : ParseDiagnostic)
    (marker : ExactTokenParses (.keyword .returnKw) input.declarativeRemainder markerSpan afterMarker)
    (notSemicolon : TokenKindAbsentAt afterMarker.tokens afterMarker.endIndex
      afterMarker.cursor (.symbol .semicolon))
    (valueParsed : expressionTrace input.file.id input.window.endByte
      afterMarker value afterValue [event, event])
    (semicolon : ExactTokenParses (.symbol .semicolon) afterValue semicolonSpan after) :
    ∃ output, returnStatement expression input = .ok {
        span := SourceSpan.cover markerSpan semicolonSpan, value := .returnStmt (some value)
      } output ∧ output.declarativeRemainder = after ∧
      output.diagnostics = input.diagnostics ++ [event, event] :=
  returnStatement_trace_success_complete complete
    (.parsed markerSpan semicolonSpan marker (.present notSemicolon valueParsed) semicolon)

/-- General-expression completeness is conditional, and both explicit laws
remain visible when the exact execution/trace equivalence is consumed. -/
theorem return_exact_success_under_expression_contracts
    (sound : ExpressionTraceSuccessSound expression expressionTrace)
    (complete : ExpressionTraceSuccessComplete expression expressionTrace)
    {input : State} {statement : Statement} {after : Remainder} {trace : List ParseDiagnostic} :
    ReturnStatementTraceParses expressionTrace input.file.id input.window.endByte
      input.declarativeRemainder statement after trace ↔
    ∃ output, returnStatement expression input = .ok statement output ∧
      output.declarativeRemainder = after ∧ output.diagnostics = input.diagnostics ++ trace :=
  returnStatement_trace_success_iff sound complete

end Solcore.Test.SyntaxParserReturnStatementSuccessTraceProperties
