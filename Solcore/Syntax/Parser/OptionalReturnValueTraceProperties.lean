import Solcore.Syntax.DeclarativeReturnStatementTraceProperties
import Solcore.Syntax.Parser.ExpressionDiagnosticTraceContracts
import Solcore.Syntax.Parser.DelimitedRejectionPrimitiveProperties
import Solcore.Syntax.Parser.Statement.Simple

/-! Exact optional-return success with semicolon-first priority. Expression
events are retained unchanged, and the empty-value branch never invokes it. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.StatementSimpleInternals

variable {expression : Parser Expr}
  {expressionTrace : SourceId → Nat → DeclarativeGrammar.Remainder → Expr →
    DeclarativeGrammar.Remainder → List ParseDiagnostic → Prop}

theorem optionalReturnValue_eq_ok_none_of_tokenAt
    (expression : Parser Expr) {input : State} {span : SourceSpan}
    (current : DeclarativeGrammar.TokenAt input.tokens input.window.endIndex input.cursor
      { span, value := .symbol .semicolon }) :
    optionalReturnValue expression input = .ok none input := by
  have present : isSymbol input .semicolon = true := by
    unfold isSymbol State.peekKind? State.peek?
    simp only [current.1, ↓reduceIte, current.2, Option.map_some]
    rfl
  simp only [optionalReturnValue, getState, bind, present, if_true, pure]

/-- Absent semicolon delegates precisely one expression, propagating either
ordinary failure or success without changing any events or state fields. -/
theorem optionalReturnValue_eq_of_semicolonAbsent
    (expression : Parser Expr) {input : State}
    (absent : DeclarativeGrammar.TokenKindAbsentAt input.tokens input.window.endIndex
      input.cursor (.symbol .semicolon)) :
    optionalReturnValue expression input = match expression input with
      | .ok value output => .ok (some value) output
      | .reject failure rejected => .reject failure rejected
      | .invariant error => .invariant error := by
  have notPresent : isSymbol input .semicolon = false := by
    apply Bool.eq_false_iff.mpr
    intro present
    rcases symbol_eq_ok_of_isSymbol_eq_true .semicolon .statement present with ⟨token, result⟩
    exact absent ⟨token.span, (symbol_ok_tokenAt .semicolon .statement result).1⟩
  simp only [optionalReturnValue, getState, bind, notPresent, Bool.false_eq_true, if_false, pure]
  cases expression input <;> rfl

theorem optionalReturnValue_success_trace_sound
    (sound : ExpressionTraceSuccessSound expression expressionTrace)
    {input output : State} {value : Option Expr}
    (result : optionalReturnValue expression input = .ok value output) :
    ∃ trace, DeclarativeGrammar.OptionalReturnValueTraceParses expressionTrace
      input.file.id input.window.endByte input.declarativeRemainder value output.declarativeRemainder trace ∧
      output.diagnostics = input.diagnostics ++ trace := by
  by_cases present : isSymbol input .semicolon = true
  · rcases symbol_eq_ok_of_isSymbol_eq_true .semicolon .statement present with ⟨token, tokenResult⟩
    have current := (symbol_ok_tokenAt .semicolon .statement tokenResult).1
    rw [optionalReturnValue_eq_ok_none_of_tokenAt expression current] at result
    cases result
    exact ⟨[], .absent token.span current, by simp only [List.append_nil]⟩
  · have absent := symbolAbsentAt_of_isSymbol_eq_false .semicolon (Bool.eq_false_iff.mpr present)
    rw [optionalReturnValue_eq_of_semicolonAbsent expression absent] at result
    cases valueResult : expression input with
    | invariant error => simp [valueResult] at result
    | reject failure rejected => simp [valueResult] at result
    | ok expressionValue next =>
        simp only [valueResult] at result
        cases result
        rcases sound valueResult with ⟨trace, parsed, events⟩
        exact ⟨trace, .present absent parsed, events⟩

theorem optionalReturnValue_trace_success_complete
    (complete : ExpressionTraceSuccessComplete expression expressionTrace)
    {input : State} {value : Option Expr} {after : DeclarativeGrammar.Remainder}
    {trace : List ParseDiagnostic}
    (parsed : DeclarativeGrammar.OptionalReturnValueTraceParses expressionTrace
      input.file.id input.window.endByte input.declarativeRemainder value after trace) :
    ∃ output, optionalReturnValue expression input = .ok value output ∧
      output.declarativeRemainder = after ∧ output.diagnostics = input.diagnostics ++ trace := by
  cases parsed with
  | absent span current =>
      exact ⟨input, optionalReturnValue_eq_ok_none_of_tokenAt expression current, rfl,
        by simp only [List.append_nil]⟩
  | present absent valueParsed =>
      rcases complete valueParsed with ⟨output, result, afterEq, events⟩
      exact ⟨output, by rw [optionalReturnValue_eq_of_semicolonAbsent expression absent, result],
        afterEq, events⟩

theorem optionalReturnValue_success_context_eq
    (contextFrame : ExpressionSuccessContext expression)
    {input output : State} {value : Option Expr}
    (result : optionalReturnValue expression input = .ok value output) :
    output.file = input.file ∧ output.window = input.window := by
  unfold optionalReturnValue getState at result
  simp only [bind] at result
  cases present : isSymbol input .semicolon with
  | true => simp only [present, if_true, pure] at result; cases result; exact ⟨rfl, rfl⟩
  | false =>
      simp only [present, Bool.false_eq_true, if_false] at result
      cases valueResult : expression input with
      | invariant error => simp [valueResult] at result
      | reject failure rejected => simp [valueResult] at result
      | ok expressionValue next =>
          simp only [valueResult, pure] at result
          cases result
          exact contextFrame valueResult

theorem optionalReturnValue_trace_success_iff
    (sound : ExpressionTraceSuccessSound expression expressionTrace)
    (complete : ExpressionTraceSuccessComplete expression expressionTrace)
    {input : State} {value : Option Expr} {after : DeclarativeGrammar.Remainder}
    {trace : List ParseDiagnostic} :
    DeclarativeGrammar.OptionalReturnValueTraceParses expressionTrace
      input.file.id input.window.endByte input.declarativeRemainder value after trace ↔
    ∃ output, optionalReturnValue expression input = .ok value output ∧
      output.declarativeRemainder = after ∧ output.diagnostics = input.diagnostics ++ trace := by
  constructor
  · exact optionalReturnValue_trace_success_complete complete
  · rintro ⟨output, result, afterEq, diagnostics⟩
    rcases optionalReturnValue_success_trace_sound sound result with ⟨actualTrace, parsed, actualEq⟩
    have events : actualTrace = trace := List.append_cancel_left (actualEq.symm.trans diagnostics)
    simpa only [afterEq, events] using parsed

end Solcore.Syntax.Parser.StatementSimpleInternals
