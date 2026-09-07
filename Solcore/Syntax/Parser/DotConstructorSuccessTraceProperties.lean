import Solcore.Syntax.Parser.OptionalDotConstructorArgumentsTraceProperties
import Solcore.Syntax.Parser.ExpressionNameTraceProperties

/-! Exact success of the real leading-dot constructor wrapper. The real
Boolean-first checked name needs no child assumption; only argument expressions
use explicit success trace and source/full-window contracts. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ExpressionAtomInternals

variable {nested : Parser Expr}
  {elementTrace : SourceId → Nat → DeclarativeGrammar.Remainder → Expr →
    DeclarativeGrammar.Remainder → List ParseDiagnostic → Prop}

private theorem bind_ok_parts {α β : Type} {first : Parser α} {next : α → Parser β}
    {input output : State} {value : β} (result : (first >>= next) input = .ok value output) :
    ∃ item after, first input = .ok item after ∧ next item after = .ok value output := by
  cases firstResult : first input <;> simp only [bind, firstResult] at result
  case ok item after => exact ⟨item, after, rfl, result⟩
  case reject => contradiction
  case invariant => contradiction

/-- This seam retains all three exact intermediate successes and the AST mapping. -/
theorem dotConstructor_success_iff_components {input output : State} {value : Expr} :
    dotConstructor nested input = .ok value output ↔
    ∃ dot afterDot name afterName arguments,
      symbol .dot .expression input = .ok dot afterDot ∧
      expressionName afterDot = .ok name afterName ∧
      optionalDotConstructorArguments nested afterName = .ok arguments output ∧
      value = {
        span := SourceSpan.cover dot.span (arguments.map (fun values => values.span) |>.getD name.span)
        value := .dotConstructor dot.span name arguments } := by
  constructor
  · intro result
    unfold dotConstructor at result
    rcases bind_ok_parts result with ⟨dot, afterDot, dotResult, rest⟩
    rcases bind_ok_parts rest with ⟨name, afterName, nameResult, rest⟩
    rcases bind_ok_parts rest with ⟨arguments, afterArguments, argsResult, finished⟩
    cases finished
    exact ⟨dot, afterDot, name, afterName, arguments, dotResult, nameResult, argsResult, rfl⟩
  · rintro ⟨dot, afterDot, name, afterName, arguments, dotResult, nameResult, argsResult, rfl⟩
    simp only [dotConstructor, bind, dotResult, nameResult, argsResult, pure]

theorem dotConstructor_trace_success_sound
    (successSound : ExpressionTraceSuccessSound nested elementTrace)
    (contextFrame : ExpressionSuccessContext nested) :
    ExpressionTraceSuccessSound (dotConstructor nested)
      (DeclarativeGrammar.DotConstructorTraceParses elementTrace) := by
  intro input output value result
  rcases dotConstructor_success_iff_components.mp result with
    ⟨dot, afterDot, name, afterName, arguments, dotResult, nameResult, argsResult, rfl⟩
  have dotParsed := symbol_success_exactTokenParses .dot .expression dotResult
  have dotState := (symbol_ok_tokenAt .dot .expression dotResult).2
  subst afterDot
  rcases expressionName_success_trace_sound nameResult with ⟨nameEvents, nameParsed, nameEq⟩
  have nameFrame := expressionName_success_context_eq nameResult
  rcases optionalDotConstructorArguments_trace_success_sound successSound contextFrame argsResult with
    ⟨argEvents, argsParsed, argsEq⟩
  refine ⟨nameEvents ++ argEvents, .parsed dot.span dotParsed nameParsed ?_, ?_⟩
  · simpa only [nameFrame.1, nameFrame.2] using argsParsed
  · rw [argsEq, nameEq]; exact List.append_assoc _ _ _

theorem dotConstructor_trace_success_complete
    (successComplete : ExpressionTraceSuccessComplete nested elementTrace)
    (contextFrame : ExpressionSuccessContext nested) :
    ExpressionTraceSuccessComplete (dotConstructor nested)
      (DeclarativeGrammar.DotConstructorTraceParses elementTrace) := by
  intro input value after trace parsed
  cases parsed with
  | parsed dotSpan dotParsed nameParsed argsParsed =>
      rename_i afterDot afterName name arguments nameEvents argEvents
      have dotResult := symbol_eq_ok_of_exactTokenParses .dot .expression dotParsed
      rcases dotParsed with ⟨_, rfl⟩
      rcases expressionName_trace_success_complete
          (input := { input with cursor := input.cursor + 1 }) nameParsed with
        ⟨next, nameResult, afterEq, nameEq⟩
      have frame := expressionName_success_context_eq nameResult
      have argsAtNext : DeclarativeGrammar.OptionalDotConstructorArgumentsTraceParses elementTrace
          next.file.id next.window.endByte next.declarativeRemainder arguments after argEvents := by
        simpa only [frame.1, frame.2, afterEq] using argsParsed
      rcases optionalDotConstructorArguments_trace_success_complete successComplete contextFrame argsAtNext with
        ⟨output, argsResult, finalEq, argsEq⟩
      refine ⟨output, dotConstructor_success_iff_components.mpr
        ⟨_, _, name, next, arguments, dotResult, nameResult, argsResult, rfl⟩, finalEq, ?_⟩
      rw [argsEq, nameEq]; exact List.append_assoc _ _ _

theorem dotConstructor_success_context
    (contextFrame : ExpressionSuccessContext nested) : ExpressionSuccessContext (dotConstructor nested) := by
  intro input output value result
  rcases dotConstructor_success_iff_components.mp result with
    ⟨dot, afterDot, name, afterName, arguments, dotResult, nameResult, argsResult, _⟩
  have dotState := (symbol_ok_tokenAt .dot .expression dotResult).2
  have nameFrame := expressionName_success_context_eq nameResult
  have argFrame := optionalDotConstructorArguments_success_context contextFrame argsResult
  rw [dotState] at nameFrame
  exact ⟨argFrame.1.trans nameFrame.1, argFrame.2.trans nameFrame.2⟩

theorem dotConstructor_trace_success_iff
    (successSound : ExpressionTraceSuccessSound nested elementTrace)
    (successComplete : ExpressionTraceSuccessComplete nested elementTrace)
    (contextFrame : ExpressionSuccessContext nested)
    {input : State} {value : Expr} {after : DeclarativeGrammar.Remainder} {trace : List ParseDiagnostic} :
    DeclarativeGrammar.DotConstructorTraceParses elementTrace input.file.id input.window.endByte
      input.declarativeRemainder value after trace ↔
    ∃ output, dotConstructor nested input = .ok value output ∧
      output.declarativeRemainder = after ∧ output.diagnostics = input.diagnostics ++ trace := by
  constructor
  · exact dotConstructor_trace_success_complete successComplete contextFrame
  · rintro ⟨output, result, afterEq, diagnostics⟩
    rcases dotConstructor_trace_success_sound successSound contextFrame result with
      ⟨actualTrace, parsed, actualEq⟩
    have events := List.append_cancel_left (actualEq.symm.trans diagnostics)
    simpa only [afterEq, events] using parsed

end Solcore.Syntax.Parser.ExpressionAtomInternals
