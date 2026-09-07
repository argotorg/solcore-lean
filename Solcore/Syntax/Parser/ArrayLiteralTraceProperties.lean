import Solcore.Syntax.DeclarativeArrayLiteralTraceGrammar
import Solcore.Syntax.Parser.DelimitedNoTrailingTraceCompletenessProperties
import Solcore.Syntax.Parser.DelimitedNoTrailingTraceContextProperties
import Solcore.Syntax.Parser.DelimitedNoTrailingRejectionTraceCompletenessProperties
import Solcore.Syntax.Parser.ExpressionDiagnosticTraceContracts
import Solcore.Syntax.Parser.Expression.Atom

/-! Exact traces for the actual array wrapper, conditional only on the five
child-expression contracts. Successful mapping changes the AST alone; ordinary
failure and its complete state escape unchanged without committing a report. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ExpressionAtomInternals

variable {element : Parser Expr}
  {elementTrace : SourceId → Nat → DeclarativeGrammar.Remainder → Expr →
    DeclarativeGrammar.Remainder → List ParseDiagnostic → Prop}
  {elementRejects : SourceId → Nat → DeclarativeGrammar.Remainder →
    DeclarativeGrammar.Remainder → ParseDiagnostic → List ParseDiagnostic → Prop}

theorem arrayLiteral_success_iff_raw {input output : State} {value : Expr} :
    arrayLiteral element input = .ok value output ↔
      ∃ values, delimitedNoTrailing .leftBracket .rightBracket true element .expression .expression input =
        .ok values output ∧ value = { span := values.span, value := .array values } := by
  cases result : delimitedNoTrailing .leftBracket .rightBracket true element .expression .expression input <;>
    simp only [arrayLiteral, bind, result, pure, reduceCtorEq, Reply.ok.injEq]
  case ok values next =>
    constructor
    · rintro ⟨rfl, rfl⟩; exact ⟨values, ⟨rfl, rfl⟩, rfl⟩
    · rintro ⟨other, ⟨rfl, rfl⟩, rfl⟩; exact ⟨rfl, rfl⟩
  case reject => simp
  case invariant => simp

theorem arrayLiteral_reject_iff_raw {input rejected : State} {failure : Failure} :
    arrayLiteral element input = .reject failure rejected ↔
      delimitedNoTrailing .leftBracket .rightBracket true element .expression .expression input =
        .reject failure rejected := by
  cases result : delimitedNoTrailing .leftBracket .rightBracket true element .expression .expression input <;>
    simp only [arrayLiteral, bind, result, pure, reduceCtorEq, Reply.reject.injEq, iff_self]

theorem arrayLiteral_trace_success_sound
    (successSound : ExpressionTraceSuccessSound element elementTrace)
    (contextFrame : ExpressionSuccessContext element) :
    ExpressionTraceSuccessSound (arrayLiteral element)
      (DeclarativeGrammar.ArrayLiteralTraceParses elementTrace) := by
  intro input output value result
  rcases arrayLiteral_success_iff_raw.mp result with ⟨values, raw, rfl⟩
  rcases delimitedNoTrailing_success_trace_sound successSound contextFrame
      .leftBracket .rightBracket true .expression .expression raw with ⟨trace, parsed, events⟩
  exact ⟨trace, .parsed parsed, events⟩

theorem arrayLiteral_trace_success_complete
    (successComplete : ExpressionTraceSuccessComplete element elementTrace)
    (contextFrame : ExpressionSuccessContext element) :
    ExpressionTraceSuccessComplete (arrayLiteral element)
      (DeclarativeGrammar.ArrayLiteralTraceParses elementTrace) := by
  intro input value after trace parsed
  cases parsed with
  | parsed values =>
      rcases delimitedNoTrailing_trace_success_complete successComplete contextFrame
          .leftBracket .rightBracket true .expression .expression values with ⟨output, result, afterEq, events⟩
      exact ⟨output, arrayLiteral_success_iff_raw.mpr ⟨_, result, rfl⟩, afterEq, events⟩

theorem arrayLiteral_trace_reject_sound
    (successSound : ExpressionTraceSuccessSound element elementTrace)
    (rejectSound : ExpressionTraceRejectSound element elementRejects)
    (contextFrame : ExpressionSuccessContext element) :
    ExpressionTraceRejectSound (arrayLiteral element)
      (DeclarativeGrammar.ArrayLiteralTraceRejects elementTrace elementRejects) := by
  intro input rejected failure result
  exact delimitedNoTrailing_reject_trace_sound successSound rejectSound contextFrame
    .leftBracket .rightBracket true .expression .expression (arrayLiteral_reject_iff_raw.mp result)

theorem arrayLiteral_trace_reject_complete
    (successComplete : ExpressionTraceSuccessComplete element elementTrace)
    (rejectComplete : ExpressionTraceRejectComplete element elementRejects)
    (contextFrame : ExpressionSuccessContext element) :
    ExpressionTraceRejectComplete (arrayLiteral element)
      (DeclarativeGrammar.ArrayLiteralTraceRejects elementTrace elementRejects) := by
  intro input after diagnostic trace rejected
  rcases delimitedNoTrailing_trace_reject_complete successComplete rejectComplete contextFrame
      .leftBracket .rightBracket true .expression .expression rejected with
    ⟨failure, output, result, afterEq, reportEq, events⟩
  exact ⟨failure, output, arrayLiteral_reject_iff_raw.mpr result, afterEq, reportEq, events⟩

theorem arrayLiteral_success_context
    (contextFrame : ExpressionSuccessContext element) :
    ExpressionSuccessContext (arrayLiteral element) := by
  intro input output value result
  rcases arrayLiteral_success_iff_raw.mp result with ⟨values, raw, _⟩
  exact delimitedNoTrailing_success_context contextFrame .leftBracket .rightBracket true
    .expression .expression raw

theorem arrayLiteral_trace_success_iff
    (successSound : ExpressionTraceSuccessSound element elementTrace)
    (successComplete : ExpressionTraceSuccessComplete element elementTrace)
    (contextFrame : ExpressionSuccessContext element)
    {input : State} {value : Expr} {after : DeclarativeGrammar.Remainder} {trace : List ParseDiagnostic} :
    DeclarativeGrammar.ArrayLiteralTraceParses elementTrace input.file.id input.window.endByte
      input.declarativeRemainder value after trace ↔
      ∃ output, arrayLiteral element input = .ok value output ∧
        output.declarativeRemainder = after ∧ output.diagnostics = input.diagnostics ++ trace := by
  constructor
  · exact arrayLiteral_trace_success_complete successComplete contextFrame
  · rintro ⟨output, result, afterEq, events⟩
    rcases arrayLiteral_trace_success_sound successSound contextFrame result with
      ⟨actual, parsed, actualEvents⟩
    have traceEq : actual = trace := List.append_cancel_left (actualEvents.symm.trans events)
    simpa only [afterEq, traceEq] using parsed

theorem arrayLiteral_trace_reject_iff
    (successSound : ExpressionTraceSuccessSound element elementTrace)
    (rejectSound : ExpressionTraceRejectSound element elementRejects)
    (successComplete : ExpressionTraceSuccessComplete element elementTrace)
    (rejectComplete : ExpressionTraceRejectComplete element elementRejects)
    (contextFrame : ExpressionSuccessContext element)
    {input : State} {after : DeclarativeGrammar.Remainder}
    {diagnostic : ParseDiagnostic} {trace : List ParseDiagnostic} :
    DeclarativeGrammar.ArrayLiteralTraceRejects elementTrace elementRejects input.file.id input.window.endByte
      input.declarativeRemainder after diagnostic trace ↔
      ∃ failure rejected, arrayLiteral element input = .reject failure rejected ∧
        rejected.declarativeRemainder = after ∧ failure.toDiagnostic = diagnostic ∧
        rejected.diagnostics = input.diagnostics ++ trace := by
  constructor
  · exact arrayLiteral_trace_reject_complete successComplete rejectComplete contextFrame
  · rintro ⟨failure, rejected, result, afterEq, reportEq, events⟩
    rcases arrayLiteral_trace_reject_sound successSound rejectSound contextFrame result with
      ⟨actual, rejection, actualEvents⟩
    have traceEq : actual = trace := List.append_cancel_left (actualEvents.symm.trans events)
    simpa only [afterEq, reportEq, traceEq] using rejection

theorem arrayLiteral_trace_reject_failure_iff
    (successSound : ExpressionTraceSuccessSound element elementTrace)
    (rejectSound : ExpressionTraceRejectSound element elementRejects)
    (successComplete : ExpressionTraceSuccessComplete element elementTrace)
    (rejectComplete : ExpressionTraceRejectComplete element elementRejects)
    (contextFrame : ExpressionSuccessContext element)
    {input : State} {after : DeclarativeGrammar.Remainder}
    {failure : Failure} {trace : List ParseDiagnostic} :
    DeclarativeGrammar.ArrayLiteralTraceRejects elementTrace elementRejects input.file.id input.window.endByte
      input.declarativeRemainder after failure.toDiagnostic trace ↔
      ∃ rejected, arrayLiteral element input = .reject failure rejected ∧
        rejected.declarativeRemainder = after ∧ rejected.diagnostics = input.diagnostics ++ trace := by
  rw [arrayLiteral_trace_reject_iff successSound rejectSound successComplete rejectComplete contextFrame]
  constructor
  · rintro ⟨actual, rejected, result, afterEq, reportEq, events⟩
    cases Failure.toDiagnostic_injective reportEq
    exact ⟨rejected, result, afterEq, events⟩
  · rintro ⟨rejected, result, afterEq, events⟩
    exact ⟨failure, rejected, result, afterEq, rfl, events⟩

end Solcore.Syntax.Parser.ExpressionAtomInternals
