import Solcore.Syntax.Parser.ParenthesizedTraceContextProperties

/-! Exact successful parenthesized outcomes and arbitrary-prefix tuple tails.
The final AST is assembled from forward values; closing spans stay explicit. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ExpressionAtomInternals

variable {nested : Parser Expr}
  {elementTrace : SourceId → Nat → DeclarativeGrammar.Remainder → Expr →
    DeclarativeGrammar.Remainder → List ParseDiagnostic → Prop}

theorem tupleTail_trace_success_iff
    (successSound : ExpressionTraceSuccessSound nested elementTrace)
    (successComplete : ExpressionTraceSuccessComplete nested elementTrace)
    (contextFrame : ExpressionSuccessContext nested) (opening : Token) (fuel : Nat) (elementsRev : List Expr)
    {input : State} (adequate : input.remainingCount < fuel) {value : Expr}
    {after : DeclarativeGrammar.Remainder} {trace : List ParseDiagnostic} :
    (∃ suffix closingSpan,
      value = DeclarativeGrammar.closeParenthesizedExpression opening.span closingSpan (elementsRev.reverse ++ suffix) ∧
      DeclarativeGrammar.ParenthesizedTupleTailTraceParses elementTrace input.file.id input.window.endByte
        input.declarativeRemainder suffix closingSpan after trace) ↔
    ∃ output, tupleTail nested opening fuel elementsRev input = .ok value output ∧
      output.declarativeRemainder = after ∧ output.diagnostics = input.diagnostics ++ trace := by
  constructor
  · rintro ⟨suffix, closingSpan, rfl, parsed⟩
    exact tupleTail_trace_success_complete successComplete contextFrame opening fuel elementsRev parsed adequate
  · rintro ⟨output, result, afterEq, diagnostics⟩
    rcases tupleTail_success_trace_sound successSound contextFrame opening fuel elementsRev input value output result with
      ⟨suffix, closingSpan, actualTrace, valueEq, parsed, actualEq⟩
    have events := List.append_cancel_left (actualEq.symm.trans diagnostics)
    exact ⟨suffix, closingSpan, valueEq, by simpa only [afterEq, events] using parsed⟩

theorem tupleTail_production_trace_success_iff
    (successSound : ExpressionTraceSuccessSound nested elementTrace)
    (successComplete : ExpressionTraceSuccessComplete nested elementTrace)
    (contextFrame : ExpressionSuccessContext nested) (opening : Token) (elementsRev : List Expr)
    {input : State} {value : Expr} {after : DeclarativeGrammar.Remainder} {trace : List ParseDiagnostic} :
    (∃ suffix closingSpan,
      value = DeclarativeGrammar.closeParenthesizedExpression opening.span closingSpan (elementsRev.reverse ++ suffix) ∧
      DeclarativeGrammar.ParenthesizedTupleTailTraceParses elementTrace input.file.id input.window.endByte
        input.declarativeRemainder suffix closingSpan after trace) ↔
    ∃ output, tupleTail nested opening (input.remainingCount + 1) elementsRev input = .ok value output ∧
      output.declarativeRemainder = after ∧ output.diagnostics = input.diagnostics ++ trace :=
  tupleTail_trace_success_iff successSound successComplete contextFrame opening
    (input.remainingCount + 1) elementsRev (by omega)

theorem parenthesized_trace_success_iff
    (successSound : ExpressionTraceSuccessSound nested elementTrace)
    (successComplete : ExpressionTraceSuccessComplete nested elementTrace)
    (contextFrame : ExpressionSuccessContext nested)
    {input : State} {value : Expr} {after : DeclarativeGrammar.Remainder} {trace : List ParseDiagnostic} :
    DeclarativeGrammar.ParenthesizedExpressionTraceParses elementTrace input.file.id input.window.endByte
      input.declarativeRemainder value after trace ↔
    ∃ output, parenthesized nested input = .ok value output ∧
      output.declarativeRemainder = after ∧ output.diagnostics = input.diagnostics ++ trace := by
  constructor
  · exact parenthesized_trace_success_complete successComplete contextFrame
  · rintro ⟨output, result, afterEq, diagnostics⟩
    rcases parenthesized_trace_success_sound successSound contextFrame result with ⟨actualTrace, parsed, actualEq⟩
    have events := List.append_cancel_left (actualEq.symm.trans diagnostics)
    simpa only [afterEq, events] using parsed

end Solcore.Syntax.Parser.ExpressionAtomInternals
