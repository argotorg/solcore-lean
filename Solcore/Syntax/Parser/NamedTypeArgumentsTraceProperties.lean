import Solcore.Syntax.Parser.NamedTypeArgumentsTracePrimitiveProperties

/-! Exact optional nonempty named-type arguments. Recursive success and the
source/full-window frame are explicit; neither silent children nor valid or
token-preserving input is assumed by these execution contracts. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

variable {nested : Parser TypeExpr}
  {elementTrace : SourceId → Nat → DeclarativeGrammar.Remainder → TypeExpr →
    DeclarativeGrammar.Remainder → List ParseDiagnostic → Prop}

theorem parseNamedTypeArguments_trace_success_sound
    (successSound : ParserTraceSuccessSound nested elementTrace)
    (contextFrame : ParserSuccessContext nested) :
    ParserTraceSuccessSound (parseNamedTypeArguments nested)
      (DeclarativeGrammar.NamedTypeArgumentsTraceParses elementTrace) := by
  intro input output arguments result
  by_cases present : isSymbol input .less = true
  · rcases symbol_eq_ok_of_isSymbol_eq_true .less .typeExpr present with ⟨token, tokenResult⟩
    rw [parseNamedTypeArguments_eq_of_present nested
      (symbol_ok_tokenAt .less .typeExpr tokenResult).1] at result
    cases argsResult : delimited .less .greater false nested .typeExpr .typeExpr input with
    | invariant error => simp [argsResult] at result
    | reject failure rejected => simp [argsResult] at result
    | ok values next =>
        simp only [argsResult] at result
        cases converted : requireNonempty values .typeExpr next with
        | invariant error => simp [converted] at result
        | reject failure rejected => simp [converted] at result
        | ok nonempty final =>
            simp only [converted] at result
            cases result
            have shape := (requireNonempty_success_iff_toList .typeExpr).mp converted
            rw [shape.2]
            rcases delimited_trace_success_sound successSound contextFrame
                .less .greater false .typeExpr .typeExpr argsResult with ⟨trace, parsed, diagnostics⟩
            exact ⟨trace, .present (by simpa only [shape.1] using parsed), diagnostics⟩
  · have absent := symbolAbsentAt_of_isSymbol_eq_false .less (Bool.eq_false_iff.mpr present)
    rw [parseNamedTypeArguments_eq_none_of_absent nested absent] at result
    cases result
    exact ⟨[], .absent absent, by simp only [List.append_nil]⟩

theorem parseNamedTypeArguments_trace_success_complete
    (successComplete : ParserTraceSuccessComplete nested elementTrace)
    (contextFrame : ParserSuccessContext nested) :
    ParserTraceSuccessComplete (parseNamedTypeArguments nested)
      (DeclarativeGrammar.NamedTypeArgumentsTraceParses elementTrace) := by
  intro input arguments after trace parsed
  cases parsed with
  | absent absent =>
      exact ⟨input, parseNamedTypeArguments_eq_none_of_absent nested absent, rfl,
        by simp only [List.append_nil]⟩
  | present parsed =>
      rcases (DeclarativeGrammar.NamedTypeArgumentsTraceParses.present parsed).present_token with
        ⟨span, opening⟩
      rcases delimited_trace_success_complete successComplete contextFrame
          .less .greater false .typeExpr .typeExpr parsed with ⟨output, result, afterEq, diagnostics⟩
      refine ⟨output, ?_, afterEq, diagnostics⟩
      rw [parseNamedTypeArguments_eq_of_present nested opening, result]
      simp only [requireNonempty_eq_ok_of_toList]

theorem parseNamedTypeArguments_success_context
    (contextFrame : ParserSuccessContext nested) :
    ParserSuccessContext (parseNamedTypeArguments nested) := by
  intro input output arguments result
  by_cases present : isSymbol input .less = true
  · rcases symbol_eq_ok_of_isSymbol_eq_true .less .typeExpr present with ⟨token, tokenResult⟩
    rw [parseNamedTypeArguments_eq_of_present nested
      (symbol_ok_tokenAt .less .typeExpr tokenResult).1] at result
    cases argsResult : delimited .less .greater false nested .typeExpr .typeExpr input with
    | invariant error => simp [argsResult] at result
    | reject failure rejected => simp [argsResult] at result
    | ok values next =>
        simp only [argsResult] at result
        cases converted : requireNonempty values .typeExpr next with
        | invariant error => simp [converted] at result
        | reject failure rejected => simp [converted] at result
        | ok nonempty final =>
            simp only [converted] at result
            cases result
            have shape := (requireNonempty_success_iff_toList .typeExpr).mp converted
            rw [shape.2]
            exact delimited_success_context contextFrame .less .greater false .typeExpr .typeExpr argsResult
  · have absent := symbolAbsentAt_of_isSymbol_eq_false .less (Bool.eq_false_iff.mpr present)
    rw [parseNamedTypeArguments_eq_none_of_absent nested absent] at result
    cases result
    exact ⟨rfl, rfl⟩

theorem parseNamedTypeArguments_trace_success_iff
    (successSound : ParserTraceSuccessSound nested elementTrace)
    (successComplete : ParserTraceSuccessComplete nested elementTrace)
    (contextFrame : ParserSuccessContext nested)
    {input : State} {arguments : Option (NonemptyDelimitedList TypeExpr)}
    {after : DeclarativeGrammar.Remainder} {trace : List ParseDiagnostic} :
    DeclarativeGrammar.NamedTypeArgumentsTraceParses elementTrace input.file.id input.window.endByte
      input.declarativeRemainder arguments after trace ↔
    ∃ output, parseNamedTypeArguments nested input = .ok arguments output ∧
      output.declarativeRemainder = after ∧ output.diagnostics = input.diagnostics ++ trace := by
  constructor
  · exact parseNamedTypeArguments_trace_success_complete successComplete contextFrame
  · rintro ⟨output, result, afterEq, diagnostics⟩
    rcases parseNamedTypeArguments_trace_success_sound successSound contextFrame result with
      ⟨actualTrace, parsed, actualEq⟩
    have events := List.append_cancel_left (actualEq.symm.trans diagnostics)
    simpa only [afterEq, events] using parsed

end Solcore.Syntax.Parser
