import Solcore.Syntax.DeclarativeTypedParameterFinishingTraceProperties
import Solcore.Syntax.Parser.DiagnosticTraceContracts
import Solcore.Syntax.Parser.Parameter

/-! Exact execution of both parameter finishers on every state. The complete
AST and state are fixed; only the finishing events are appended. Previously
emitted type/name diagnostics remain prior events, never regenerated here. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.FunctionParameterInternals

open DeclarativeGrammar

theorem finishTypedParameter_eq_ok_of_trace (start : SourceSpan) (marker : Option SourceSpan)
    (name : Identifier) (type : TypeExpr) (input : State) {trace : List ParseDiagnostic}
    (events : TypedParameterFinishingTrace type trace) :
    finishTypedParameter start marker name type input =
      .ok (typedParameterTraceValue start marker name type)
        { input with diagnosticsRev := trace.reverse ++ input.diagnosticsRev } := by
  cases events with
  | ordinary allowed =>
      cases kind : type.value <;> simp only [ParameterTypeAllowed, kind] at allowed
      all_goals simp only [finishTypedParameter, kind, pure]; rfl
  | comptime forbidden =>
      cases kind : type.value <;> simp [ParameterTypeAllowed, kind] at forbidden
      simp only [finishTypedParameter, kind, emitDiagnostic, modifyState, bind, pure]
      rfl

theorem finishTypedParameter_success_trace_sound (start : SourceSpan) (marker : Option SourceSpan)
    (name : Identifier) (type : TypeExpr) {input output : State} {value : FunctionParameter}
    (result : finishTypedParameter start marker name type input = .ok value output) :
    ∃ trace, TypedParameterFinishingTrace type trace ∧ value = typedParameterTraceValue start marker name type ∧
      output = { input with diagnosticsRev := trace.reverse ++ input.diagnosticsRev } := by
  rcases typedParameterFinishingTrace_exists type with ⟨trace, events⟩
  have expected := finishTypedParameter_eq_ok_of_trace start marker name type input events
  rw [result] at expected
  exact ⟨trace, events, (Reply.ok.inj expected).1, (Reply.ok.inj expected).2⟩

theorem finishTypedParameter_success_context (start : SourceSpan) (marker : Option SourceSpan)
    (name : Identifier) (type : TypeExpr) : ParserSuccessContext (finishTypedParameter start marker name type) := by
  intro input output value result
  rcases finishTypedParameter_success_trace_sound start marker name type result with ⟨_, _, _, same⟩
  rw [same]
  exact ⟨rfl, rfl⟩

theorem finishTypedParameter_trace_success_iff (start : SourceSpan) (marker : Option SourceSpan)
    (name : Identifier) (type : TypeExpr) {input : State} {trace : List ParseDiagnostic} :
    TypedParameterFinishingTrace type trace ↔
      ∃ output, finishTypedParameter start marker name type input =
        .ok (typedParameterTraceValue start marker name type) output ∧
        output.declarativeRemainder = input.declarativeRemainder ∧
        output.diagnostics = input.diagnostics ++ trace := by
  constructor
  · intro events
    refine ⟨_, finishTypedParameter_eq_ok_of_trace start marker name type input events, rfl, ?_⟩
    simp only [State.diagnostics, List.reverse_append, List.reverse_reverse]
  · rintro ⟨output, result, _, diagnostics⟩
    rcases finishTypedParameter_success_trace_sound start marker name type result with ⟨actual, events, _, same⟩
    rw [same] at diagnostics
    simp only [State.diagnostics, List.reverse_append, List.reverse_reverse] at diagnostics
    have traceEq := List.append_cancel_left diagnostics
    simpa only [traceEq] using events

theorem finishTypedParameter_ne_reject (start : SourceSpan) (marker : Option SourceSpan)
    (name : Identifier) (type : TypeExpr) (input rejected : State) (failure : Failure) :
    finishTypedParameter start marker name type input ≠ .reject failure rejected := by
  rcases typedParameterFinishingTrace_exists type with ⟨trace, events⟩
  rw [finishTypedParameter_eq_ok_of_trace start marker name type input events]
  intro impossible
  contradiction

theorem finishTypedParameter_ne_invariant (start : SourceSpan) (marker : Option SourceSpan)
    (name : Identifier) (type : TypeExpr) (input : State) (error : ParserInvariantError) :
    finishTypedParameter start marker name type input ≠ .invariant error := by
  rcases typedParameterFinishingTrace_exists type with ⟨trace, events⟩
  rw [finishTypedParameter_eq_ok_of_trace start marker name type input events]
  intro impossible
  contradiction

theorem errorParameter_eq_ok_of_trace (span : SourceSpan) (constraint : ParseConstraint)
    (input : State) {trace : List ParseDiagnostic} (events : ErrorParameterFinishingTrace span constraint trace) :
    errorParameter span constraint input = .ok (errorParameterTraceValue span)
      { input with diagnosticsRev := trace.reverse ++ input.diagnosticsRev } := by
  cases events
  rfl

theorem errorParameter_success_trace_sound (span : SourceSpan) (constraint : ParseConstraint)
    {input output : State} {value : FunctionParameter} (result : errorParameter span constraint input = .ok value output) :
    ∃ trace, ErrorParameterFinishingTrace span constraint trace ∧ value = errorParameterTraceValue span ∧
      output = { input with diagnosticsRev := trace.reverse ++ input.diagnosticsRev } := by
  have expected := errorParameter_eq_ok_of_trace span constraint input .emitted
  rw [result] at expected
  exact ⟨_, .emitted, (Reply.ok.inj expected).1, (Reply.ok.inj expected).2⟩

theorem errorParameter_success_context (span : SourceSpan) (constraint : ParseConstraint) :
    ParserSuccessContext (errorParameter span constraint) := by
  intro input output value result
  rcases errorParameter_success_trace_sound span constraint result with ⟨_, _, _, same⟩
  rw [same]
  exact ⟨rfl, rfl⟩

theorem errorParameter_trace_success_iff (span : SourceSpan) (constraint : ParseConstraint)
    {input : State} {trace : List ParseDiagnostic} :
    ErrorParameterFinishingTrace span constraint trace ↔
      ∃ output, errorParameter span constraint input = .ok (errorParameterTraceValue span) output ∧
        output.declarativeRemainder = input.declarativeRemainder ∧
        output.diagnostics = input.diagnostics ++ trace := by
  constructor
  · intro events
    refine ⟨_, errorParameter_eq_ok_of_trace span constraint input events, rfl, ?_⟩
    simp only [State.diagnostics, List.reverse_append, List.reverse_reverse]
  · rintro ⟨output, result, _, diagnostics⟩
    rcases errorParameter_success_trace_sound span constraint result with ⟨actual, events, _, same⟩
    rw [same] at diagnostics
    simp only [State.diagnostics, List.reverse_append, List.reverse_reverse] at diagnostics
    have traceEq := List.append_cancel_left diagnostics
    simpa only [traceEq] using events

theorem errorParameter_ne_reject (span : SourceSpan) (constraint : ParseConstraint)
    (input rejected : State) (failure : Failure) : errorParameter span constraint input ≠ .reject failure rejected := by
  rw [errorParameter_eq_ok_of_trace span constraint input .emitted]
  intro impossible
  contradiction

theorem errorParameter_ne_invariant (span : SourceSpan) (constraint : ParseConstraint)
    (input : State) (error : ParserInvariantError) : errorParameter span constraint input ≠ .invariant error := by
  rw [errorParameter_eq_ok_of_trace span constraint input .emitted]
  intro impossible
  contradiction

end Solcore.Syntax.Parser.FunctionParameterInternals
