import Solcore.Syntax.Parser.LambdaParameterTailTraceProperties

/-! Exact lambda-tail correspondence determines the whole Reply and State,
including complete uncommitted Failures and arbitrary prior diagnostics.
Retagging changes the AST carrier only, never the returned state or events. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.LambdaParameterInternals

open DeclarativeGrammar FunctionParameterInternals

theorem ordinaryLambdaParameterTail_trace_success_state_iff (name : Identifier)
    {input : State} {value : LambdaParameter} {after : Remainder} {trace : List ParseDiagnostic} :
    OrdinaryLambdaParameterTailTraceParses name input.file.id input.window.endByte
      input.declarativeRemainder value after trace ↔
      ordinaryLambdaParameterTail name input = .ok value (input.traceResult after trace) := by
  constructor
  · intro parsed
    cases parsed with
    | typed present tail =>
        simp only [ordinaryLambdaParameterTail_eq_of_present name present,
          namedParameterTail_eq_ok_of_trace name.span none name name.span tail]
    | inferred absent =>
        rw [ordinaryLambdaParameterTail_eq_of_absent name absent]
        rfl
  · intro result
    rcases ordinaryLambdaParameterTail_trace_success_sound name result with ⟨actual, parsed, events⟩
    rw [input.traceResult_diagnostics] at events
    have traceEq := List.append_cancel_left events
    simpa only [State.traceResult_declarativeRemainder, ← traceEq] using parsed

theorem ordinaryLambdaParameterTail_trace_reject_failure_state_iff (name : Identifier)
    {input : State} {failure : Failure} {after : Remainder} {trace : List ParseDiagnostic} :
    OrdinaryLambdaParameterTailTraceRejects name input.file.id input.window.endByte
      input.declarativeRemainder after failure.toDiagnostic trace ↔
      ordinaryLambdaParameterTail name input = .reject failure (input.traceResult after trace) := by
  constructor
  · intro rejection
    simp only [ordinaryLambdaParameterTail_eq_of_present name rejection.colon_present,
      namedParameterTail_eq_reject_of_trace name.span none name name.span rejection]
  · intro result
    rcases ordinaryLambdaParameterTail_reject_trace_sound name result with ⟨actual, rejection, events⟩
    rw [input.traceResult_diagnostics] at events
    have traceEq := List.append_cancel_left events
    simpa only [State.traceResult_declarativeRemainder, ← traceEq] using rejection

theorem ordinaryLambdaParameterTail_trace_reject_state_iff (name : Identifier)
    {input : State} {report : ParseDiagnostic} {after : Remainder} {trace : List ParseDiagnostic} :
    OrdinaryLambdaParameterTailTraceRejects name input.file.id input.window.endByte
      input.declarativeRemainder after report trace ↔
      ∃ failure, ordinaryLambdaParameterTail name input = .reject failure (input.traceResult after trace) ∧
        failure.toDiagnostic = report := by
  constructor
  · intro rejection
    rcases namedParameterTail_trace_reject_complete name.span none name name.span rejection with
      ⟨failure, _, _, _, reportEq, _⟩
    exact ⟨failure, (ordinaryLambdaParameterTail_trace_reject_failure_state_iff name).mp
      (reportEq.symm ▸ rejection), reportEq⟩
  · rintro ⟨failure, result, reportEq⟩
    exact reportEq ▸ (ordinaryLambdaParameterTail_trace_reject_failure_state_iff name).mpr result

theorem ordinaryLambdaParameterTail_trace_success_complete (name : Identifier) :
    ParserTraceSuccessComplete (ordinaryLambdaParameterTail name) (OrdinaryLambdaParameterTailTraceParses name) := by
  intro input value after trace parsed
  exact ⟨_, (ordinaryLambdaParameterTail_trace_success_state_iff name).mp parsed,
    input.traceResult_declarativeRemainder after trace, input.traceResult_diagnostics after trace⟩

theorem ordinaryLambdaParameterTail_trace_reject_complete (name : Identifier) :
    ParserTraceRejectComplete (ordinaryLambdaParameterTail name) (OrdinaryLambdaParameterTailTraceRejects name) := by
  intro input after report trace rejection
  rcases (ordinaryLambdaParameterTail_trace_reject_state_iff name).mp rejection with ⟨failure, result, reportEq⟩
  exact ⟨failure, _, result, input.traceResult_declarativeRemainder after trace, reportEq,
    input.traceResult_diagnostics after trace⟩

theorem ordinaryLambdaParameterTail_success_context (name : Identifier) :
    ParserSuccessContext (ordinaryLambdaParameterTail name) := by
  intro input output value result
  have window := ordinaryLambdaParameterTail_preservesTokenWindow name input
  rw [result] at window
  exact ⟨(ordinaryLambdaParameterTail_preservesFile name).file_eq_of_ok result, window.2⟩

theorem ordinaryLambdaParameterTail_reject_context (name : Identifier)
    {input rejected : State} {failure : Failure}
    (result : ordinaryLambdaParameterTail name input = .reject failure rejected) :
    rejected.file = input.file ∧ rejected.window = input.window := by
  have window := ordinaryLambdaParameterTail_preservesTokenWindow name input
  rw [result] at window
  exact ⟨(ordinaryLambdaParameterTail_preservesFile name).file_eq_of_reject result, window.2⟩

theorem ordinaryLambdaParameterTail_ne_invariant (name : Identifier) (input : State) (error : ParserInvariantError) :
    ordinaryLambdaParameterTail name input ≠ .invariant error :=
  (ordinaryLambdaParameterTail_ordinary name).ne_invariant input error

theorem comptimeLambdaParameterTail_trace_success_state_iff (marker : Token) (name : Identifier)
    {input : State} {value : LambdaParameter} {after : Remainder} {trace : List ParseDiagnostic} :
    ComptimeLambdaParameterTailTraceParses marker.span name input.file.id input.window.endByte
      input.declarativeRemainder value after trace ↔
      comptimeLambdaParameterTail marker name input = .ok value (input.traceResult after trace) := by
  constructor
  · intro parsed
    cases parsed with
    | typed present tail =>
        simp only [comptimeLambdaParameterTail_eq_of_present marker name present,
          namedParameterTail_eq_ok_of_trace marker.span (some marker.span) name
            (SourceSpan.cover marker.span name.span) tail]
    | typeMissing absent finished =>
        simp only [comptimeLambdaParameterTail_eq_of_absent marker name absent,
          errorParameter_eq_ok_of_trace (SourceSpan.cover marker.span name.span) .comptimeParameterRequiresType input finished]
        rfl
  · intro result
    rcases comptimeLambdaParameterTail_trace_success_sound marker name result with ⟨actual, parsed, events⟩
    rw [input.traceResult_diagnostics] at events
    have traceEq := List.append_cancel_left events
    simpa only [State.traceResult_declarativeRemainder, ← traceEq] using parsed

theorem comptimeLambdaParameterTail_trace_reject_failure_state_iff (marker : Token) (name : Identifier)
    {input : State} {failure : Failure} {after : Remainder} {trace : List ParseDiagnostic} :
    ComptimeLambdaParameterTailTraceRejects marker.span name input.file.id input.window.endByte
      input.declarativeRemainder after failure.toDiagnostic trace ↔
      comptimeLambdaParameterTail marker name input = .reject failure (input.traceResult after trace) := by
  constructor
  · intro rejection
    simp only [comptimeLambdaParameterTail_eq_of_present marker name rejection.colon_present,
      namedParameterTail_eq_reject_of_trace marker.span (some marker.span) name
        (SourceSpan.cover marker.span name.span) rejection]
  · intro result
    rcases comptimeLambdaParameterTail_reject_trace_sound marker name result with ⟨actual, rejection, events⟩
    rw [input.traceResult_diagnostics] at events
    have traceEq := List.append_cancel_left events
    simpa only [State.traceResult_declarativeRemainder, ← traceEq] using rejection

theorem comptimeLambdaParameterTail_trace_reject_state_iff (marker : Token) (name : Identifier)
    {input : State} {report : ParseDiagnostic} {after : Remainder} {trace : List ParseDiagnostic} :
    ComptimeLambdaParameterTailTraceRejects marker.span name input.file.id input.window.endByte
      input.declarativeRemainder after report trace ↔
      ∃ failure, comptimeLambdaParameterTail marker name input = .reject failure (input.traceResult after trace) ∧
        failure.toDiagnostic = report := by
  constructor
  · intro rejection
    rcases namedParameterTail_trace_reject_complete marker.span (some marker.span) name
        (SourceSpan.cover marker.span name.span) rejection with ⟨failure, _, _, _, reportEq, _⟩
    exact ⟨failure, (comptimeLambdaParameterTail_trace_reject_failure_state_iff marker name).mp
      (reportEq.symm ▸ rejection), reportEq⟩
  · rintro ⟨failure, result, reportEq⟩
    exact reportEq ▸ (comptimeLambdaParameterTail_trace_reject_failure_state_iff marker name).mpr result

theorem comptimeLambdaParameterTail_trace_success_complete (marker : Token) (name : Identifier) :
    ParserTraceSuccessComplete (comptimeLambdaParameterTail marker name)
      (ComptimeLambdaParameterTailTraceParses marker.span name) := by
  intro input value after trace parsed
  exact ⟨_, (comptimeLambdaParameterTail_trace_success_state_iff marker name).mp parsed,
    input.traceResult_declarativeRemainder after trace, input.traceResult_diagnostics after trace⟩

theorem comptimeLambdaParameterTail_trace_reject_complete (marker : Token) (name : Identifier) :
    ParserTraceRejectComplete (comptimeLambdaParameterTail marker name)
      (ComptimeLambdaParameterTailTraceRejects marker.span name) := by
  intro input after report trace rejection
  rcases (comptimeLambdaParameterTail_trace_reject_state_iff marker name).mp rejection with ⟨failure, result, reportEq⟩
  exact ⟨failure, _, result, input.traceResult_declarativeRemainder after trace, reportEq,
    input.traceResult_diagnostics after trace⟩

theorem comptimeLambdaParameterTail_success_context (marker : Token) (name : Identifier) :
    ParserSuccessContext (comptimeLambdaParameterTail marker name) := by
  intro input output value result
  have window := comptimeLambdaParameterTail_preservesTokenWindow marker name input
  rw [result] at window
  exact ⟨(comptimeLambdaParameterTail_preservesFile marker name).file_eq_of_ok result, window.2⟩

theorem comptimeLambdaParameterTail_reject_context (marker : Token) (name : Identifier)
    {input rejected : State} {failure : Failure}
    (result : comptimeLambdaParameterTail marker name input = .reject failure rejected) :
    rejected.file = input.file ∧ rejected.window = input.window := by
  have window := comptimeLambdaParameterTail_preservesTokenWindow marker name input
  rw [result] at window
  exact ⟨(comptimeLambdaParameterTail_preservesFile marker name).file_eq_of_reject result, window.2⟩

theorem comptimeLambdaParameterTail_ne_invariant (marker : Token) (name : Identifier)
    (input : State) (error : ParserInvariantError) : comptimeLambdaParameterTail marker name input ≠ .invariant error :=
  (comptimeLambdaParameterTail_ordinary marker name).ne_invariant input error

end Solcore.Syntax.Parser.LambdaParameterInternals
