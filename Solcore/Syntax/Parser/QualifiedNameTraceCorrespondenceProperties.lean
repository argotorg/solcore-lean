import Solcore.Syntax.Parser.QualifiedNameTraceCompletenessProperties

/-! Exact AST, remainder, and prior-preserving traces, including arbitrary
tail accumulators and the concrete public parser's complete output state. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

namespace QualifiedNameInternals

theorem qualifiedNameTail_trace_success_iff
    (context : ParseContext) (phase : ParserPhase) (first last : Identifier)
    (fuel : Nat) (tailRev : List Identifier) {input : State}
    (adequate : input.remainingCount < fuel) {name : QualifiedName}
    {after : DeclarativeGrammar.Remainder} {trace : List ParseDiagnostic} :
    (∃ components,
      name = DeclarativeGrammar.qualifiedNameFromSuffix first last tailRev.reverse components ∧
      DeclarativeGrammar.DottedIdentifierTailTraceParses input.file.id input.window.endByte
        input.declarativeRemainder components after trace) ↔
    ∃ output, qualifiedNameTail context phase first fuel last tailRev input = .ok name output ∧
      output.declarativeRemainder = after ∧ output.diagnostics = input.diagnostics ++ trace := by
  constructor
  · rintro ⟨components, rfl, parsed⟩
    exact qualifiedNameTail_trace_success_complete context phase first last fuel tailRev parsed adequate
  · rintro ⟨output, result, afterEq, diagnostics⟩
    rcases qualifiedNameTail_success_trace_sound context phase first fuel last tailRev input name output result with
      ⟨components, actualTrace, valueEq, parsed, actualEq, _⟩
    have events := List.append_cancel_left (actualEq.symm.trans diagnostics)
    exact ⟨components, valueEq, by simpa only [afterEq, events] using parsed⟩

theorem qualifiedNameTail_production_trace_success_iff
    (context : ParseContext) (phase : ParserPhase) (first last : Identifier)
    (tailRev : List Identifier) {input : State} {name : QualifiedName}
    {after : DeclarativeGrammar.Remainder} {trace : List ParseDiagnostic} :
    (∃ components,
      name = DeclarativeGrammar.qualifiedNameFromSuffix first last tailRev.reverse components ∧
      DeclarativeGrammar.DottedIdentifierTailTraceParses input.file.id input.window.endByte
        input.declarativeRemainder components after trace) ↔
    ∃ output, qualifiedNameTail context phase first (input.remainingCount + 1) last tailRev input = .ok name output ∧
      output.declarativeRemainder = after ∧ output.diagnostics = input.diagnostics ++ trace :=
  qualifiedNameTail_trace_success_iff context phase first last (input.remainingCount + 1) tailRev (by omega)

end QualifiedNameInternals

theorem qualifiedName_trace_success_iff (context : ParseContext) (phase : ParserPhase)
    {input : State} {name : QualifiedName} {after : DeclarativeGrammar.Remainder}
    {trace : List ParseDiagnostic} :
    DeclarativeGrammar.QualifiedNameTraceParses input.file.id input.window.endByte
      input.declarativeRemainder name after trace ↔
    ∃ output, qualifiedName context phase input = .ok name output ∧
      output.declarativeRemainder = after ∧ output.diagnostics = input.diagnostics ++ trace := by
  constructor
  · exact qualifiedName_trace_success_complete context phase
  · rintro ⟨output, result, afterEq, diagnostics⟩
    rcases qualifiedName_trace_success_sound context phase result with ⟨actualTrace, parsed, actualEq⟩
    have events := List.append_cancel_left (actualEq.symm.trans diagnostics)
    simpa only [afterEq, events] using parsed

/-- Narrow exact traces strengthen ordinary AST/remainder laws to complete
state equality, without changing any generic ordinary-success contract. -/
theorem qualifiedName_success_state_eq_of_trace (context : ParseContext) (phase : ParserPhase)
    {input output : State} {name : QualifiedName} {after : DeclarativeGrammar.Remainder}
    {trace : List ParseDiagnostic}
    (result : qualifiedName context phase input = .ok name output)
    (parsed : DeclarativeGrammar.QualifiedNameTraceParses input.file.id input.window.endByte
      input.declarativeRemainder name after trace) :
    output = { input with
      cursor := after.cursor
      diagnosticsRev := trace.reverse ++ input.diagnosticsRev } := by
  rcases qualifiedName_trace_success_sound context phase result with ⟨actualTrace, actual, actualEq⟩
  have same := actual.result_unique parsed
  have tokensEq : output.tokens = input.tokens := actual.output_window.1
  have cursorEq : output.cursor = after.cursor := congrArg DeclarativeGrammar.Remainder.cursor same.2.1
  have frame := qualifiedName_success_context context phase result
  have events := congrArg List.reverse actualEq
  have diagnosticsEq : output.diagnosticsRev = trace.reverse ++ input.diagnosticsRev := by
    simpa only [same.2.2, State.diagnostics, List.reverse_append, List.reverse_reverse] using events
  cases input
  cases output
  simp_all only [State.declarativeRemainder]

theorem qualifiedName_eq_ok_of_trace (context : ParseContext) (phase : ParserPhase)
    {input : State} {name : QualifiedName} {after : DeclarativeGrammar.Remainder}
    {trace : List ParseDiagnostic}
    (parsed : DeclarativeGrammar.QualifiedNameTraceParses input.file.id input.window.endByte
      input.declarativeRemainder name after trace) :
    qualifiedName context phase input = .ok name { input with
      cursor := after.cursor
      diagnosticsRev := trace.reverse ++ input.diagnosticsRev } := by
  rcases qualifiedName_trace_success_complete context phase parsed with ⟨output, result, _, _⟩
  exact qualifiedName_success_state_eq_of_trace context phase result parsed ▸ result

end Solcore.Syntax.Parser
