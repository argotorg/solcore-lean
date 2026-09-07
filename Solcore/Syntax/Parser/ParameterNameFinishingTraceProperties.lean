import Solcore.Syntax.DeclarativeParameterNameFinishingTraceProperties
import Solcore.Syntax.Parser.IdentifierTraceProperties
import Solcore.Syntax.Parser.SourceFrameProperties
import Solcore.Syntax.Parser.DiagnosticTraceStateProperties

/-! Exact state bridges for the inline ordinary-name check shared by named
and lambda parameters. No executable helper is introduced. A continuation law
retains every result, including the complete Failure and State on rejection.
The checked prefix is not the pair-selected parameter core or public recovery. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

open DeclarativeGrammar

theorem parameterNameFinishing_eq_ok_of_trace (name : Identifier) (input : State)
    {trace : List ParseDiagnostic} (events : ParameterNameFinishingTrace name trace) :
    (if name.value == ContextualKeyword.comptime.spelling then
      emitDiagnostic { span := name.span, kind := .constraintViolation .comptimeUsedAsParameterName }
    else pure ()) input = .ok () { input with diagnosticsRev := trace.reverse ++ input.diagnosticsRev } := by
  cases events with
  | ordinary spelling => simp only [beq_eq_false_iff_ne.mpr spelling, Bool.false_eq_true, if_false]; rfl
  | comptime spelling => simp only [spelling, beq_self_eq_true, if_true]; rfl

theorem parameterNameFinishing_success_trace_sound (name : Identifier)
    {input output : State} {value : Unit}
    (result : (if name.value == ContextualKeyword.comptime.spelling then
      emitDiagnostic { span := name.span, kind := .constraintViolation .comptimeUsedAsParameterName }
      else pure ()) input = .ok value output) :
    ∃ trace, ParameterNameFinishingTrace name trace ∧ value = () ∧
      output = { input with diagnosticsRev := trace.reverse ++ input.diagnosticsRev } := by
  rcases parameterNameFinishingTrace_exists name with ⟨trace, events⟩
  have expected := parameterNameFinishing_eq_ok_of_trace name input events
  rw [result] at expected
  exact ⟨trace, events, (Reply.ok.inj expected).1, (Reply.ok.inj expected).2⟩

theorem parameterNameFinishing_trace_success_state_iff (name : Identifier) (input : State)
    {trace : List ParseDiagnostic} :
    ParameterNameFinishingTrace name trace ↔
    (if name.value == ContextualKeyword.comptime.spelling then
      emitDiagnostic { span := name.span, kind := .constraintViolation .comptimeUsedAsParameterName }
    else pure ()) input = .ok () { input with diagnosticsRev := trace.reverse ++ input.diagnosticsRev } := by
  constructor
  · exact parameterNameFinishing_eq_ok_of_trace name input
  · intro result
    rcases parameterNameFinishing_success_trace_sound name result with ⟨actual, events, _, stateEq⟩
    have reversed := congrArg State.diagnosticsRev stateEq
    have same := List.append_cancel_right reversed
    have sameTrace := congrArg List.reverse same
    simp only [List.reverse_reverse] at sameTrace
    exact sameTrace ▸ events

/-- The original inline conditional can be followed by any parser. The check
changes only the reverse event accumulator and never commits a Failure. -/
theorem parameterNameFinishing_continue_of_trace {α : Type} (name : Identifier)
    (next : Parser α) (input : State) {trace : List ParseDiagnostic}
    (events : ParameterNameFinishingTrace name trace) :
    (if name.value == ContextualKeyword.comptime.spelling then
      emitDiagnostic { span := name.span, kind := .constraintViolation .comptimeUsedAsParameterName } >>= fun _ => next
    else next) input = next { input with diagnosticsRev := trace.reverse ++ input.diagnosticsRev } := by
  cases events with
  | ordinary spelling => simp only [beq_eq_false_iff_ne.mpr spelling, Bool.false_eq_true, if_false]; rfl
  | comptime spelling => simp only [spelling, beq_self_eq_true, if_true]; rfl

/-- Combine the real checked identifier with the subsequent inline spelling
check. Identifier events precede finishing events for every incoming State;
the continuation result itself is neither inspected nor weakened. -/
theorem checkedParameterName_continue_of_trace {α : Type} (next : Identifier → Parser α)
    {input : State} {name : Identifier} {after : Remainder} {trace : List ParseDiagnostic}
    (parsed : CheckedParameterNameTraceParses input.declarativeRemainder name after trace) :
    (identifier .parameter >>= fun found =>
      if found.value == ContextualKeyword.comptime.spelling then
        emitDiagnostic { span := found.span, kind := .constraintViolation .comptimeUsedAsParameterName } >>=
          fun _ => next found
      else next found) input = next name (input.traceResult after trace) := by
  cases parsed with
  | parsed identifierTrace finishingTrace =>
      rcases (identifier_trace_success_iff .parameter).mp identifierTrace with
        ⟨afterName, nameResult, remainderEq, nameEvents⟩
      have window := identifier_preservesTokenWindow .parameter input
      rw [nameResult] at window
      have nameState := State.eq_traceResult_of_fields
        ((identifier_preservesFile .parameter).file_eq_of_ok nameResult)
        (congrArg TokenWindow.endByte window.2) remainderEq nameEvents
      have finished := parameterNameFinishing_continue_of_trace name (next name) afterName finishingTrace
      simp only [bind] at finished
      simp only [bind, nameResult]
      rw [finished, nameState]
      simp only [State.traceResult, List.reverse_append, List.append_assoc]

end Solcore.Syntax.Parser
