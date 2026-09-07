import Solcore.Syntax.Parser.NamedParameterCoreTraceExistenceProperties
import Solcore.Test.SyntaxNamedParameterRawTraceProperties

/-! Selected-core consumers reconstruct whole replies from independent raw
components. All input states and prior events are arbitrary; neither child
execution contracts nor diagnostic-free premises are needed. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxNamedParameterCoreTraceProperties

open Syntax Syntax.Parser Syntax.Parser.FunctionParameterInternals
open Syntax.DeclarativeGrammar

private def stateFrom (source : SourceId) (endByte : Nat) (before : Remainder)
    (prior : List ParseDiagnostic) : State := {
  file := { id := source, content := "" }, tokens := before.tokens, cursor := before.cursor
  window := { endIndex := before.endIndex, endByte }, diagnosticsRev := prior.reverse
}

private theorem restore_ordinary_priority
    {source : SourceId} {endByte : Nat} {before after rejected : Remainder}
    {value : FunctionParameter} {trace : List ParseDiagnostic} {failure : Failure}
    (prior : List ParseDiagnostic)
    (absent : ComptimeParameterPrefixAbsentAt before)
    (ordinary : OrdinaryNamedParameterTraceParses source endByte before value after trace)
    (rawRejected : ComptimeNamedParameterTraceRejects source endByte before rejected failure.toDiagnostic []) :
    namedParameterCore (stateFrom source endByte before prior) =
      .ok value ((stateFrom source endByte before prior).traceResult after trace) ∧
    comptimeNamedParameter (stateFrom source endByte before prior) =
      .reject failure ((stateFrom source endByte before prior).traceResult rejected []) ∧
    ¬ ∃ rejected report events, NamedParameterCoreTraceRejects source endByte before rejected report events := by
  have selected := NamedParameterCoreTraceParses.ordinary absent ordinary
  refine ⟨namedParameterCore_trace_success_state_iff.mp selected,
    comptimeNamedParameter_trace_reject_failure_state_iff.mp rawRejected, ?_⟩
  rintro ⟨_, _, _, rejection⟩
  exact rejection.disjoint_success ⟨_, _, _, selected⟩

/-- Reuse the independently constructed `comptime;` fixture. Its ordinary
error-valued success wins; the raw comptime identifier failure is not a selected
failure. Existing events, including duplicates of either constraint, stay first. -/
theorem bare_comptime_selects_success_not_raw_early_failure (prior : List ParseDiagnostic) :
    ∃ (input : State) (value : FunctionParameter) (after : Remainder)
      (trace : List ParseDiagnostic) (failure : Failure) (rejected : Remainder),
      input.diagnostics = prior ∧
      namedParameterCore input = .ok value (input.traceResult after trace) ∧
      comptimeNamedParameter input = .reject failure (input.traceResult rejected []) ∧
      (¬ ∃ after report events, NamedParameterCoreTraceRejects input.file.id input.window.endByte
        input.declarativeRemainder after report events) ∧
      value.value = .error ∧
      trace.map (·.kind) = [.constraintViolation .comptimeUsedAsParameterName,
        .constraintViolation .namedParameterRequiresType] ∧
      failure.expected = { head := .identifier, tail := [] } ∧ failure.context = .parameter ∧
      failure.found = some (.symbol .semicolon) ∧
      (input.traceResult after trace).diagnostics = prior ++ trace ∧
      (input.traceResult rejected []).diagnostics = prior ∧
      (input.traceResult after trace).peek?.map (·.value) = some (.symbol .semicolon) := by
  have witnesses := SyntaxNamedParameterRawTraceProperties.bare_comptime_raw_traces
  have replies := restore_ordinary_priority prior witnesses.2.2 witnesses.1 witnesses.2.1
  refine ⟨_, _, _, _, _, _, ?_, replies.1, replies.2.1, replies.2.2,
    rfl, rfl, rfl, rfl, rfl, ?_, ?_, rfl⟩
  · simp only [stateFrom, State.diagnostics, List.reverse_reverse]
  · rw [State.traceResult_diagnostics]
    simp only [stateFrom, State.diagnostics, List.reverse_reverse]
  · rw [State.traceResult_diagnostics]
    simp only [stateFrom, State.diagnostics, List.reverse_reverse, List.append_nil]

/-- Checked-name events precede type events, which precede finishing events.
The exact covering AST and every remainder field are restored together. -/
theorem ordinary_typed_components_restore_selected_reply
    {input : State} {afterName afterColon output : Remainder}
    {name : Identifier} {type : TypeExpr} {colonSpan : SourceSpan}
    {nameEvents typeEvents finishingEvents : List ParseDiagnostic}
    (absent : ComptimeParameterPrefixAbsentAt input.declarativeRemainder)
    (nameParsed : CheckedParameterNameTraceParses input.declarativeRemainder name afterName nameEvents)
    (colon : ExactTokenParses (.symbol .colon) afterName colonSpan afterColon)
    (typeParsed : TypeExprTraceParses input.file.id input.window.endByte afterColon type output typeEvents)
    (finished : TypedParameterFinishingTrace type finishingEvents) :
    namedParameterCore input = .ok (typedParameterTraceValue name.span none name type)
      (input.traceResult output (nameEvents ++ typeEvents ++ finishingEvents)) ∧
    (input.traceResult output (nameEvents ++ typeEvents ++ finishingEvents)).diagnostics =
      input.diagnostics ++ nameEvents ++ typeEvents ++ finishingEvents := by
  constructor
  · apply namedParameterCore_trace_success_state_iff.mp
    simpa only [List.append_assoc] using NamedParameterCoreTraceParses.ordinary absent
      (OrdinaryNamedParameterTraceParses.parsed nameParsed
        (.typed colonSpan colon typeParsed finished))
  · simp only [State.traceResult_diagnostics, List.append_assoc]

/-- A selected marker is silent. Even when the following name spells
`comptime`, only its identifier trace is used, without ordinary-name finishing. -/
theorem comptime_typed_components_restore_selected_reply
    {input : State} {afterMarker afterName afterColon output : Remainder}
    {markerSpan colonSpan : SourceSpan} {name : Identifier} {type : TypeExpr}
    {nameEvents typeEvents finishingEvents : List ParseDiagnostic}
    (present : ComptimeLambdaParameterStartsAt input.declarativeRemainder)
    (marker : ExactTokenParses (.identifier ContextualKeyword.comptime.spelling)
      input.declarativeRemainder markerSpan afterMarker)
    (nameParsed : IdentifierTraceParses afterMarker name afterName nameEvents)
    (colon : ExactTokenParses (.symbol .colon) afterName colonSpan afterColon)
    (typeParsed : TypeExprTraceParses input.file.id input.window.endByte afterColon type output typeEvents)
    (finished : TypedParameterFinishingTrace type finishingEvents) :
    namedParameterCore input = .ok (typedParameterTraceValue markerSpan (some markerSpan) name type)
      (input.traceResult output (nameEvents ++ typeEvents ++ finishingEvents)) := by
  apply namedParameterCore_trace_success_state_iff.mp
  simpa only [List.append_assoc] using NamedParameterCoreTraceParses.comptime present
    (ComptimeNamedParameterTraceParses.parsed markerSpan marker nameParsed
      (.typed colonSpan colon typeParsed finished))

/-- A failed type contributes its complete Failure and its own trace only:
no typed-parameter finishing event or committed terminal report is added. -/
theorem comptime_type_rejection_restores_selected_full_failure
    {input : State} {afterMarker afterName afterColon rejected : Remainder}
    {markerSpan colonSpan : SourceSpan} {name : Identifier} {failure : Failure}
    {nameEvents typeEvents : List ParseDiagnostic}
    (present : ComptimeLambdaParameterStartsAt input.declarativeRemainder)
    (marker : ExactTokenParses (.identifier ContextualKeyword.comptime.spelling)
      input.declarativeRemainder markerSpan afterMarker)
    (nameParsed : IdentifierTraceParses afterMarker name afterName nameEvents)
    (colon : ExactTokenParses (.symbol .colon) afterName colonSpan afterColon)
    (typeRejected : TypeExprTraceRejects input.file.id input.window.endByte afterColon
      rejected failure.toDiagnostic typeEvents) :
    namedParameterCore input = .reject failure (input.traceResult rejected (nameEvents ++ typeEvents)) ∧
    (input.traceResult rejected (nameEvents ++ typeEvents)).diagnostics =
      input.diagnostics ++ nameEvents ++ typeEvents := by
  constructor
  · exact namedParameterCore_trace_reject_failure_state_iff.mp (.comptime present
      (.tailRejected markerSpan marker nameParsed (.typeRejected colonSpan colon typeRejected)))
  · simp only [State.traceResult_diagnostics, List.append_assoc]

/-- Ordinary execution supplies existence, independently of joint uniqueness.
Every arbitrary State has a protected exact suffix and a reconstructed reply. -/
theorem every_state_has_a_protected_exact_core_reply (input : State) (lexical : List SourceSpan) :
    ∃ trace, ParseDiagnosticCascadeFilters input.file.content lexical trace trace ∧
      ((∃ value after,
        namedParameterCore input = .ok value (input.traceResult after trace) ∧
        NamedParameterCoreTraceParses input.file.id input.window.endByte
          input.declarativeRemainder value after trace) ∨
       (∃ failure after,
        namedParameterCore input = .reject failure (input.traceResult after trace) ∧
        NamedParameterCoreTraceRejects input.file.id input.window.endByte
          input.declarativeRemainder after failure.toDiagnostic trace)) := by
  rcases namedParameterCore_exists_trace_outcome input with
    ⟨value, output, trace, _, parsed, _⟩ | ⟨failure, rejected, trace, _, rejection, _⟩
  · exact ⟨trace, parsed.cascadeFilters _ _, .inl
      ⟨value, output.declarativeRemainder, namedParameterCore_trace_success_state_iff.mp parsed, parsed⟩⟩
  · exact ⟨trace, rejection.cascadeFilters _ _, .inr
      ⟨failure, rejected.declarativeRemainder, namedParameterCore_trace_reject_failure_state_iff.mp rejection, rejection⟩⟩

end Solcore.Test.SyntaxNamedParameterCoreTraceProperties
