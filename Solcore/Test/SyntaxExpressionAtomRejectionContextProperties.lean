import Solcore.Syntax.Parser.ExpressionAtomDispatchRejectionContextProperties
import Solcore.Syntax.Parser.ExpressionAtomDispatchTraceCorrespondenceProperties
import Solcore.Syntax.Parser.ExpressionAtomTraceStateProperties

/-! A synthetic rejected expression replaces both tokens and endIndex while
keeping its file/endByte. Actual parenthesized atom dispatch and public rewind
retain that failed carrier, so a new boundary replaces the original nonboundary.
The unused block deliberately returns an invariant; no child totality is used. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxExpressionAtomRejectionContextProperties

open Solcore.Syntax Solcore.Syntax.Parser Solcore.Syntax.DeclarativeGrammar
open Solcore.Syntax.Parser.ExpressionAtomInternals

private def source : SourceId := { origin := .main, path := "atom-rejection-context.sol" }
private def span (startByte endByte : Nat) : SourceSpan := { source, startByte, endByte }
private def token (value : TokenKind) : Token := { span := span 0 1, value }
private def original : List Token := [token (.symbol .leftParen), token (.identifier "x")]
private def changed : List Token := [token (.symbol .semicolon)]
private def before : Remainder := { tokens := original.toArray, cursor := 0, endIndex := 2 }
private def failed : Remainder := { tokens := changed.toArray, cursor := 3, endIndex := 1 }
private def input (prior : List ParseDiagnostic) : State := {
  file := { id := source, content := "" }, tokens := original.toArray, cursor := 0
  window := { endIndex := 2, endByte := 99 }, diagnosticsRev := prior.reverse
}
private def event : ParseDiagnostic := { span := span 1 4, kind := .invalidIdentifierHyphen "a-b" }
private def failure : Failure := {
  span := span 1 4, found := some (.symbol .plus)
  expected := { head := .expression, tail := [] }, context := .expression
}
private def replaceOnReject (state : State) : State := {
  state with
  tokens := changed.toArray
  cursor := 3
  window := { endIndex := 1, endByte := state.window.endByte }
  diagnosticsRev := event :: state.diagnosticsRev
}
private def nested : Parser Expr := fun state => .reject failure (replaceOnReject state)
private def unusedBlock : Parser Block := fun state => .invariant (.fuelExhausted .expression state.currentSpan)
private def childSuccess (_ : SourceId) (_ : Nat) (_ : Remainder) (_ : Expr)
    (_ : Remainder) (_ : List ParseDiagnostic) : Prop := False
private def childRejects (_ : SourceId) (_ : Nat) (_ : Remainder) (after : Remainder)
    (report : ParseDiagnostic) (trace : List ParseDiagnostic) : Prop :=
  after = failed ∧ report = failure.toDiagnostic ∧ trace = [event]
private def blockRejects (_ : SourceId) (_ : Nat) (_ _ : Remainder)
    (_ : ParseDiagnostic) (_ : List ParseDiagnostic) : Prop := False
private abbrev coreRejects := ExpressionAtomDispatchTraceRejects childSuccess childRejects blockRejects
private def rejectedState (prior : List ParseDiagnostic) : State := {
  input prior with
  tokens := changed.toArray
  cursor := 3
  window := { endIndex := 1, endByte := 99 }
  diagnosticsRev := event :: prior.reverse
}

private theorem nested_success_sound : ParserTraceSuccessSound nested childSuccess := by
  intro state output value result
  simp [nested] at result
private theorem nested_success_complete : ParserTraceSuccessComplete nested childSuccess := by
  intro state value after trace impossible
  exact False.elim impossible
private theorem nested_success_context : ParserSuccessContext nested := by
  intro state output value result
  simp [nested] at result
private theorem nested_reject_sound : ParserTraceRejectSound nested childRejects := by
  intro state output actual result
  change Reply.reject failure (replaceOnReject state) = Reply.reject actual output at result
  cases result
  refine ⟨[event], ⟨rfl, rfl, rfl⟩, ?_⟩
  simp only [replaceOnReject, State.diagnostics, List.reverse_cons]
private theorem nested_reject_complete : ParserTraceRejectComplete nested childRejects := by
  rintro state after report trace ⟨rfl, rfl, rfl⟩
  refine ⟨failure, replaceOnReject state, rfl, rfl, rfl, ?_⟩
  simp only [replaceOnReject, State.diagnostics, List.reverse_cons]
private theorem nested_reject_frame {state output : State} {actual : Failure}
    (result : nested state = .reject actual output) :
    output.file = state.file ∧ output.window.endByte = state.window.endByte := by
  change Reply.reject failure (replaceOnReject state) = Reply.reject actual output at result
  cases result
  exact ⟨rfl, rfl⟩
private theorem block_reject_sound : ParserTraceRejectSound unusedBlock blockRejects := by
  intro state output actual result
  simp [unusedBlock] at result
private theorem block_reject_complete : ParserTraceRejectComplete unusedBlock blockRejects := by
  intro state after report trace impossible
  exact False.elim impossible
private theorem block_reject_frame {state output : State} {actual : Failure}
    (result : unusedBlock state = .reject actual output) :
    output.file = state.file ∧ output.window.endByte = state.window.endByte := by
  simp [unusedBlock] at result

private theorem core_reject_frame {state output : State} {actual : Failure}
    (result : expressionAtomCore nested unusedBlock state = .reject actual output) :
    output.file = state.file ∧ output.window.endByte = state.window.endByte :=
  expressionAtomCore_reject_source_endByte nested_success_context nested_reject_frame block_reject_frame result
private theorem core_reject_sound : ParserTraceRejectSound (expressionAtomCore nested unusedBlock) coreRejects :=
  expressionAtomCore_reject_trace_sound nested_success_sound nested_reject_sound nested_success_context block_reject_sound
private theorem core_reject_complete : ParserTraceRejectComplete (expressionAtomCore nested unusedBlock) coreRejects :=
  expressionAtomCore_trace_reject_complete nested_success_complete nested_reject_complete
    nested_success_context block_reject_complete

private theorem selected_parenthesis : ExpressionAtomDispatchSelects before .parenthesized := by
  constructor <;> simp [CoreLiteralStartsAt, ExpressionNameStartsAt, TokenKindAbsentAt, TokenAt, before, original, token]

theorem independent_core_rejection : coreRejects source 99 before failed failure.toDiagnostic [event] :=
  .selected .parenthesized selected_parenthesis
    (.firstRejected (span 0 1) ⟨⟨by change 0 < 2; decide, rfl⟩, rfl⟩
      (by simp [TokenKindAbsentAt, TokenAt, before, original, token]) ⟨rfl, rfl, rfl⟩)

/-- The same complete child Failure and event escape; only file/endByte are
framed. The independent remainder supplies every replaced state field. -/
theorem core_reply_from_independent_trace (prior : List ParseDiagnostic) :
    expressionAtomCore nested unusedBlock (input prior) = .reject failure (rejectedState prior) :=
  (expressionAtomCore_trace_reject_failure_state_iff nested_success_sound nested_reject_sound
    nested_success_complete nested_reject_complete nested_success_context block_reject_sound block_reject_complete
    core_reject_frame (input := input prior)).mp independent_core_rejection

theorem weak_frame_allows_new_carrier_and_endIndex (prior : List ParseDiagnostic) :
    (rejectedState prior).file = (input prior).file ∧
    (rejectedState prior).window.endByte = (input prior).window.endByte ∧
    (rejectedState prior).tokens ≠ (input prior).tokens ∧
    (rejectedState prior).window.endIndex ≠ (input prior).window.endIndex ∧
    (rejectedState prior).cursor = 3 := by
  have frame := core_reject_frame (core_reply_from_independent_trace prior)
  exact ⟨frame.1, frame.2, by change changed.toArray ≠ original.toArray; decide, by change 1 ≠ 2; decide, rfl⟩

theorem rewind_changes_boundary_observation :
    ¬ ExpressionAtomBoundaryStops before ∧
    ExpressionAtomBoundaryStops (expressionAtomTraceRewind before failed) ∧
    (expressionAtomTraceRewind before failed).tokens = failed.tokens ∧
    (expressionAtomTraceRewind before failed).endIndex = 1 ∧
    (expressionAtomTraceRewind before failed).cursor = before.cursor := by
  refine ⟨?_, .semicolon ⟨by change 0 < 1; decide, rfl⟩, rfl, rfl, rfl⟩
  intro stops
  cases stops <;> simp_all [TokenAt, before, original, token]

theorem independent_public_boundary_rejection :
    ExpressionAtomTraceRejects coreRejects source 99 before
      (expressionAtomTraceRewind before failed) failure.toDiagnostic [event] :=
  .boundary independent_core_rejection rewind_changes_boundary_observation.2.1

/-- Public recovery is bypassed using the changed carrier, not the original
opening parenthesis. The original report stays terminal and uncommitted. -/
theorem public_reply_keeps_failed_carrier (prior : List ParseDiagnostic) :
    expressionAtom nested unusedBlock (input prior) =
      .reject failure { rejectedState prior with cursor := 0 } ∧
    ({ rejectedState prior with cursor := 0 } : State).diagnostics = prior ++ [event] ∧
    isAtomBoundary (input prior) = false ∧
    isAtomBoundary { rejectedState prior with cursor := 0 } = true := by
  refine ⟨(expressionAtom_trace_reject_failure_state_iff core_reject_sound core_reject_complete
    core_reject_frame (input := input prior)).mp independent_public_boundary_rejection, ?_, rfl, rfl⟩
  simp only [rejectedState, State.diagnostics, List.reverse_cons, List.reverse_reverse]

theorem prior_duplicate_event_is_not_replayed (prior : List ParseDiagnostic) :
    expressionAtom nested unusedBlock (input (prior ++ [event])) =
      .reject failure { rejectedState (prior ++ [event]) with cursor := 0 } ∧
    ({ rejectedState (prior ++ [event]) with cursor := 0 } : State).diagnostics = prior ++ [event, event] := by
  have result := public_reply_keeps_failed_carrier (prior ++ [event])
  exact ⟨result.1, by simpa only [List.append_assoc, List.cons_append, List.nil_append] using result.2.1⟩

end Solcore.Test.SyntaxExpressionAtomRejectionContextProperties
