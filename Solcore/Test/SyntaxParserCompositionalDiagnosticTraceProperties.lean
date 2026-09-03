import Solcore.Syntax.Parser.TransactionalChoiceDiagnosticTraceProperties

/-! Executable combinator consumers. Nonempty earlier and rejected-branch
diagnostics make retention versus transactional rollback observable. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserCompositionalDiagnosticTraceProperties

open Solcore.Syntax
open Solcore.Syntax.Parser

example := @emitDiagnostic_success_trace
example := @bind_success_trace
example := @bind_reject_right_trace
example := @bind_reject_left_trace
example := @map_success_trace
example := @map_reject_trace
example := @bind_invariant_left_exact
example := @orElse_eq_right_of_reject
example := @orElse_success_left_trace
example := @orElse_success_right_trace
example := @orElse_reject_right_trace
example := @orElse_invariant_left_exact
example := @orElse_invariant_right_exact

private def emitValue (diagnostic : ParseDiagnostic) (value : Nat) : Parser Nat := do
  emitDiagnostic diagnostic
  pure value

private def emitReject (diagnostic : ParseDiagnostic) (failure : Failure) : Parser Nat := do
  emitDiagnostic diagnostic
  fun state => .reject failure state

private theorem emit_nonempty (input : State) (diagnostic : ParseDiagnostic) :
    (input.emit diagnostic).diagnostics ≠ [] := by
  simp [State.emit, State.diagnostics]

/-- Sequencing preserves a nonempty prior prefix and both new events in order. -/
theorem sequencing_success_order (input : State)
    (prior firstEvent nextEvent : ParseDiagnostic) :
    ((emitValue firstEvent 3) >>= fun _ => emitValue nextEvent 7) (input.emit prior) =
      .ok 7 (((input.emit prior).emit firstEvent).emit nextEvent) ∧
      (((input.emit prior).emit firstEvent).emit nextEvent).diagnostics =
        input.diagnostics ++ [prior, firstEvent, nextEvent] := by
  have result := bind_success_trace
    (first := emitValue firstEvent 3) (next := fun _ => emitValue nextEvent 7)
    (input := input.emit prior) rfl
    (emitDiagnostic_success_trace firstEvent (input.emit prior)).2 rfl
    (emitDiagnostic_success_trace nextEvent ((input.emit prior).emit firstEvent)).2
  refine ⟨result.1, ?_⟩
  simpa only [(emitDiagnostic_success_trace prior input).2, List.append_assoc,
    List.singleton_append] using result.2

/-- A later ordinary rejection does not roll back the earlier successful event. -/
theorem sequencing_reject_retains_both (input : State)
    (prior firstEvent nextEvent : ParseDiagnostic) (failure : Failure) :
    ((emitValue firstEvent 3) >>= fun _ => emitReject nextEvent failure) (input.emit prior) =
      .reject failure (((input.emit prior).emit firstEvent).emit nextEvent) ∧
      (((input.emit prior).emit firstEvent).emit nextEvent).diagnostics =
        input.diagnostics ++ [prior, firstEvent, nextEvent] := by
  have result := bind_reject_right_trace
    (first := emitValue firstEvent 3) (next := fun _ => emitReject nextEvent failure)
    (input := input.emit prior) rfl
    (emitDiagnostic_success_trace firstEvent (input.emit prior)).2 rfl
    (emitDiagnostic_success_trace nextEvent ((input.emit prior).emit firstEvent)).2
  refine ⟨result.1, ?_⟩
  simpa only [(emitDiagnostic_success_trace prior input).2, List.append_assoc,
    List.singleton_append] using result.2

/-- First-stage rejection never runs an arbitrary continuation. -/
theorem sequencing_first_reject_stops (input : State)
    (prior event : ParseDiagnostic) (failure : Failure) (next : Nat → Parser Nat) :
    (emitReject event failure >>= next) (input.emit prior) =
      .reject failure ((input.emit prior).emit event) ∧
      ((input.emit prior).emit event).diagnostics = input.diagnostics ++ [prior, event] := by
  have result := bind_reject_left_trace next
    (first := emitReject event failure) (input := input.emit prior) rfl
    (emitDiagnostic_success_trace event (input.emit prior)).2
  refine ⟨result.1, ?_⟩
  simpa only [(emitDiagnostic_success_trace prior input).2, List.append_assoc,
    List.singleton_append] using result.2

/-- Mapping the returned value cannot reorder or remove the diagnostic event. -/
theorem mapping_success_preserves_trace (input : State)
    (prior event : ParseDiagnostic) :
    (Nat.succ <$> emitValue event 7) (input.emit prior) =
      .ok 8 ((input.emit prior).emit event) ∧
      ((input.emit prior).emit event).diagnostics = input.diagnostics ++ [prior, event] := by
  have result := map_success_trace Nat.succ
    (parser := emitValue event 7) (input := input.emit prior) rfl
    (emitDiagnostic_success_trace event (input.emit prior)).2
  refine ⟨result.1, ?_⟩
  simpa only [(emitDiagnostic_success_trace prior input).2, List.append_assoc,
    List.singleton_append] using result.2

/-- Mapping also preserves a rejected payload and its nonempty raw trace. -/
theorem mapping_reject_preserves_trace (input : State)
    (prior event : ParseDiagnostic) (failure : Failure) :
    (Nat.succ <$> emitReject event failure) (input.emit prior) =
      .reject failure ((input.emit prior).emit event) ∧
      ((input.emit prior).emit event).diagnostics = input.diagnostics ++ [prior, event] := by
  have result := map_reject_trace Nat.succ
    (parser := emitReject event failure) (input := input.emit prior) rfl
    (emitDiagnostic_success_trace event (input.emit prior)).2
  refine ⟨result.1, ?_⟩
  simpa only [(emitDiagnostic_success_trace prior input).2, List.append_assoc,
    List.singleton_append] using result.2

/-- Both the original and failed-left diagnostic sequences are nonempty.
Fallback discards the left event but retains the prior prefix and right event. -/
theorem choice_nonempty_rollback_success (input : State)
    (prior leftEvent rightEvent : ParseDiagnostic) (failure : Failure) :
    (input.emit prior).diagnostics ≠ [] ∧
      ((input.emit prior).emit leftEvent).diagnostics ≠ [] ∧
      orElse (emitReject leftEvent failure) (emitValue rightEvent 7) (input.emit prior) =
        .ok 7 ((input.emit prior).emit rightEvent) ∧
      ((input.emit prior).emit rightEvent).diagnostics =
        input.diagnostics ++ [prior, rightEvent] := by
  have result := orElse_success_right_trace
    (first := emitReject leftEvent failure) (second := emitValue rightEvent 7)
    (input := input.emit prior) rfl rfl
    (emitDiagnostic_success_trace rightEvent (input.emit prior)).2
  refine ⟨emit_nonempty input prior, emit_nonempty (input.emit prior) leftEvent, result.1, ?_⟩
  simpa only [(emitDiagnostic_success_trace prior input).2, List.append_assoc,
    List.singleton_append] using result.2

/-- Even when both alternatives reject after emitting, only the right failure
and its event survive; the original nonempty diagnostic prefix is retained. -/
theorem choice_nonempty_rollback_reject (input : State)
    (prior leftEvent rightEvent : ParseDiagnostic) (leftFailure rightFailure : Failure) :
    (input.emit prior).diagnostics ≠ [] ∧
      ((input.emit prior).emit leftEvent).diagnostics ≠ [] ∧
      orElse (emitReject leftEvent leftFailure) (emitReject rightEvent rightFailure)
        (input.emit prior) = .reject rightFailure ((input.emit prior).emit rightEvent) ∧
      ((input.emit prior).emit rightEvent).diagnostics =
        input.diagnostics ++ [prior, rightEvent] := by
  have result := orElse_reject_right_trace
    (first := emitReject leftEvent leftFailure) (second := emitReject rightEvent rightFailure)
    (input := input.emit prior) rfl rfl
    (emitDiagnostic_success_trace rightEvent (input.emit prior)).2
  refine ⟨emit_nonempty input prior, emit_nonempty (input.emit prior) leftEvent, result.1, ?_⟩
  simpa only [(emitDiagnostic_success_trace prior input).2, List.append_assoc,
    List.singleton_append] using result.2

/-- A successful left branch retains its own event and ignores any right parser. -/
theorem choice_left_success_keeps_trace (input : State)
    (prior event : ParseDiagnostic) (second : Parser Nat) :
    orElse (emitValue event 3) second (input.emit prior) =
      .ok 3 ((input.emit prior).emit event) ∧
      ((input.emit prior).emit event).diagnostics = input.diagnostics ++ [prior, event] := by
  have result := orElse_success_left_trace second
    (first := emitValue event 3) (input := input.emit prior) rfl
    (emitDiagnostic_success_trace event (input.emit prior)).2
  refine ⟨result.1, ?_⟩
  simpa only [(emitDiagnostic_success_trace prior input).2, List.append_assoc,
    List.singleton_append] using result.2

end Solcore.Test.SyntaxParserCompositionalDiagnosticTraceProperties
