import Solcore.Syntax.Parser.Primitive

/-! Compositional laws from executable branch premises, not independent
grammar judgments. Sequencing retains each executed branch's diagnostics. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- One explicit emission appends one event after all prior diagnostics. -/
theorem emitDiagnostic_success_trace (diagnostic : ParseDiagnostic) (input : State) :
    emitDiagnostic diagnostic input = .ok () (input.emit diagnostic) ∧
      (input.emit diagnostic).diagnostics = input.diagnostics ++ [diagnostic] := by
  refine ⟨rfl, ?_⟩
  simp only [State.emit, State.diagnostics, List.reverse_cons]

/-- Successful sequencing appends suffixes in execution order. -/
theorem bind_success_trace {alpha beta : Type}
    {first : Parser alpha} {next : alpha → Parser beta}
    {input middle output : State} {firstValue : alpha} {value : beta}
    {firstTrace nextTrace : List ParseDiagnostic}
    (firstResult : first input = .ok firstValue middle)
    (firstDiagnostics : middle.diagnostics = input.diagnostics ++ firstTrace)
    (nextResult : next firstValue middle = .ok value output)
    (nextDiagnostics : output.diagnostics = middle.diagnostics ++ nextTrace) :
    (first >>= next) input = .ok value output ∧
      output.diagnostics = input.diagnostics ++ (firstTrace ++ nextTrace) := by
  refine ⟨?_, ?_⟩
  · simp only [bind, firstResult, nextResult]
  · rw [nextDiagnostics, firstDiagnostics, List.append_assoc]

/-- Rejection in the continuation retains both executed suffixes in order;
ordinary bind is not a transactional rollback boundary. -/
theorem bind_reject_right_trace {alpha beta : Type}
    {first : Parser alpha} {next : alpha → Parser beta}
    {input middle rejected : State} {firstValue : alpha} {failure : Failure}
    {firstTrace nextTrace : List ParseDiagnostic}
    (firstResult : first input = .ok firstValue middle)
    (firstDiagnostics : middle.diagnostics = input.diagnostics ++ firstTrace)
    (nextResult : next firstValue middle = .reject failure rejected)
    (nextDiagnostics : rejected.diagnostics = middle.diagnostics ++ nextTrace) :
    (first >>= next) input = .reject failure rejected ∧
      rejected.diagnostics = input.diagnostics ++ (firstTrace ++ nextTrace) := by
  refine ⟨?_, ?_⟩
  · simp only [bind, firstResult, nextResult]
  · rw [nextDiagnostics, firstDiagnostics, List.append_assoc]

/-- A rejected first stage retains its exact failure/state/trace and never
executes the continuation. No premise about that continuation is required. -/
theorem bind_reject_left_trace {alpha beta : Type}
    {first : Parser alpha} (next : alpha → Parser beta)
    {input rejected : State} {failure : Failure} {trace : List ParseDiagnostic}
    (firstResult : first input = .reject failure rejected)
    (diagnostics : rejected.diagnostics = input.diagnostics ++ trace) :
    (first >>= next) input = .reject failure rejected ∧
      rejected.diagnostics = input.diagnostics ++ trace := by
  exact ⟨by simp only [bind, firstResult], diagnostics⟩

/-- Mapping changes only the successful value, preserving the exact state
and complete diagnostic suffix returned by its executable argument. -/
theorem map_success_trace {alpha beta : Type}
    (transform : alpha → beta) {parser : Parser alpha}
    {input output : State} {value : alpha} {trace : List ParseDiagnostic}
    (result : parser input = .ok value output)
    (diagnostics : output.diagnostics = input.diagnostics ++ trace) :
    (transform <$> parser) input = .ok (transform value) output ∧
      output.diagnostics = input.diagnostics ++ trace := by
  refine ⟨?_, diagnostics⟩
  change ((parser >>= fun parsed => pure (transform parsed)) : Parser beta) input = _
  simp only [bind, result, pure]

/-- Mapping cannot replace a failure, rejected state, or emitted suffix. -/
theorem map_reject_trace {alpha beta : Type}
    (transform : alpha → beta) {parser : Parser alpha}
    {input rejected : State} {failure : Failure} {trace : List ParseDiagnostic}
    (result : parser input = .reject failure rejected)
    (diagnostics : rejected.diagnostics = input.diagnostics ++ trace) :
    (transform <$> parser) input = .reject failure rejected ∧
      rejected.diagnostics = input.diagnostics ++ trace := by
  refine ⟨?_, diagnostics⟩
  change ((parser >>= fun parsed => pure (transform parsed)) : Parser beta) input = _
  simp only [bind, result]

/-- Executor failure is propagated before sequencing can invoke a continuation. -/
theorem bind_invariant_left_exact {alpha beta : Type}
    {first : Parser alpha} (next : alpha → Parser beta)
    {input : State} {error : ParserInvariantError}
    (result : first input = .invariant error) :
    (first >>= next) input = .invariant error := by
  simp only [bind, result]

end Solcore.Syntax.Parser
