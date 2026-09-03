import Solcore.Syntax.Parser.SequencingDiagnosticTraceProperties

/-! Executable-premise laws for transactional ordered choice. Rejected left
states, including all their diagnostics, are discarded before the right branch.
These are compositional execution laws, not independent grammar judgments. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Left rejection retries the right parser on exactly the original input.
No constraint on the discarded cursor, carrier, or diagnostic trace is needed. -/
theorem orElse_eq_right_of_reject {alpha : Type}
    {first : Parser alpha} (second : Parser alpha)
    {input discarded : State} {failure : Failure}
    (firstResult : first input = .reject failure discarded) :
    orElse first second input = second input := by
  simp only [orElse, firstResult]

/-- The first successful alternative returns its exact state and suffix;
the right alternative is irrelevant and no right outcome is assumed. -/
theorem orElse_success_left_trace {alpha : Type}
    {first : Parser alpha} (second : Parser alpha)
    {input output : State} {value : alpha} {trace : List ParseDiagnostic}
    (firstResult : first input = .ok value output)
    (diagnostics : output.diagnostics = input.diagnostics ++ trace) :
    orElse first second input = .ok value output ∧
      output.diagnostics = input.diagnostics ++ trace := by
  exact ⟨by simp only [orElse, firstResult], diagnostics⟩

/-- Successful fallback retains only its suffix after the original prefix.
The left branch may have emitted any nonempty trace before rejecting. -/
theorem orElse_success_right_trace {alpha : Type}
    {first second : Parser alpha} {input discarded output : State}
    {failure : Failure} {value : alpha} {trace : List ParseDiagnostic}
    (firstResult : first input = .reject failure discarded)
    (secondResult : second input = .ok value output)
    (diagnostics : output.diagnostics = input.diagnostics ++ trace) :
    orElse first second input = .ok value output ∧
      output.diagnostics = input.diagnostics ++ trace := by
  exact ⟨(orElse_eq_right_of_reject second firstResult).trans secondResult, diagnostics⟩

/-- Failed fallback also retains only the right failure/state/trace; neither
the left failure payload nor its emitted suffix survives the transaction. -/
theorem orElse_reject_right_trace {alpha : Type}
    {first second : Parser alpha} {input discarded rejected : State}
    {leftFailure rightFailure : Failure} {trace : List ParseDiagnostic}
    (firstResult : first input = .reject leftFailure discarded)
    (secondResult : second input = .reject rightFailure rejected)
    (diagnostics : rejected.diagnostics = input.diagnostics ++ trace) :
    orElse first second input = .reject rightFailure rejected ∧
      rejected.diagnostics = input.diagnostics ++ trace := by
  exact ⟨(orElse_eq_right_of_reject second firstResult).trans secondResult, diagnostics⟩

/-- Invariant failure is not ordinary rejection and never enables fallback. -/
theorem orElse_invariant_left_exact {alpha : Type}
    {first : Parser alpha} (second : Parser alpha)
    {input : State} {error : ParserInvariantError}
    (firstResult : first input = .invariant error) :
    orElse first second input = .invariant error := by
  simp only [orElse, firstResult]

/-- A fallback invariant is exactly the right reply at the original input;
there is no rejected-state trace to expose at an invariant-only boundary. -/
theorem orElse_invariant_right_exact {alpha : Type}
    {first second : Parser alpha} {input discarded : State}
    {failure : Failure} {error : ParserInvariantError}
    (firstResult : first input = .reject failure discarded)
    (secondResult : second input = .invariant error) :
    orElse first second input = .invariant error :=
  (orElse_eq_right_of_reject second firstResult).trans secondResult

end Solcore.Syntax.Parser
