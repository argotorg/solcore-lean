import Solcore.Syntax.Parser.QualifiedNameRejectionTraceCorrespondenceProperties

/-! Concrete checked qualified-name rejection fixes the complete state while
keeping the reported Failure uncommitted, even for arbitrary input carriers. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

namespace QualifiedNameInternals

theorem qualifiedNameTail_reject_context
    (context : ParseContext) (phase : ParserPhase) (first : Identifier) :
    ∀ fuel last tailRev input failure rejected,
      qualifiedNameTail context phase first fuel last tailRev input = .reject failure rejected →
      rejected.file = input.file ∧ rejected.window = input.window := by
  intro fuel
  induction fuel with
  | zero => intro last tailRev input failure rejected result; simp [qualifiedNameTail] at result
  | succ fuel ih =>
      intro last tailRev input failure rejected result
      unfold qualifiedNameTail at result
      split at result
      · rename_i present
        rcases symbol_eq_ok_of_isSymbol_eq_true .dot context present with ⟨dot, dotResult⟩
        simp only [dotResult] at result
        cases childResult : identifier context { input with cursor := input.cursor + 1 } with
        | invariant error => simp [childResult] at result
        | reject childFailure childRejected =>
            simp only [childResult] at result
            cases result
            rw [identifier_reject_state_eq context childResult]
            exact ⟨rfl, rfl⟩
        | ok component next =>
            simp only [childResult] at result
            have frame := identifier_success_context_eq context childResult
            have later := ih component (component :: tailRev) next failure rejected result
            exact ⟨later.1.trans frame.1, later.2.trans frame.2⟩
      · unfold finishQualifiedName at result
        contradiction

end QualifiedNameInternals

theorem qualifiedName_reject_context (context : ParseContext) (phase : ParserPhase)
    {input rejected : State} {failure : Failure}
    (result : qualifiedName context phase input = .reject failure rejected) :
    rejected.file = input.file ∧ rejected.window = input.window := by
  unfold qualifiedName at result
  cases firstResult : identifier context input with
  | invariant error => simp [firstResult] at result
  | reject firstFailure firstRejected =>
      simp only [firstResult] at result
      cases result
      rw [identifier_reject_state_eq context firstResult]
      exact ⟨rfl, rfl⟩
  | ok first next =>
      simp only [firstResult] at result
      have firstFrame := identifier_success_context_eq context firstResult
      have tailFrame := QualifiedNameInternals.qualifiedNameTail_reject_context context phase first
        (next.remainingCount + 1) first [] next failure rejected result
      exact ⟨tailFrame.1.trans firstFrame.1, tailFrame.2.trans firstFrame.2⟩

theorem qualifiedName_reject_state_eq_of_trace (context : ParseContext) (phase : ParserPhase)
    {input rejected : State} {failure : Failure} {after : DeclarativeGrammar.Remainder}
    {trace : List ParseDiagnostic}
    (result : qualifiedName context phase input = .reject failure rejected)
    (rejection : DeclarativeGrammar.QualifiedNameTraceRejects context input.file.id input.window.endByte
      input.declarativeRemainder after failure.toDiagnostic trace) :
    rejected = { input with
      cursor := after.cursor
      diagnosticsRev := trace.reverse ++ input.diagnosticsRev } := by
  rcases qualifiedName_reject_trace_sound context phase result with ⟨actualTrace, actual, actualEq⟩
  have same := actual.result_unique rejection
  have tokensEq : rejected.tokens = input.tokens := actual.output_window.1
  have cursorEq : rejected.cursor = after.cursor := congrArg DeclarativeGrammar.Remainder.cursor same.1
  have frame := qualifiedName_reject_context context phase result
  have events := congrArg List.reverse actualEq
  have diagnosticsEq : rejected.diagnosticsRev = trace.reverse ++ input.diagnosticsRev := by
    simpa only [same.2.2, State.diagnostics, List.reverse_append, List.reverse_reverse] using events
  cases input
  cases rejected
  simp_all only [State.declarativeRemainder]

theorem qualifiedName_eq_reject_of_trace (context : ParseContext) (phase : ParserPhase)
    {input : State} {after : DeclarativeGrammar.Remainder}
    {failure : Failure} {trace : List ParseDiagnostic}
    (rejection : DeclarativeGrammar.QualifiedNameTraceRejects context input.file.id input.window.endByte
      input.declarativeRemainder after failure.toDiagnostic trace) :
    qualifiedName context phase input = .reject failure { input with
      cursor := after.cursor
      diagnosticsRev := trace.reverse ++ input.diagnosticsRev } := by
  rcases (qualifiedName_trace_reject_failure_iff context phase).mp rejection with ⟨rejected, result, _, _⟩
  exact qualifiedName_reject_state_eq_of_trace context phase result rejection ▸ result

end Solcore.Syntax.Parser
