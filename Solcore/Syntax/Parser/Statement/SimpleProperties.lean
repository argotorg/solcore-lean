import Solcore.Syntax.Parser.Statement.Simple
import Solcore.Syntax.Parser.PrimitiveCarrierProperties

/-! Contracts for nonrecursive canonical Core-statement components. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser
namespace StatementSimpleInternals

private theorem advanceAfterValueAssignPeek_validFor {input : State}
    {token : Token} (valid : input.ValidFor)
    (found : input.peek? = some token) :
    token.span.ValidFor input.file ∧
      ({ input with cursor := input.cursor + 1 } : State).ValidFor ∧
      ({ input with cursor := input.cursor + 1 } : State).file = input.file := by
  refine ⟨valid.peek?_span_validFor found, ?_, rfl⟩
  apply valid.advance?_validFor (token := token)
  unfold State.advance?
  rw [found]
  rfl

/-- Assignment-operator success consumes the current token exactly once. -/
theorem valueAssignOperator_ok_state_shape {input next : State}
    {operator : Located ValueAssignOp}
    (parsed : valueAssignOperator input = .ok operator next) :
    ∃ token, input.peek? = some token ∧ token.span = operator.span ∧
      next = { input with cursor := input.cursor + 1 } := by
  unfold valueAssignOperator at parsed
  cases found : input.peek? with
  | none =>
      simp only [found] at parsed
      unfold rejectAt at parsed
      contradiction
  | some token =>
      simp only [found] at parsed
      cases accepted : valueAssignOp? token.value with
      | none =>
          simp only [accepted] at parsed
          unfold rejectAt at parsed
          contradiction
      | some value =>
          simp only [accepted] at parsed
          cases parsed
          exact ⟨token, rfl, rfl, rfl⟩

/-- Assignment-operator success preserves source and state validity. -/
theorem valueAssignOperator_ok_validFor {input next : State}
    {operator : Located ValueAssignOp} (valid : input.ValidFor)
    (parsed : valueAssignOperator input = .ok operator next) :
    operator.span.ValidFor input.file ∧ next.ValidFor ∧
      next.file = input.file := by
  rcases valueAssignOperator_ok_state_shape parsed with
    ⟨token, found, span, rfl⟩
  have advanced := advanceAfterValueAssignPeek_validFor valid found
  exact ⟨by simpa [span] using advanced.1, advanced.2⟩

/-- Assignment-operator rejection leaves the parser state unchanged. -/
theorem valueAssignOperator_reject_state_shape {input next : State}
    {failure : Failure}
    (parsed : valueAssignOperator input = .reject failure next) :
    next = input := by
  unfold valueAssignOperator at parsed
  cases found : input.peek? with
  | none =>
      simp only [found] at parsed
      unfold rejectAt at parsed
      cases parsed
      rfl
  | some token =>
      simp only [found] at parsed
      cases accepted : valueAssignOp? token.value with
      | none =>
          simp only [accepted] at parsed
          unfold rejectAt at parsed
          cases parsed
          rfl
      | some value => simp [accepted] at parsed

/-- Assignment-operator rejection retains valid failure provenance. -/
theorem valueAssignOperator_reject_validFor {input next : State}
    {failure : Failure} (valid : input.ValidFor)
    (parsed : valueAssignOperator input = .reject failure next) :
    failure.span.ValidFor input.file ∧ next.ValidFor ∧
      next.file = input.file := by
  unfold valueAssignOperator at parsed
  cases found : input.peek? with
  | none =>
      simp only [found] at parsed
      exact rejectAt_reject_validFor valid _ _ parsed
  | some token =>
      simp only [found] at parsed
      cases accepted : valueAssignOp? token.value with
      | none =>
          simp only [accepted] at parsed
          exact rejectAt_reject_validFor valid _ _ parsed
      | some value => simp [accepted] at parsed

/-- Every ordinary assignment-operator result has valid provenance. -/
theorem valueAssignOperator_validFor :
    valueAssignOperator.ValidFor Located.ValidFor := by
  intro input valid
  cases parsed : valueAssignOperator input with
  | ok operator next =>
      exact valueAssignOperator_ok_validFor valid parsed
  | reject failure next =>
      exact valueAssignOperator_reject_validFor valid parsed
  | invariant error => trivial

/-- Assignment-operator parsing preserves the complete token window. -/
theorem valueAssignOperator_preservesTokenWindow :
    Parser.PreservesTokenWindow valueAssignOperator := by
  intro input
  cases parsed : valueAssignOperator input with
  | ok operator next =>
      rcases valueAssignOperator_ok_state_shape parsed with
        ⟨_token, _found, _span, rfl⟩
      exact ⟨rfl, rfl⟩
  | reject failure next =>
      rw [valueAssignOperator_reject_state_shape parsed]
      exact ⟨rfl, rfl⟩
  | invariant error => trivial

theorem valueAssignOperator_preservesTokensOnSuccess :
    Parser.PreservesTokensOnSuccess valueAssignOperator :=
  valueAssignOperator_preservesTokenWindow.preservesTokensOnSuccess

/-- Assignment-operator success advances by exactly one token. -/
theorem valueAssignOperator_cursorMonotoneOnSuccess :
    Parser.CursorMonotoneOnSuccess valueAssignOperator := by
  intro input operator next parsed
  rcases valueAssignOperator_ok_state_shape parsed with
    ⟨_token, _found, _span, rfl⟩
  simp

/-- Assignment operators start at the current input token. -/
theorem valueAssignOperator_startsAtCurrentTokenOnSuccess :
    Parser.StartsAtCurrentTokenOnSuccess valueAssignOperator (·.span) := by
  intro input operator next parsed
  rcases valueAssignOperator_ok_state_shape parsed with
    ⟨token, found, span, _next⟩
  exact ⟨token, found, congrArg SourceSpan.startByte span⟩

end StatementSimpleInternals
end Solcore.Syntax.Parser
