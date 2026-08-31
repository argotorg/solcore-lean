import Solcore.Syntax.Parser.Validity

/-! Immutable token-carrier laws for primitive canonical parsers. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- An uncommitted rejection retains the input token array and window. -/
theorem rejectAt_preservesTokenWindow {α : Type} (state : State)
    (expected : NonemptyList ParseExpectation) (context : ParseContext) :
    (rejectAt (α := α) state expected context).PreservesTokenWindow state := by
  exact ⟨rfl, rfl⟩

/-- Generic token rejection returns the unchanged input state. -/
theorem acceptToken_reject_state_shape
    (expected : ParseExpectation) (context : ParseContext)
    (accepts : TokenKind → Bool) {input next : State} {failure : Failure}
    (result : acceptToken expected context accepts input =
      .reject failure next) : next = input := by
  unfold acceptToken at result
  cases found : input.peek? with
  | none =>
      simp only [found] at result
      unfold rejectAt at result
      cases result
      rfl
  | some token =>
      simp only [found] at result
      split at result
      · contradiction
      · unfold rejectAt at result
        cases result
        rfl

/-- Generic token acceptance preserves the token window on every reply. -/
theorem acceptToken_preservesTokenWindow
    (expected : ParseExpectation) (context : ParseContext)
    (accepts : TokenKind → Bool) :
    Parser.PreservesTokenWindow (acceptToken expected context accepts) := by
  intro input
  cases result : acceptToken expected context accepts input with
  | ok token next =>
      rw [(acceptToken_ok_state_shape expected context accepts result).2]
      exact ⟨rfl, rfl⟩
  | reject failure next =>
      rw [acceptToken_reject_state_shape expected context accepts result]
      exact ⟨rfl, rfl⟩
  | invariant error => trivial

/-- Generic token acceptance changes only the parser cursor. -/
theorem acceptToken_preservesTokensOnSuccess
    (expected : ParseExpectation) (context : ParseContext)
    (accepts : TokenKind → Bool) :
    Parser.PreservesTokensOnSuccess
      (acceptToken expected context accepts) := by
  intro input token next result
  rcases acceptToken_ok_state_shape expected context accepts result with
    ⟨_found, rfl⟩
  rfl

/-- Generic token acceptance advances by exactly one token on success. -/
theorem acceptToken_cursor_lt_onSuccess
    (expected : ParseExpectation) (context : ParseContext)
    (accepts : TokenKind → Bool) {input next : State} {token : Token}
    (result : acceptToken expected context accepts input = .ok token next) :
    input.cursor < next.cursor := by
  rw [(acceptToken_ok_state_shape expected context accepts result).2]
  simp

theorem acceptToken_cursorMonotoneOnSuccess
    (expected : ParseExpectation) (context : ParseContext)
    (accepts : TokenKind → Bool) :
    Parser.CursorMonotoneOnSuccess
      (acceptToken expected context accepts) := by
  intro input token next result
  exact Nat.le_of_lt
    (acceptToken_cursor_lt_onSuccess expected context accepts result)

/-- Generic token acceptance returns a span beginning at the input token. -/
theorem acceptToken_startsAtCurrentTokenOnSuccess
    (expected : ParseExpectation) (context : ParseContext)
    (accepts : TokenKind → Bool) :
    Parser.StartsAtCurrentTokenOnSuccess
      (acceptToken expected context accepts) (·.span) := by
  intro input token next result
  exact ⟨token,
    (acceptToken_ok_state_shape expected context accepts result).1, rfl⟩

theorem keyword_preservesTokensOnSuccess
    (value : HardKeyword) (context : ParseContext) :
    Parser.PreservesTokensOnSuccess (keyword value context) :=
  acceptToken_preservesTokensOnSuccess (.keyword value) context
    (· == .keyword value)

theorem keyword_preservesTokenWindow
    (value : HardKeyword) (context : ParseContext) :
    Parser.PreservesTokenWindow (keyword value context) :=
  acceptToken_preservesTokenWindow (.keyword value) context
    (· == .keyword value)

theorem keyword_cursorMonotoneOnSuccess
    (value : HardKeyword) (context : ParseContext) :
    Parser.CursorMonotoneOnSuccess (keyword value context) :=
  acceptToken_cursorMonotoneOnSuccess (.keyword value) context
    (· == .keyword value)

theorem symbol_preservesTokensOnSuccess
    (value : Symbol) (context : ParseContext) :
    Parser.PreservesTokensOnSuccess (symbol value context) :=
  acceptToken_preservesTokensOnSuccess (.symbol value) context
    (· == .symbol value)

theorem symbol_preservesTokenWindow
    (value : Symbol) (context : ParseContext) :
    Parser.PreservesTokenWindow (symbol value context) :=
  acceptToken_preservesTokenWindow (.symbol value) context
    (· == .symbol value)

theorem symbol_cursorMonotoneOnSuccess
    (value : Symbol) (context : ParseContext) :
    Parser.CursorMonotoneOnSuccess (symbol value context) :=
  acceptToken_cursorMonotoneOnSuccess (.symbol value) context
    (· == .symbol value)

theorem symbol_startsAtCurrentTokenOnSuccess
    (value : Symbol) (context : ParseContext) :
    Parser.StartsAtCurrentTokenOnSuccess (symbol value context) (·.span) :=
  acceptToken_startsAtCurrentTokenOnSuccess (.symbol value) context
    (· == .symbol value)

theorem contextual_preservesTokensOnSuccess
    (value : ContextualKeyword) (context : ParseContext) :
    Parser.PreservesTokensOnSuccess (contextual value context) :=
  acceptToken_preservesTokensOnSuccess (.contextual value) context
    (·.isContextual value)

theorem contextual_preservesTokenWindow
    (value : ContextualKeyword) (context : ParseContext) :
    Parser.PreservesTokenWindow (contextual value context) :=
  acceptToken_preservesTokenWindow (.contextual value) context
    (·.isContextual value)

theorem contextual_cursorMonotoneOnSuccess
    (value : ContextualKeyword) (context : ParseContext) :
    Parser.CursorMonotoneOnSuccess (contextual value context) :=
  acceptToken_cursorMonotoneOnSuccess (.contextual value) context
    (·.isContextual value)

theorem contextual_startsAtCurrentTokenOnSuccess
    (value : ContextualKeyword) (context : ParseContext) :
    Parser.StartsAtCurrentTokenOnSuccess (contextual value context) (·.span) :=
  acceptToken_startsAtCurrentTokenOnSuccess (.contextual value) context
    (·.isContextual value)

/-- Raw identifier success changes only the parser cursor. -/
theorem rawIdentifier_ok_state_shape (context : ParseContext)
    {input next : State} {name : Identifier}
    (result : rawIdentifier context input = .ok name next) :
    next = { input with cursor := input.cursor + 1 } := by
  unfold rawIdentifier at result
  cases found : input.peek? with
  | none =>
      simp only [found] at result
      unfold rejectAt at result
      contradiction
  | some token =>
      rcases token with ⟨span, kind⟩
      cases kind <;> simp only [found] at result
      all_goals try { unfold rejectAt at result; contradiction }
      case identifier text => cases result; rfl

theorem rawIdentifier_preservesTokensOnSuccess (context : ParseContext) :
    Parser.PreservesTokensOnSuccess (rawIdentifier context) := by
  intro input name next result
  rw [rawIdentifier_ok_state_shape context result]

/-- Raw identifiers preserve the token window on success and rejection. -/
theorem rawIdentifier_preservesTokenWindow (context : ParseContext) :
    Parser.PreservesTokenWindow (rawIdentifier context) := by
  intro input
  unfold rawIdentifier
  cases found : input.peek? with
  | none => exact rejectAt_preservesTokenWindow input _ _
  | some token =>
      rcases token with ⟨span, kind⟩
      cases kind <;> simp only
      all_goals try { exact rejectAt_preservesTokenWindow input _ _ }
      exact ⟨rfl, rfl⟩

theorem rawIdentifier_cursorMonotoneOnSuccess (context : ParseContext) :
    Parser.CursorMonotoneOnSuccess (rawIdentifier context) := by
  intro input name next result
  rw [rawIdentifier_ok_state_shape context result]
  simp

theorem identifier_preservesTokensOnSuccess (context : ParseContext) :
    Parser.PreservesTokensOnSuccess (identifier context) := by
  intro input name next result
  exact (identifier_ok_state_shape context result).choose_spec.2.2.1

/-- Checked identifiers preserve the token window on success and rejection. -/
theorem identifier_preservesTokenWindow (context : ParseContext) :
    Parser.PreservesTokenWindow (identifier context) := by
  intro input
  unfold identifier
  cases raw : rawIdentifier context input with
  | ok name next =>
      have rawShape := rawIdentifier_preservesTokenWindow context input
      rw [raw] at rawShape
      change (if name.value.toList.contains '-' then
          Reply.ok name (next.emit {
            span := name.span
            kind := .invalidIdentifierHyphen name.value
          })
        else Reply.ok name next).PreservesTokenWindow input
      split
      · exact ⟨by simpa [State.emit] using rawShape.1,
          by simpa [State.emit] using rawShape.2⟩
      · exact rawShape
  | reject failure next =>
      have rawShape := rawIdentifier_preservesTokenWindow context input
      rw [raw] at rawShape
      change (Reply.reject failure next).PreservesTokenWindow input
      exact rawShape
  | invariant error =>
      change (Reply.invariant error).PreservesTokenWindow input
      trivial

theorem identifier_cursorMonotoneOnSuccess (context : ParseContext) :
    Parser.CursorMonotoneOnSuccess (identifier context) := by
  intro input name next result
  rw [(identifier_ok_state_shape context result).choose_spec.2.2.2]
  simp

/-- Yul identifier success changes only the parser cursor. -/
theorem yulIdentifier_ok_state_shape (context : ParseContext)
    {input next : State} {name : Identifier}
    (result : yulIdentifier context input = .ok name next) :
    next = { input with cursor := input.cursor + 1 } := by
  unfold yulIdentifier at result
  cases found : input.peek? with
  | none =>
      simp only [found] at result
      unfold rejectAt at result
      contradiction
  | some token =>
      rcases token with ⟨span, kind⟩
      cases kind <;> simp only [found] at result
      all_goals try { unfold rejectAt at result; contradiction }
      case yulIdentifier text => cases result; rfl

theorem yulIdentifier_preservesTokensOnSuccess (context : ParseContext) :
    Parser.PreservesTokensOnSuccess (yulIdentifier context) := by
  intro input name next result
  rw [yulIdentifier_ok_state_shape context result]

/-- Primitive Yul identifiers preserve every ordinary token window. -/
theorem yulIdentifier_preservesTokenWindow (context : ParseContext) :
    Parser.PreservesTokenWindow (yulIdentifier context) := by
  intro input
  unfold yulIdentifier
  cases found : input.peek? with
  | none => exact rejectAt_preservesTokenWindow input _ _
  | some token =>
      rcases token with ⟨span, kind⟩
      cases kind <;> simp only
      all_goals try { exact rejectAt_preservesTokenWindow input _ _ }
      exact ⟨rfl, rfl⟩

theorem yulIdentifier_cursorMonotoneOnSuccess (context : ParseContext) :
    Parser.CursorMonotoneOnSuccess (yulIdentifier context) := by
  intro input name next result
  rw [yulIdentifier_ok_state_shape context result]
  simp

end Solcore.Syntax.Parser
