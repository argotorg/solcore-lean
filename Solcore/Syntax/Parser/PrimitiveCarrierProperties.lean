import Solcore.Syntax.Parser.Validity

/-! Immutable token-carrier laws for primitive canonical parsers. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

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

theorem rawIdentifier_cursorMonotoneOnSuccess (context : ParseContext) :
    Parser.CursorMonotoneOnSuccess (rawIdentifier context) := by
  intro input name next result
  rw [rawIdentifier_ok_state_shape context result]
  simp

theorem identifier_preservesTokensOnSuccess (context : ParseContext) :
    Parser.PreservesTokensOnSuccess (identifier context) := by
  intro input name next result
  exact (identifier_ok_state_shape context result).choose_spec.2.2.1

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

theorem yulIdentifier_cursorMonotoneOnSuccess (context : ParseContext) :
    Parser.CursorMonotoneOnSuccess (yulIdentifier context) := by
  intro input name next result
  rw [yulIdentifier_ok_state_shape context result]
  simp

end Solcore.Syntax.Parser
