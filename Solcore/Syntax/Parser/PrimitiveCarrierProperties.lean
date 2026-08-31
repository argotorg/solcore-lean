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

theorem keyword_preservesTokensOnSuccess
    (value : HardKeyword) (context : ParseContext) :
    Parser.PreservesTokensOnSuccess (keyword value context) :=
  acceptToken_preservesTokensOnSuccess (.keyword value) context
    (· == .keyword value)

theorem symbol_preservesTokensOnSuccess
    (value : Symbol) (context : ParseContext) :
    Parser.PreservesTokensOnSuccess (symbol value context) :=
  acceptToken_preservesTokensOnSuccess (.symbol value) context
    (· == .symbol value)

theorem contextual_preservesTokensOnSuccess
    (value : ContextualKeyword) (context : ParseContext) :
    Parser.PreservesTokensOnSuccess (contextual value context) :=
  acceptToken_preservesTokensOnSuccess (.contextual value) context
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

theorem identifier_preservesTokensOnSuccess (context : ParseContext) :
    Parser.PreservesTokensOnSuccess (identifier context) := by
  intro input name next result
  exact (identifier_ok_state_shape context result).choose_spec.2.2.1

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

end Solcore.Syntax.Parser
