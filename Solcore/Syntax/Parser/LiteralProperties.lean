import Solcore.Syntax.Parser.Validity

/-! Compositional contracts for canonical literal token consumers. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Core-literal success advances only the parser cursor. -/
theorem coreLiteral_ok_state_shape {input next : State}
    {literal : CoreLiteral}
    (result : coreLiteral input = .ok literal next) :
    next = { input with cursor := input.cursor + 1 } := by
  unfold coreLiteral at result
  cases found : input.peek? with
  | none =>
      simp only [found] at result
      unfold rejectAt at result
      contradiction
  | some token =>
      rcases token with ⟨span, kind⟩
      cases kind <;> simp only [found] at result
      all_goals try { unfold rejectAt at result; contradiction }
      all_goals cases result
      all_goals rfl

/-- Boolean-identifier success advances only the parser cursor. -/
theorem booleanIdentifier_ok_state_shape {input next : State}
    {name : Identifier}
    (result : booleanIdentifier input = .ok name next) :
    next = { input with cursor := input.cursor + 1 } := by
  unfold booleanIdentifier at result
  cases found : input.peek? with
  | none =>
      simp only [found] at result
      unfold rejectAt at result
      contradiction
  | some token =>
      rcases token with ⟨span, kind⟩
      cases kind <;> simp only [found] at result
      all_goals try { unfold rejectAt at result; contradiction }
      case keyword keyword =>
        cases keyword <;> simp only at result
        all_goals try { unfold rejectAt at result; contradiction }
        all_goals cases result
        all_goals rfl

/-- Core-literal success preserves the immutable token carrier. -/
theorem coreLiteral_preservesTokensOnSuccess :
    Parser.PreservesTokensOnSuccess coreLiteral := by
  intro input literal next result
  rw [coreLiteral_ok_state_shape result]

/-- Boolean-identifier success preserves the immutable token carrier. -/
theorem booleanIdentifier_preservesTokensOnSuccess :
    Parser.PreservesTokensOnSuccess booleanIdentifier := by
  intro input name next result
  rw [booleanIdentifier_ok_state_shape result]

end Solcore.Syntax.Parser
