import Solcore.Syntax.Parser.PrimitiveCarrierProperties

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

/-- Core literals preserve the complete token window on every reply. -/
theorem coreLiteral_preservesTokenWindow :
    Parser.PreservesTokenWindow coreLiteral := by
  intro input
  unfold coreLiteral
  cases found : input.peek? with
  | none => exact rejectAt_preservesTokenWindow input _ _
  | some token =>
      rcases token with ⟨span, kind⟩
      cases kind
      all_goals try { exact rejectAt_preservesTokenWindow input _ _ }
      all_goals exact ⟨rfl, rfl⟩

/-- Boolean builtin names preserve the complete token window on every reply. -/
theorem booleanIdentifier_preservesTokenWindow :
    Parser.PreservesTokenWindow booleanIdentifier := by
  intro input
  unfold booleanIdentifier
  cases found : input.peek? with
  | none => exact rejectAt_preservesTokenWindow input _ _
  | some token =>
      rcases token with ⟨span, kind⟩
      cases kind
      all_goals try { exact rejectAt_preservesTokenWindow input _ _ }
      case keyword keyword =>
        cases keyword
        all_goals try { exact rejectAt_preservesTokenWindow input _ _ }
        all_goals exact ⟨rfl, rfl⟩

/-- Core-literal success preserves the immutable token carrier. -/
theorem coreLiteral_preservesTokensOnSuccess :
    Parser.PreservesTokensOnSuccess coreLiteral := by
  intro input literal next result
  rw [coreLiteral_ok_state_shape result]

/-- Core-literal success consumes exactly one token. -/
theorem coreLiteral_cursor_lt_onSuccess {input next : State}
    {literal : CoreLiteral}
    (result : coreLiteral input = .ok literal next) :
    input.cursor < next.cursor := by
  rw [coreLiteral_ok_state_shape result]
  simp

/-- Core-literal success advances by exactly one token. -/
theorem coreLiteral_cursorMonotoneOnSuccess :
    Parser.CursorMonotoneOnSuccess coreLiteral := by
  intro input literal next result
  rw [coreLiteral_ok_state_shape result]
  simp

/-- A core literal starts at the literal token it consumes. -/
theorem coreLiteral_startsAtCurrentTokenOnSuccess :
    Parser.StartsAtCurrentTokenOnSuccess coreLiteral (·.span) := by
  intro input literal next result
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
      all_goals exact ⟨_, rfl, rfl⟩

/-- Boolean-identifier success preserves the immutable token carrier. -/
theorem booleanIdentifier_preservesTokensOnSuccess :
    Parser.PreservesTokensOnSuccess booleanIdentifier := by
  intro input name next result
  rw [booleanIdentifier_ok_state_shape result]

/-- Boolean-identifier success consumes exactly one token. -/
theorem booleanIdentifier_cursor_lt_onSuccess {input next : State}
    {name : Identifier}
    (result : booleanIdentifier input = .ok name next) :
    input.cursor < next.cursor := by
  rw [booleanIdentifier_ok_state_shape result]
  simp

/-- Boolean-identifier success advances by exactly one token. -/
theorem booleanIdentifier_cursorMonotoneOnSuccess :
    Parser.CursorMonotoneOnSuccess booleanIdentifier := by
  intro input name next result
  rw [booleanIdentifier_ok_state_shape result]
  simp

/-- A Boolean builtin name starts at its keyword token. -/
theorem booleanIdentifier_startsAtCurrentTokenOnSuccess :
    Parser.StartsAtCurrentTokenOnSuccess booleanIdentifier (·.span) := by
  intro input name next result
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
        all_goals exact ⟨_, rfl, rfl⟩

end Solcore.Syntax.Parser
