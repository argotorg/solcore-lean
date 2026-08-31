import Solcore.Syntax.Parser.Yul.Expression
import Solcore.Syntax.Parser.PrimitiveCarrierProperties
import Solcore.Syntax.Parser.LiteralProperties

/-! Provenance and cursor contracts for nonrecursive inline-Yul leaves. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

private theorem advanceAfterYulPeek_validFor {state : State}
    {token : Token} (valid : state.ValidFor)
    (found : state.peek? = some token) :
    token.span.ValidFor state.file ∧
      ({ state with cursor := state.cursor + 1 } : State).ValidFor ∧
      ({ state with cursor := state.cursor + 1 } : State).file = state.file := by
  refine ⟨valid.peek?_span_validFor found, ?_, rfl⟩
  apply valid.advance?_validFor (token := token)
  unfold State.advance?
  rw [found]
  rfl

/-- Yul-name success consumes exactly one token and preserves its span. -/
theorem yulName_ok_state_shape {input next : State} {name : YulIdentifier}
    (result : yulName input = .ok name next) :
    ∃ token, input.peek? = some token ∧
      token.span = name.span ∧ next.tokens = input.tokens ∧
      next.cursor = input.cursor + 1 := by
  unfold yulName at result
  cases found : input.peek? with
  | none =>
      simp only [found] at result
      unfold rejectAt at result
      contradiction
  | some token =>
      rcases token with ⟨span, kind⟩
      cases kind <;> simp only [found] at result
      all_goals try { unfold rejectAt at result; contradiction }
      case identifier text =>
        rcases identifier_ok_state_shape .yulExpression result with
          ⟨token, tokenFound, tokenSpan, tokensEq, cursorEq⟩
        exact ⟨token, by simpa [found] using tokenFound,
          tokenSpan, tokensEq, cursorEq⟩
      case yulIdentifier text =>
        cases result
        exact ⟨_, rfl, rfl, rfl, rfl⟩
      case keyword keyword =>
        cases keyword <;> simp only at result
        all_goals try { unfold rejectAt at result; contradiction }
        case fallbackKw =>
          cases result
          exact ⟨_, rfl, rfl, rfl, rfl⟩
      case symbol symbol =>
        cases symbol <;> simp only at result
        all_goals try { unfold rejectAt at result; contradiction }
        case underscore =>
          cases result
          exact ⟨_, rfl, rfl, rfl, rfl⟩

/-- Yul-literal success changes only the cursor by one token. -/
theorem yulLiteral_ok_state_shape {input next : State}
    {literal : YulLiteral}
    (result : yulLiteral input = .ok literal next) :
    next = { input with cursor := input.cursor + 1 } := by
  unfold yulLiteral at result
  cases found : input.peek? with
  | none =>
      simp only [found] at result
      unfold rejectAt at result
      contradiction
  | some token =>
      rcases token with ⟨span, kind⟩
      cases kind <;> simp only [found] at result
      all_goals try { unfold rejectAt at result; contradiction }
      all_goals try { cases result; rfl }
      case keyword keyword =>
        cases keyword <;> simp only at result
        all_goals try { unfold rejectAt at result; contradiction }
        all_goals cases result
        all_goals rfl

/-- Yul-name acceptance preserves its located range and parser-state validity. -/
theorem yulName_ok_validFor {state next : State} {name : YulIdentifier}
    (valid : state.ValidFor) (result : yulName state = .ok name next) :
    name.span.ValidFor state.file ∧ next.ValidFor ∧
      next.file = state.file := by
  unfold yulName at result
  cases found : state.peek? with
  | none =>
      simp only [found] at result
      unfold rejectAt at result
      contradiction
  | some token =>
      rcases token with ⟨span, kind⟩
      cases kind <;> simp only [found] at result
      all_goals try { unfold rejectAt at result; contradiction }
      case identifier text =>
        exact identifier_ok_validFor valid .yulExpression result
      case yulIdentifier text =>
        cases result
        exact advanceAfterYulPeek_validFor valid found
      case keyword keyword =>
        cases keyword <;> simp only at result
        all_goals try { unfold rejectAt at result; contradiction }
        case fallbackKw =>
          cases result
          exact advanceAfterYulPeek_validFor valid found
      case symbol symbol =>
        cases symbol <;> simp only at result
        all_goals try { unfold rejectAt at result; contradiction }
        case underscore =>
          cases result
          exact advanceAfterYulPeek_validFor valid found

/-- Yul-name rejection preserves its source position and parser state. -/
theorem yulName_reject_validFor {state next : State} {failure : Failure}
    (valid : state.ValidFor)
    (result : yulName state = .reject failure next) :
    failure.span.ValidFor state.file ∧ next.ValidFor ∧
      next.file = state.file := by
  unfold yulName at result
  cases found : state.peek? with
  | none =>
      simp only [found] at result
      exact rejectAt_reject_validFor valid _ _ result
  | some token =>
      rcases token with ⟨span, kind⟩
      cases kind <;> simp only [found] at result
      all_goals try { exact rejectAt_reject_validFor valid _ _ result }
      case identifier text =>
        exact identifier_reject_validFor valid .yulExpression result
      case yulIdentifier text => contradiction
      case keyword keyword =>
        cases keyword <;> simp only at result
        all_goals try { exact rejectAt_reject_validFor valid _ _ result }
        case fallbackKw => contradiction
      case symbol symbol =>
        cases symbol <;> simp only at result
        all_goals try { exact rejectAt_reject_validFor valid _ _ result }
        case underscore => contradiction

/-- Yul-literal acceptance preserves its located range and parser state. -/
theorem yulLiteral_ok_validFor {state next : State} {literal : YulLiteral}
    (valid : state.ValidFor) (result : yulLiteral state = .ok literal next) :
    literal.span.ValidFor state.file ∧ next.ValidFor ∧
      next.file = state.file := by
  unfold yulLiteral at result
  cases found : state.peek? with
  | none =>
      simp only [found] at result
      unfold rejectAt at result
      contradiction
  | some token =>
      rcases token with ⟨span, kind⟩
      cases kind <;> simp only [found] at result
      all_goals try { unfold rejectAt at result; contradiction }
      all_goals try { cases result; exact advanceAfterYulPeek_validFor valid found }
      case keyword keyword =>
        cases keyword <;> simp only at result
        all_goals try { unfold rejectAt at result; contradiction }
        all_goals cases result
        all_goals exact advanceAfterYulPeek_validFor valid found

/-- Yul-literal rejection preserves its source position and parser state. -/
theorem yulLiteral_reject_validFor {state next : State} {failure : Failure}
    (valid : state.ValidFor)
    (result : yulLiteral state = .reject failure next) :
    failure.span.ValidFor state.file ∧ next.ValidFor ∧
      next.file = state.file := by
  unfold yulLiteral at result
  cases found : state.peek? with
  | none =>
      simp only [found] at result
      exact rejectAt_reject_validFor valid _ _ result
  | some token =>
      rcases token with ⟨span, kind⟩
      cases kind <;> simp only [found] at result
      all_goals try { exact rejectAt_reject_validFor valid _ _ result }
      all_goals try contradiction
      case keyword keyword =>
        cases keyword <;> simp only at result
        all_goals try { exact rejectAt_reject_validFor valid _ _ result }
        all_goals contradiction

/-- Every accepted Yul name retains a source-valid token range. -/
theorem yulName_validFor : yulName.ValidFor Located.ValidFor := by
  apply Parser.validFor_of_ok_reject
  · intro input inputValid value next result
    exact yulName_ok_validFor inputValid result
  · intro input inputValid failure next result
    exact yulName_reject_validFor inputValid result

/-- Every accepted Yul literal retains a source-valid token range. -/
theorem yulLiteral_validFor : yulLiteral.ValidFor Located.ValidFor := by
  apply Parser.validFor_of_ok_reject
  · intro input inputValid value next result
    exact yulLiteral_ok_validFor inputValid result
  · intro input inputValid failure next result
    exact yulLiteral_reject_validFor inputValid result

/-- Yul-name parsing preserves the immutable token carrier. -/
theorem yulName_preservesTokensOnSuccess :
    Parser.PreservesTokensOnSuccess yulName := by
  intro input name next result
  exact (yulName_ok_state_shape result).choose_spec.2.2.1

/-- Yul-literal parsing preserves the immutable token carrier. -/
theorem yulLiteral_preservesTokensOnSuccess :
    Parser.PreservesTokensOnSuccess yulLiteral := by
  intro input literal next result
  rw [yulLiteral_ok_state_shape result]

/-- Yul-name parsing advances by one token on success. -/
theorem yulName_cursorMonotoneOnSuccess :
    Parser.CursorMonotoneOnSuccess yulName := by
  intro input name next result
  rw [(yulName_ok_state_shape result).choose_spec.2.2.2]
  simp

/-- Yul-literal parsing advances by one token on success. -/
theorem yulLiteral_cursorMonotoneOnSuccess :
    Parser.CursorMonotoneOnSuccess yulLiteral := by
  intro input literal next result
  rw [yulLiteral_ok_state_shape result]
  simp

end Solcore.Syntax.Parser
