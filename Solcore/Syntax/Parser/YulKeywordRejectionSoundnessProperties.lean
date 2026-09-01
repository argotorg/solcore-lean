import Solcore.Syntax.Parser.DeclarativePrimitiveProperties

/-! Exact ordinary rejection facts for required hard-keyword tokens. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Required-keyword rejection is exact absence of that keyword token. -/
theorem keyword_reject_tokenKindAbsentAt (value : HardKeyword)
    (context : ParseContext) {input rejected : State} {failure : Failure}
    (result : keyword value context input = .reject failure rejected) :
    DeclarativeGrammar.TokenKindAbsentAt input.tokens input.window.endIndex
      input.cursor (.keyword value) := by
  rintro ⟨span, inside, found⟩
  unfold keyword acceptToken at result
  unfold State.peek? at result
  simp only [inside, ↓reduceIte, found] at result
  change (if instBEqTokenKind.beq (.keyword value) (.keyword value) then
      Reply.ok _ _ else _) = _ at result
  simp only [instBEqTokenKind.beq] at result
  change (if instBEqHardKeyword.beq value value then Reply.ok _ _ else _) = _
    at result
  unfold instBEqHardKeyword.beq at result
  cases value <;> contradiction

/-- Required-keyword rejection retains the complete input state. -/
theorem keyword_reject_state_eq (value : HardKeyword)
    (context : ParseContext) {input rejected : State} {failure : Failure}
    (result : keyword value context input = .reject failure rejected) :
    rejected = input :=
  acceptToken_reject_state_shape (.keyword value) context
    (· == .keyword value) result

end Solcore.Syntax.Parser
