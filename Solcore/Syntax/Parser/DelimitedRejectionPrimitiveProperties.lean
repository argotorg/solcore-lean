import Solcore.Syntax.Parser.DeclarativePrimitiveProperties

/-! Primitive facts used by ordinary-rejection reflection. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Positive symbol lookahead determines the following symbol parse exactly. -/
theorem symbol_eq_ok_of_isSymbol_eq_true (value : Symbol)
    (context : ParseContext) {input : State}
    (present : isSymbol input value = true) :
    ∃ token, symbol value context input =
      .ok token { input with cursor := input.cursor + 1 } := by
  unfold isSymbol State.peekKind? at present
  cases found : input.peek? with
  | none => simp [found] at present
  | some token =>
      simp only [found, Option.map_some] at present
      change (token.value == .symbol value) = true at present
      refine ⟨token, ?_⟩
      unfold symbol acceptToken
      simp only [found, present, ↓reduceIte]

/-- Ordinary symbol rejection is exact evidence that the symbol is absent. -/
theorem symbol_reject_tokenKindAbsentAt (value : Symbol)
    (context : ParseContext) {input rejected : State} {failure : Failure}
    (result : symbol value context input = .reject failure rejected) :
    DeclarativeGrammar.TokenKindAbsentAt input.tokens input.window.endIndex
      input.cursor (.symbol value) := by
  by_cases present : isSymbol input value = true
  · rcases symbol_eq_ok_of_isSymbol_eq_true value context present with
      ⟨token, parsed⟩
    rw [parsed] at result
    contradiction
  · exact symbolAbsentAt_of_isSymbol_eq_false value
      (Bool.eq_false_iff.mpr present)

/-- Ordinary symbol rejection retains the complete input state. -/
theorem symbol_reject_state_eq (value : Symbol) (context : ParseContext)
    {input rejected : State} {failure : Failure}
    (result : symbol value context input = .reject failure rejected) :
    rejected = input :=
  acceptToken_reject_state_shape (.symbol value) context
    (· == .symbol value) result

end Solcore.Syntax.Parser
