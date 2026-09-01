import Solcore.Syntax.DeclarativeCoreLiteralOutcomeProperties
import Solcore.Syntax.Parser.CoreExpressionAtomLeafSoundnessProperties

/-! Exact executable ordinary outcomes for Core literal leaves. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

private theorem rejectAt_rejected_state_eq {alpha : Type}
    {input rejected : State} {failure : Failure}
    {expected : NonemptyList ParseExpectation} {context : ParseContext}
    (result : (rejectAt input expected context : Reply alpha) =
      .reject failure rejected) : rejected = input := by
  unfold rejectAt at result
  cases result
  rfl

private theorem bind_pure_reject_first {alpha beta : Type}
    {first : Parser alpha} {finish : alpha → beta}
    {input rejected : State} {failure : Failure}
    (result : (first >>= fun value => pure (finish value)) input =
      .reject failure rejected) :
    first input = .reject failure rejected := by
  change (match first input with
    | .ok value afterFirst =>
        (pure (finish value) : Parser beta) afterFirst
    | .reject firstFailure firstRejected =>
        Reply.reject firstFailure firstRejected
    | .invariant error => Reply.invariant error) =
      Reply.reject failure rejected at result
  cases firstResult : first input with
  | ok value afterFirst => rw [firstResult] at result; contradiction
  | invariant error => rw [firstResult] at result; contradiction
  | reject firstFailure firstRejected =>
      rw [firstResult] at result
      cases result
      rfl

/-- Core-literal rejection returns the complete input state unchanged. -/
theorem coreLiteral_reject_state_eq {input rejected : State}
    {failure : Failure}
    (result : coreLiteral input = .reject failure rejected) :
    rejected = input := by
  unfold coreLiteral at result
  cases found : input.peek? with
  | none =>
      simp only [found] at result
      exact rejectAt_rejected_state_eq result
  | some token =>
      rcases token with ⟨span, kind⟩
      cases kind <;> simp only [found] at result
      all_goals try { exact rejectAt_rejected_state_eq result }
      all_goals contradiction

/-- Core-literal rejection proves absence of every admitted literal token. -/
theorem coreLiteral_reject_coreLiteralAbsentAt
    {input rejected : State} {failure : Failure}
    (result : coreLiteral input = .reject failure rejected) :
    DeclarativeGrammar.CoreLiteralAbsentAt input.declarativeRemainder := by
  constructor
  · rintro ⟨span, spelling, inside, atCursor⟩
    have found : input.peek? = some {
        span
        value := TokenKind.decimalLiteral spelling
      } := by
      unfold State.peek?
      change input.cursor < input.window.endIndex at inside
      change input.tokens[input.cursor]? = some {
        span
        value := TokenKind.decimalLiteral spelling
      } at atCursor
      simp only [inside, ↓reduceIte, atCursor]
    unfold coreLiteral at result
    simp [found] at result
  constructor
  · rintro ⟨span, spelling, inside, atCursor⟩
    have found : input.peek? = some {
        span
        value := TokenKind.hexadecimalLiteral spelling
      } := by
      unfold State.peek?
      change input.cursor < input.window.endIndex at inside
      change input.tokens[input.cursor]? = some {
        span
        value := TokenKind.hexadecimalLiteral spelling
      } at atCursor
      simp only [inside, ↓reduceIte, atCursor]
    unfold coreLiteral at result
    simp [found] at result
  · rintro ⟨span, spelling, inside, atCursor⟩
    have found : input.peek? = some {
        span
        value := TokenKind.stringLiteral spelling
      } := by
      unfold State.peek?
      change input.cursor < input.window.endIndex at inside
      change input.tokens[input.cursor]? = some {
        span
        value := TokenKind.stringLiteral spelling
      } at atCursor
      simp only [inside, ↓reduceIte, atCursor]
    unfold coreLiteral at result
    simp [found] at result

/-- Every executable Core-literal rejection is exact and non-consuming. -/
theorem coreLiteral_reject_ordinary_sound
    {input rejected : State} {failure : Failure}
    (result : coreLiteral input = .reject failure rejected) :
    DeclarativeGrammar.CoreLiteralRejects input.declarativeRemainder
      rejected.declarativeRemainder := by
  have rejectedEq := coreLiteral_reject_state_eq result
  subst rejected
  exact .absent (coreLiteral_reject_coreLiteralAbsentAt result)

/-- A positive Core-literal guard cannot enter the rejection path. -/
theorem coreLiteral_ne_reject_of_isCoreLiteral_eq_true
    {input rejected : State} {failure : Failure}
    (starts : isCoreLiteral input = true)
    (result : coreLiteral input = .reject failure rejected) : False := by
  unfold isCoreLiteral State.peekKind? at starts
  unfold coreLiteral at result
  cases found : input.peek? with
  | none => simp [found] at starts
  | some token =>
      rcases token with ⟨span, kind⟩
      cases kind <;> simp only [found, Option.map_some] at starts result
      all_goals contradiction

/-- Package unconditional Core-literal success with exact rejection. -/
theorem coreLiteral_ordinaryOutcome_sound :
    (∀ {input output : State} {literal : CoreLiteral},
      coreLiteral input = .ok literal output →
        DeclarativeGrammar.CoreLiteralOrdinaryParses
          input.declarativeRemainder literal output.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      coreLiteral input = .reject failure rejected →
        DeclarativeGrammar.CoreLiteralRejects input.declarativeRemainder
          rejected.declarativeRemainder) :=
  ⟨coreLiteral_success_sound, coreLiteral_reject_ordinary_sound⟩

/-- Re-export the deterministic Core-literal outcome at its executable
boundary. -/
theorem coreLiteral_ordinaryOutcomeSpec :
    DeclarativeGrammar.DeterministicOutcomeSpec
      DeclarativeGrammar.CoreLiteralOrdinaryParses
      DeclarativeGrammar.CoreLiteralRejects :=
  DeclarativeGrammar.coreLiteralDeterministicOutcomeSpec

namespace ExpressionAtomInternals

/-- Literal-expression rejection returns the complete input state unchanged. -/
theorem literalExpression_reject_state_eq
    {input rejected : State} {failure : Failure}
    (result : literalExpression input = .reject failure rejected) :
    rejected = input := by
  unfold literalExpression at result
  have literalResult : coreLiteral input = .reject failure rejected :=
    bind_pure_reject_first result
  exact coreLiteral_reject_state_eq literalResult

/-- Every literal-expression rejection is its primitive literal rejection. -/
theorem literalExpression_reject_ordinary_sound
    {input rejected : State} {failure : Failure}
    (result : literalExpression input = .reject failure rejected) :
    DeclarativeGrammar.LiteralExpressionRejects input.declarativeRemainder
      rejected.declarativeRemainder := by
  unfold literalExpression at result
  have literalResult : coreLiteral input = .reject failure rejected :=
    bind_pure_reject_first result
  have rejectedEq := literalExpression_reject_state_eq result
  subst rejected
  exact .absent (coreLiteral_reject_coreLiteralAbsentAt literalResult)

/-- A positive literal guard also excludes wrapper-level rejection. -/
theorem literalExpression_ne_reject_of_isCoreLiteral_eq_true
    {input rejected : State} {failure : Failure}
    (starts : isCoreLiteral input = true)
    (result : literalExpression input = .reject failure rejected) : False := by
  unfold literalExpression at result
  have literalResult : coreLiteral input = .reject failure rejected :=
    bind_pure_reject_first result
  exact coreLiteral_ne_reject_of_isCoreLiteral_eq_true starts literalResult

/-- Package literal-expression success with exact primitive rejection. -/
theorem literalExpression_ordinaryOutcome_sound :
    (∀ {input output : State} {expression : Expr},
      literalExpression input = .ok expression output →
        DeclarativeGrammar.LiteralExpressionOrdinaryParses
          input.declarativeRemainder expression output.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      literalExpression input = .reject failure rejected →
        DeclarativeGrammar.LiteralExpressionRejects
          input.declarativeRemainder rejected.declarativeRemainder) :=
  ⟨literalExpression_success_sound,
    literalExpression_reject_ordinary_sound⟩

/-- Re-export the deterministic literal-expression outcome at its executable
boundary. -/
theorem literalExpression_ordinaryOutcomeSpec :
    DeclarativeGrammar.DeterministicOutcomeSpec
      DeclarativeGrammar.LiteralExpressionOrdinaryParses
      DeclarativeGrammar.LiteralExpressionRejects :=
  DeclarativeGrammar.literalExpressionDeterministicOutcomeSpec

end ExpressionAtomInternals

end Solcore.Syntax.Parser
