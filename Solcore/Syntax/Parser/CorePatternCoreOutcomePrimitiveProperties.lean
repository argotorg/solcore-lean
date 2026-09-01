import Solcore.Syntax.Parser.CoreExpressionAtomDispatcherLookaheadProperties
import Solcore.Syntax.Parser.CorePatternDispatcherLookaheadProperties
import Solcore.Syntax.Parser.CoreTypeOutcomePrimitiveProperties
import Solcore.Syntax.Parser.DelimitedRejectionPrimitiveProperties

/-! Positive lookahead bridges for exact `patternCore` branch selection. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.PatternInternals

/-- A positive symbol guard exposes the exact current marker token. -/
theorem symbolTokenAt_of_isSymbol_eq_true (value : Symbol)
    {input : State} (present : isSymbol input value = true) :
    ∃ span, DeclarativeGrammar.TokenAt input.tokens input.window.endIndex
      input.cursor { span, value := .symbol value } := by
  rcases symbol_eq_ok_of_isSymbol_eq_true value .pattern present with
    ⟨token, parsed⟩
  exact ⟨token.span,
    (symbol_success_exactTokenParses value .pattern parsed).1⟩

/-- A positive literal guard exposes one exact admitted literal token. -/
theorem coreLiteralStartsAt_of_isCoreLiteral_eq_true {input : State}
    (present : isCoreLiteral input = true) :
    DeclarativeGrammar.CoreLiteralStartsAt
      input.declarativeRemainder := by
  unfold isCoreLiteral State.peekKind? at present
  cases found : input.peek? with
  | none => simp [found] at present
  | some token =>
      rcases token with ⟨span, kind⟩
      cases kind <;> simp only [found, Option.map_some] at present
      all_goals try { contradiction }
      case decimalLiteral spelling =>
        exact Or.inl ⟨span, spelling, tokenAt_of_peek?_eq_some found⟩
      case hexadecimalLiteral spelling =>
        exact Or.inr (Or.inl
          ⟨span, spelling, tokenAt_of_peek?_eq_some found⟩)
      case stringLiteral spelling =>
        exact Or.inr (Or.inr
          ⟨span, spelling, tokenAt_of_peek?_eq_some found⟩)

/-- A positive Boolean guard exposes the exact hard-keyword token. -/
theorem booleanPatternStartsAt_of_isBooleanValue_eq_true {input : State}
    (present : isBooleanValue input = true) :
    DeclarativeGrammar.BooleanPatternStartsAt
      input.declarativeRemainder := by
  rcases Bool.or_eq_true_iff.mp (by
      simpa only [isBooleanValue] using present) with truePresent |
        falsePresent
  · rcases keyword_eq_ok_of_isKeyword_eq_true .trueKw .pattern
        truePresent with ⟨token, parsed⟩
    exact Or.inl ⟨token.span,
      (keyword_success_exactTokenParses .trueKw .pattern parsed).1⟩
  · rcases keyword_eq_ok_of_isKeyword_eq_true .falseKw .pattern
        falsePresent with ⟨token, parsed⟩
    exact Or.inr ⟨token.span,
      (keyword_success_exactTokenParses .falseKw .pattern parsed).1⟩

/-- A positive contextual guard exposes its exact identifier token. -/
theorem contextualTokenAt_of_isContextual_eq_true
    (value : ContextualKeyword) {input : State}
    (present : isContextual input value = true) :
    ∃ span, DeclarativeGrammar.TokenAt input.tokens input.window.endIndex
      input.cursor { span, value := .identifier value.spelling } := by
  rcases contextual_eq_ok_of_isContextual_eq_true value .pattern present with
    ⟨token, parsed⟩
  exact ⟨token.span,
    (contextual_success_exactTokenParses value .pattern parsed).1⟩

end Solcore.Syntax.Parser.PatternInternals
