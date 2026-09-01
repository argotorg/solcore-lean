import Solcore.Syntax.Parser.YulExpressionCoreFinalRejectionProperties
import Solcore.Syntax.Parser.YulExpressionRejectionSoundnessProperties

/-! Exact ordinary-success reflection for inline-Yul expression recovery. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

private theorem isSymbol_eq_true_of_tokenAt (value : Symbol)
    {input : State} {span : SourceSpan}
    (token : DeclarativeGrammar.TokenAt input.tokens input.window.endIndex
      input.cursor { span, value := .symbol value }) :
    isSymbol input value = true := by
  unfold isSymbol State.peekKind? State.peek?
  simp only [token.1, ↓reduceIte, token.2, Option.map_some]
  cases value <;> rfl

private theorem yulExpressionRejects_of_symbol
    (value : Symbol) {input : State}
    (allowed : value = .comma ∨ value = .rightParen ∨ value = .rightBrace)
    (present : isSymbol input value = true) :
    DeclarativeGrammar.YulExpressionRejects input.declarativeRemainder
      input.declarativeRemainder := by
  rcases symbol_eq_ok_of_isSymbol_eq_true value .yulExpression present with
    ⟨token, parsed⟩
  have exactToken := (symbol_ok_tokenAt value .yulExpression parsed).1
  rcases allowed with rfl | rfl | rfl
  · exact .comma exactToken
  · exact .rightParen exactToken
  · exact .rightBrace exactToken

private theorem yulExpressionRejects_of_isBoundary
    (input : State)
    (boundary : YulExpressionInternals.isBoundary input = true) :
    DeclarativeGrammar.YulExpressionRejects input.declarativeRemainder
      input.declarativeRemainder := by
  by_cases atEnd : input.window.endIndex ≤ input.cursor
  · exact .windowEnd atEnd
  · by_cases comma : isSymbol input .comma = true
    · exact yulExpressionRejects_of_symbol .comma (Or.inl rfl) comma
    · by_cases rightParen : isSymbol input .rightParen = true
      · exact yulExpressionRejects_of_symbol .rightParen
          (Or.inr (Or.inl rfl)) rightParen
      · by_cases rightBrace : isSymbol input .rightBrace = true
        · exact yulExpressionRejects_of_symbol .rightBrace
            (Or.inr (Or.inr rfl)) rightBrace
        · have notAtEnd : input.atEnd = false := by
            unfold State.atEnd
            exact decide_eq_false atEnd
          have commaFalse : isSymbol input .comma = false :=
            Bool.eq_false_iff.mpr comma
          have rightParenFalse : isSymbol input .rightParen = false :=
            Bool.eq_false_iff.mpr rightParen
          have rightBraceFalse : isSymbol input .rightBrace = false :=
            Bool.eq_false_iff.mpr rightBrace
          simp [YulExpressionInternals.isBoundary, notAtEnd, commaFalse,
            rightParenFalse, rightBraceFalse] at boundary

private theorem yulExpressionRejects_of_advance?_eq_none
    (input : State) (advanced : input.advance? = none) :
    DeclarativeGrammar.YulExpressionRejects input.declarativeRemainder
      input.declarativeRemainder := by
  by_cases atEnd : input.window.endIndex ≤ input.cursor
  · exact .windowEnd atEnd
  · have inside : input.cursor < input.window.endIndex := by omega
    apply DeclarativeGrammar.YulExpressionRejects.missingToken inside
    unfold State.advance? State.peek? at advanced
    simpa [State.declarativeRemainder, inside] using advanced

/-- A present non-boundary token selects recovery continuation rather than a
stop constructor. -/
theorem no_yulExpressionRejects_of_nonBoundary_token
    {input : State} {token : Token}
    (boundary : YulExpressionInternals.isBoundary input = false)
    (found : input.peek? = some token) :
    ¬ DeclarativeGrammar.YulExpressionRejects input.declarativeRemainder
      input.declarativeRemainder := by
  intro rejected
  have current := tokenAt_of_peek?_eq_some found
  cases rejected with
  | windowEnd atEnd =>
      change input.window.endIndex ≤ input.cursor at atEnd
      have inside := State.cursor_lt_endIndex_of_peek?_eq_some found
      omega
  | comma commaToken =>
      have present := isSymbol_eq_true_of_tokenAt .comma commaToken
      simp [YulExpressionInternals.isBoundary, present] at boundary
  | rightParen rightParenToken =>
      have present := isSymbol_eq_true_of_tokenAt .rightParen rightParenToken
      simp [YulExpressionInternals.isBoundary, present] at boundary
  | rightBrace rightBraceToken =>
      have present := isSymbol_eq_true_of_tokenAt .rightBrace rightBraceToken
      simp [YulExpressionInternals.isBoundary, present] at boundary
  | missingToken inside missing =>
      change input.tokens[input.cursor]? = none at missing
      rw [current.2] at missing
      contradiction

private theorem advance?_state_shape {input next : State} {token : Token}
    (advanced : input.advance? = some (token, next)) :
    input.peek? = some token ∧
      next = { input with cursor := input.cursor + 1 } := by
  unfold State.advance? at advanced
  cases found : input.peek? with
  | none => simp [found] at advanced
  | some current =>
      simp only [found, Option.map_some] at advanced
      cases advanced
      exact ⟨rfl, rfl⟩

namespace YulExpressionInternals

/-- Every successful recovery execution follows the exact boundary-prioritized
scan relation. -/
theorem recoverAux_success_ordinary_sound (first : SourceSpan) :
    ∀ fuel last input expression output,
      recoverAux first last fuel input = .ok expression output →
      DeclarativeGrammar.YulExpressionRecoveryScanParses first last
        input.declarativeRemainder expression output.declarativeRemainder := by
  intro fuel
  induction fuel with
  | zero =>
      intro last input expression output result
      simp [recoverAux] at result
  | succ fuel inductionHypothesis =>
      intro last input expression output result
      unfold recoverAux at result
      by_cases boundary : isBoundary input = true
      · simp only [boundary, if_true] at result
        unfold finishRecovered at result
        cases result
        exact .stop (yulExpressionRejects_of_isBoundary input boundary)
      · have boundaryFalse : isBoundary input = false :=
          Bool.eq_false_iff.mpr boundary
        simp only [boundaryFalse, Bool.false_eq_true, if_false] at result
        cases advanced : input.advance? with
        | none =>
            simp only [advanced] at result
            unfold finishRecovered at result
            cases result
            exact .stop (yulExpressionRejects_of_advance?_eq_none input
              advanced)
        | some pair =>
            rcases pair with ⟨token, next⟩
            simp only [advanced] at result
            rcases advance?_state_shape advanced with ⟨found, nextEq⟩
            have tail := inductionHypothesis token.span next expression output
              result
            have current := tokenAt_of_peek?_eq_some found
            have continues := no_yulExpressionRejects_of_nonBoundary_token
              boundaryFalse found
            rw [nextEq] at tail
            exact .next continues current tail

end YulExpressionInternals

end Solcore.Syntax.Parser
