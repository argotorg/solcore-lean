import Solcore.Syntax.DeclarativeYulStatementOrdinaryRecoveryGrammar
import Solcore.Syntax.Parser.DelimitedRejectionPrimitiveProperties
import Solcore.Syntax.Parser.Yul.Statement

/-! Exact ordinary-success reflection for outer Yul-statement recovery. -/

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

private theorem yulStatementRejects_of_rightBrace {input : State}
    (present : isSymbol input .rightBrace = true) :
    DeclarativeGrammar.YulStatementRejects input.declarativeRemainder
      input.declarativeRemainder := by
  rcases symbol_eq_ok_of_isSymbol_eq_true .rightBrace .yulStatement present
      with ⟨token, parsed⟩
  exact .rightBrace
    (symbol_ok_tokenAt .rightBrace .yulStatement parsed).1

/-- An executable statement boundary gives exact declarative rejection. -/
theorem yulStatementRejects_of_boundary (input : State)
    (boundary : (input.atEnd || isSymbol input .rightBrace) = true) :
    DeclarativeGrammar.YulStatementRejects input.declarativeRemainder
      input.declarativeRemainder := by
  by_cases atEnd : input.window.endIndex ≤ input.cursor
  · exact .windowEnd atEnd
  · have notAtEnd : input.atEnd = false := by
      unfold State.atEnd
      exact decide_eq_false atEnd
    have rightBrace : isSymbol input .rightBrace = true := by
      simpa [notAtEnd] using boundary
    exact yulStatementRejects_of_rightBrace rightBrace

/-- Failure to advance is an end or missing-token statement boundary. -/
theorem yulStatementRejects_of_advance?_eq_none
    (input : State) (advanced : input.advance? = none) :
    DeclarativeGrammar.YulStatementRejects input.declarativeRemainder
      input.declarativeRemainder := by
  by_cases atEnd : input.window.endIndex ≤ input.cursor
  · exact .windowEnd atEnd
  · have inside : input.cursor < input.window.endIndex := by omega
    apply DeclarativeGrammar.YulStatementRejects.missingToken inside
    unfold State.advance? State.peek? at advanced
    simpa [State.declarativeRemainder, inside] using advanced

/-- A present non-boundary token continues statement recovery. -/
theorem no_yulStatementRejects_of_nonBoundary_token
    {input : State} {token : Token}
    (boundary : (input.atEnd || isSymbol input .rightBrace) = false)
    (found : input.peek? = some token) :
    ¬ DeclarativeGrammar.YulStatementRejects input.declarativeRemainder
      input.declarativeRemainder := by
  intro rejected
  have current := tokenAt_of_peek?_eq_some found
  cases rejected with
  | windowEnd atEnd =>
      change input.window.endIndex ≤ input.cursor at atEnd
      have inside := State.cursor_lt_endIndex_of_peek?_eq_some found
      omega
  | rightBrace rightBraceToken =>
      have present := isSymbol_eq_true_of_tokenAt .rightBrace rightBraceToken
      simp [present] at boundary
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

/-- Every successful executable statement-recovery scan follows the exact
boundary-prioritized declarative scan. -/
theorem recoverYulStatementAux_success_ordinary_sound (first : SourceSpan) :
    ∀ fuel last input statement output,
      recoverYulStatementAux first last fuel input = .ok statement output →
      DeclarativeGrammar.YulStatementRecoveryScanParses first last
        input.declarativeRemainder statement output.declarativeRemainder := by
  intro fuel
  induction fuel with
  | zero =>
      intro last input statement output result
      simp [recoverYulStatementAux] at result
  | succ fuel inductionHypothesis =>
      intro last input statement output result
      unfold recoverYulStatementAux at result
      by_cases boundary :
          (input.atEnd || isSymbol input .rightBrace) = true
      · simp only [boundary, if_true] at result
        unfold finishRecoveredYulStatement at result
        cases result
        exact .stop (yulStatementRejects_of_boundary input boundary)
      · have boundaryFalse :
            (input.atEnd || isSymbol input .rightBrace) = false :=
          Bool.eq_false_iff.mpr boundary
        simp only [boundaryFalse, Bool.false_eq_true, if_false] at result
        cases advanced : input.advance? with
        | none =>
            simp only [advanced] at result
            unfold finishRecoveredYulStatement at result
            cases result
            exact .stop
              (yulStatementRejects_of_advance?_eq_none input advanced)
        | some pair =>
            rcases pair with ⟨token, next⟩
            simp only [advanced] at result
            rcases advance?_state_shape advanced with ⟨found, nextEq⟩
            have tail := inductionHypothesis token.span next statement output
              result
            have current := tokenAt_of_peek?_eq_some found
            have continues := no_yulStatementRejects_of_nonBoundary_token
              boundaryFalse found
            rw [nextEq] at tail
            exact .next continues current tail

end Solcore.Syntax.Parser
