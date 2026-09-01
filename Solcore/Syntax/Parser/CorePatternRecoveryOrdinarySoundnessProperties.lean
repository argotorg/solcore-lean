import Solcore.Syntax.DeclarativeCorePatternRecoveryOutcomeProperties
import Solcore.Syntax.Parser.DelimitedRejectionPrimitiveProperties
import Solcore.Syntax.Parser.Pattern

/-! Exact ordinary-success reflection for Core pattern recovery scans. -/

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

private theorem tokenAt_of_isSymbol_eq_true (value : Symbol)
    {input : State} (present : isSymbol input value = true) :
    ∃ span, DeclarativeGrammar.TokenAt input.tokens input.window.endIndex
      input.cursor { span, value := .symbol value } := by
  rcases symbol_eq_ok_of_isSymbol_eq_true value .pattern present with
    ⟨token, parsed⟩
  exact ⟨token.span, (symbol_ok_tokenAt value .pattern parsed).1⟩

namespace PatternInternals

/-- A true executable boundary guard gives its exact declarative stop. -/
theorem patternRecoveryStops_of_isPatternBoundary
    (input : State) (boundary : isPatternBoundary input = true) :
    DeclarativeGrammar.PatternRecoveryStops
      input.declarativeRemainder input.declarativeRemainder := by
  by_cases atEnd : input.window.endIndex ≤ input.cursor
  · exact .windowEnd atEnd
  · have atEndFalse : input.atEnd = false := by
      unfold State.atEnd
      exact decide_eq_false atEnd
    by_cases comma : isSymbol input .comma = true
    · exact .comma (tokenAt_of_isSymbol_eq_true .comma comma).choose_spec
    · have commaFalse := Bool.eq_false_iff.mpr comma
      by_cases rightParen : isSymbol input .rightParen = true
      · exact .rightParen
          (tokenAt_of_isSymbol_eq_true .rightParen rightParen).choose_spec
      · have rightParenFalse := Bool.eq_false_iff.mpr rightParen
        by_cases fatArrow : isSymbol input .fatArrow = true
        · exact .fatArrow
            (tokenAt_of_isSymbol_eq_true .fatArrow fatArrow).choose_spec
        · have fatArrowFalse := Bool.eq_false_iff.mpr fatArrow
          by_cases pipe : isSymbol input .pipe = true
          · exact .pipe
              (tokenAt_of_isSymbol_eq_true .pipe pipe).choose_spec
          · have pipeFalse := Bool.eq_false_iff.mpr pipe
            have rightBrace : isSymbol input .rightBrace = true := by
              simpa [isPatternBoundary, atEndFalse, commaFalse,
                rightParenFalse, fatArrowFalse, pipeFalse] using boundary
            exact .rightBrace
              (tokenAt_of_isSymbol_eq_true .rightBrace rightBrace).choose_spec

/-- Failed advancement is the exact window-end or missing-carrier stop. -/
theorem patternRecoveryStops_of_advance?_eq_none
    (input : State) (advanced : input.advance? = none) :
    DeclarativeGrammar.PatternRecoveryStops
      input.declarativeRemainder input.declarativeRemainder := by
  by_cases atEnd : input.window.endIndex ≤ input.cursor
  · exact .windowEnd atEnd
  · have inside : input.cursor < input.window.endIndex := by omega
    apply DeclarativeGrammar.PatternRecoveryStops.missingToken inside
    unfold State.advance? State.peek? at advanced
    simpa [State.declarativeRemainder, inside] using advanced

/-- A present non-boundary token selects continuation, never scan stop. -/
theorem no_patternRecoveryStops_of_nonBoundary_token
    {input : State} {token : Token}
    (boundary : isPatternBoundary input = false)
    (found : input.peek? = some token) :
    ¬ DeclarativeGrammar.PatternRecoveryStops
      input.declarativeRemainder input.declarativeRemainder := by
  intro stops
  have current := tokenAt_of_peek?_eq_some found
  cases stops with
  | windowEnd atEnd =>
      exact Nat.not_lt_of_ge atEnd
        (State.cursor_lt_endIndex_of_peek?_eq_some found)
  | comma present =>
      have guard : isSymbol input .comma = true :=
        isSymbol_eq_true_of_tokenAt .comma (by
          simpa [State.declarativeRemainder] using present)
      simp [isPatternBoundary, guard] at boundary
  | rightParen present =>
      have guard : isSymbol input .rightParen = true :=
        isSymbol_eq_true_of_tokenAt .rightParen (by
          simpa [State.declarativeRemainder] using present)
      simp [isPatternBoundary, guard] at boundary
  | fatArrow present =>
      have guard : isSymbol input .fatArrow = true :=
        isSymbol_eq_true_of_tokenAt .fatArrow (by
          simpa [State.declarativeRemainder] using present)
      simp [isPatternBoundary, guard] at boundary
  | pipe present =>
      have guard : isSymbol input .pipe = true :=
        isSymbol_eq_true_of_tokenAt .pipe (by
          simpa [State.declarativeRemainder] using present)
      simp [isPatternBoundary, guard] at boundary
  | rightBrace present =>
      have guard : isSymbol input .rightBrace = true :=
        isSymbol_eq_true_of_tokenAt .rightBrace (by
          simpa [State.declarativeRemainder] using present)
      simp [isPatternBoundary, guard] at boundary
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

/-- Every successful executable auxiliary scan follows the exact relation. -/
theorem recoverPatternAux_success_ordinary_sound (first : SourceSpan) :
    ∀ fuel last input pattern output,
      recoverPatternAux first last fuel input = .ok pattern output →
      DeclarativeGrammar.PatternRecoveryScanParses first last
        input.declarativeRemainder pattern output.declarativeRemainder := by
  intro fuel
  induction fuel with
  | zero =>
      intro last input pattern output result
      simp [recoverPatternAux] at result
  | succ fuel inductionHypothesis =>
      intro last input pattern output result
      unfold recoverPatternAux at result
      by_cases boundary : isPatternBoundary input = true
      · simp only [boundary, if_true] at result
        unfold finishRecoveredPattern at result
        cases result
        exact .stop (patternRecoveryStops_of_isPatternBoundary input boundary)
      · have boundaryFalse : isPatternBoundary input = false :=
          Bool.eq_false_iff.mpr boundary
        simp only [boundaryFalse, Bool.false_eq_true, if_false] at result
        cases advanced : input.advance? with
        | none =>
            simp only [advanced] at result
            unfold finishRecoveredPattern at result
            cases result
            exact .stop
              (patternRecoveryStops_of_advance?_eq_none input advanced)
        | some pair =>
            rcases pair with ⟨token, next⟩
            simp only [advanced] at result
            rcases advance?_state_shape advanced with ⟨found, nextEq⟩
            have tail := inductionHypothesis token.span next pattern output
              result
            rw [nextEq] at tail
            exact .next
              (no_patternRecoveryStops_of_nonBoundary_token boundaryFalse
                found)
              (tokenAt_of_peek?_eq_some found) tail

end PatternInternals

end Solcore.Syntax.Parser
