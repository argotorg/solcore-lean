import Solcore.Syntax.DeclarativeCoreExpressionAtomRecoveryProperties
import Solcore.Syntax.Parser.DelimitedRejectionPrimitiveProperties
import Solcore.Syntax.Parser.Expression.Atom

/-! Exact ordinary-outcome reflection for Core expression-atom recovery. -/

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

private theorem isKeyword_eq_true_of_tokenAt (value : HardKeyword)
    {input : State} {span : SourceSpan}
    (token : DeclarativeGrammar.TokenAt input.tokens input.window.endIndex
      input.cursor { span, value := .keyword value }) :
    isKeyword input value = true := by
  unfold isKeyword State.peekKind? State.peek?
  simp only [token.1, ↓reduceIte, token.2, Option.map_some]
  change instBEqTokenKind.beq (.keyword value) (.keyword value) = true
  simp only [instBEqTokenKind.beq]
  change instBEqHardKeyword.beq value value = true
  unfold instBEqHardKeyword.beq
  cases value <;> rfl

private theorem tokenAt_of_isSymbol_eq_true (value : Symbol)
    {input : State} (present : isSymbol input value = true) :
    ∃ span, DeclarativeGrammar.TokenAt input.tokens input.window.endIndex
      input.cursor { span, value := .symbol value } := by
  rcases symbol_eq_ok_of_isSymbol_eq_true value .expression present with
    ⟨token, parsed⟩
  exact ⟨token.span, (symbol_ok_tokenAt value .expression parsed).1⟩

private theorem tokenAt_of_isKeyword_eq_true (value : HardKeyword)
    {input : State} (present : isKeyword input value = true) :
    ∃ span, DeclarativeGrammar.TokenAt input.tokens input.window.endIndex
      input.cursor { span, value := .keyword value } := by
  unfold isKeyword State.peekKind? at present
  cases found : input.peek? with
  | none => simp [found] at present
  | some token =>
      simp only [found, Option.map_some] at present
      change (token.value == .keyword value) = true at present
      have parsed : keyword value .expression input =
          .ok token { input with cursor := input.cursor + 1 } := by
        unfold keyword acceptToken
        simp only [found, present, ↓reduceIte]
      exact ⟨token.span, (keyword_ok_tokenAt value .expression parsed).1⟩

namespace ExpressionAtomInternals

/-- A true executable boundary guard gives its exact declarative stop. -/
theorem expressionAtomRecoveryStops_of_isAtomBoundary
    (input : State) (boundary : isAtomBoundary input = true) :
    DeclarativeGrammar.ExpressionAtomRecoveryStops
      input.declarativeRemainder input.declarativeRemainder := by
  by_cases atEnd : input.window.endIndex ≤ input.cursor
  · exact .windowEnd atEnd
  · have atEndFalse : input.atEnd = false := by
      unfold State.atEnd
      exact decide_eq_false atEnd
    by_cases semicolon : isSymbol input .semicolon = true
    · exact .semicolon (tokenAt_of_isSymbol_eq_true .semicolon semicolon).choose_spec
    · have semicolonFalse := Bool.eq_false_iff.mpr semicolon
      by_cases comma : isSymbol input .comma = true
      · exact .comma (tokenAt_of_isSymbol_eq_true .comma comma).choose_spec
      · have commaFalse := Bool.eq_false_iff.mpr comma
        by_cases rightParen : isSymbol input .rightParen = true
        · exact .rightParen
            (tokenAt_of_isSymbol_eq_true .rightParen rightParen).choose_spec
        · have rightParenFalse := Bool.eq_false_iff.mpr rightParen
          by_cases rightBracket : isSymbol input .rightBracket = true
          · exact .rightBracket
              (tokenAt_of_isSymbol_eq_true .rightBracket rightBracket).choose_spec
          · have rightBracketFalse := Bool.eq_false_iff.mpr rightBracket
            by_cases rightBrace : isSymbol input .rightBrace = true
            · exact .rightBrace
                (tokenAt_of_isSymbol_eq_true .rightBrace rightBrace).choose_spec
            · have rightBraceFalse := Bool.eq_false_iff.mpr rightBrace
              by_cases question : isSymbol input .question = true
              · exact .question
                  (tokenAt_of_isSymbol_eq_true .question question).choose_spec
              · have questionFalse := Bool.eq_false_iff.mpr question
                by_cases colon : isSymbol input .colon = true
                · exact .colon
                    (tokenAt_of_isSymbol_eq_true .colon colon).choose_spec
                · have colonFalse := Bool.eq_false_iff.mpr colon
                  by_cases fatArrow : isSymbol input .fatArrow = true
                  · exact .fatArrow
                      (tokenAt_of_isSymbol_eq_true .fatArrow fatArrow).choose_spec
                  · have fatArrowFalse := Bool.eq_false_iff.mpr fatArrow
                    by_cases pipe : isSymbol input .pipe = true
                    · exact .pipe
                        (tokenAt_of_isSymbol_eq_true .pipe pipe).choose_spec
                    · have pipeFalse := Bool.eq_false_iff.mpr pipe
                      have elseKeyword : isKeyword input .elseKw = true := by
                        simpa [isAtomBoundary, atEndFalse, semicolonFalse,
                          commaFalse, rightParenFalse, rightBracketFalse,
                          rightBraceFalse, questionFalse, colonFalse,
                          fatArrowFalse, pipeFalse] using boundary
                      exact .elseKeyword
                        (tokenAt_of_isKeyword_eq_true .elseKw
                          elseKeyword).choose_spec

/-- Failed advancement is the exact window-end or missing-carrier stop. -/
theorem expressionAtomRecoveryStops_of_advance?_eq_none
    (input : State) (advanced : input.advance? = none) :
    DeclarativeGrammar.ExpressionAtomRecoveryStops
      input.declarativeRemainder input.declarativeRemainder := by
  by_cases atEnd : input.window.endIndex ≤ input.cursor
  · exact .windowEnd atEnd
  · have inside : input.cursor < input.window.endIndex := by omega
    apply DeclarativeGrammar.ExpressionAtomRecoveryStops.missingToken inside
    unfold State.advance? State.peek? at advanced
    simpa [State.declarativeRemainder, inside] using advanced

/-- A present non-boundary token selects continuation, never scan stop. -/
theorem no_expressionAtomRecoveryStops_of_nonBoundary_token
    {input : State} {token : Token}
    (boundary : isAtomBoundary input = false)
    (found : input.peek? = some token) :
    ¬ DeclarativeGrammar.ExpressionAtomRecoveryStops
      input.declarativeRemainder input.declarativeRemainder := by
  intro stops
  have current := tokenAt_of_peek?_eq_some found
  cases stops with
  | windowEnd atEnd =>
      exact Nat.not_lt_of_ge atEnd
        (State.cursor_lt_endIndex_of_peek?_eq_some found)
  | semicolon present =>
      have guard : isSymbol input .semicolon = true :=
        isSymbol_eq_true_of_tokenAt .semicolon (by
          simpa [State.declarativeRemainder] using present)
      simp [isAtomBoundary, guard] at boundary
  | comma present =>
      have guard : isSymbol input .comma = true :=
        isSymbol_eq_true_of_tokenAt .comma (by
          simpa [State.declarativeRemainder] using present)
      simp [isAtomBoundary, guard] at boundary
  | rightParen present =>
      have guard : isSymbol input .rightParen = true :=
        isSymbol_eq_true_of_tokenAt .rightParen (by
          simpa [State.declarativeRemainder] using present)
      simp [isAtomBoundary, guard] at boundary
  | rightBracket present =>
      have guard : isSymbol input .rightBracket = true :=
        isSymbol_eq_true_of_tokenAt .rightBracket (by
          simpa [State.declarativeRemainder] using present)
      simp [isAtomBoundary, guard] at boundary
  | rightBrace present =>
      have guard : isSymbol input .rightBrace = true :=
        isSymbol_eq_true_of_tokenAt .rightBrace (by
          simpa [State.declarativeRemainder] using present)
      simp [isAtomBoundary, guard] at boundary
  | question present =>
      have guard : isSymbol input .question = true :=
        isSymbol_eq_true_of_tokenAt .question (by
          simpa [State.declarativeRemainder] using present)
      simp [isAtomBoundary, guard] at boundary
  | colon present =>
      have guard : isSymbol input .colon = true :=
        isSymbol_eq_true_of_tokenAt .colon (by
          simpa [State.declarativeRemainder] using present)
      simp [isAtomBoundary, guard] at boundary
  | fatArrow present =>
      have guard : isSymbol input .fatArrow = true :=
        isSymbol_eq_true_of_tokenAt .fatArrow (by
          simpa [State.declarativeRemainder] using present)
      simp [isAtomBoundary, guard] at boundary
  | pipe present =>
      have guard : isSymbol input .pipe = true :=
        isSymbol_eq_true_of_tokenAt .pipe (by
          simpa [State.declarativeRemainder] using present)
      simp [isAtomBoundary, guard] at boundary
  | elseKeyword present =>
      have guard : isKeyword input .elseKw = true :=
        isKeyword_eq_true_of_tokenAt .elseKw (by
          simpa [State.declarativeRemainder] using present)
      simp [isAtomBoundary, guard] at boundary
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
theorem recoverAtomAux_success_ordinary_sound (first : SourceSpan) :
    ∀ fuel last input expression output,
      recoverAtomAux first last fuel input = .ok expression output →
      DeclarativeGrammar.ExpressionAtomRecoveryScanParses first last
        input.declarativeRemainder expression output.declarativeRemainder := by
  intro fuel
  induction fuel with
  | zero =>
      intro last input expression output result
      simp [recoverAtomAux] at result
  | succ fuel inductionHypothesis =>
      intro last input expression output result
      unfold recoverAtomAux at result
      by_cases boundary : isAtomBoundary input = true
      · simp only [boundary, if_true] at result
        unfold finishRecoveredAtom at result
        cases result
        exact .stop (expressionAtomRecoveryStops_of_isAtomBoundary input boundary)
      · have boundaryFalse : isAtomBoundary input = false :=
          Bool.eq_false_iff.mpr boundary
        simp only [boundaryFalse, Bool.false_eq_true, if_false] at result
        cases advanced : input.advance? with
        | none =>
            simp only [advanced] at result
            unfold finishRecoveredAtom at result
            cases result
            exact .stop
              (expressionAtomRecoveryStops_of_advance?_eq_none input advanced)
        | some pair =>
            rcases pair with ⟨token, next⟩
            simp only [advanced] at result
            rcases advance?_state_shape advanced with ⟨found, nextEq⟩
            have tail := inductionHypothesis token.span next expression output result
            rw [nextEq] at tail
            exact .next
              (no_expressionAtomRecoveryStops_of_nonBoundary_token
                boundaryFalse found)
              (tokenAt_of_peek?_eq_some found) tail

/-- Every successful complete executable recovery includes its first token. -/
theorem recoverAtom_success_ordinary_sound
    {input output : State} {expression : Expr}
    (result : recoverAtom input = .ok expression output) :
    DeclarativeGrammar.ExpressionAtomRecoveryParses
      input.declarativeRemainder expression output.declarativeRemainder := by
  unfold recoverAtom at result
  cases advanced : input.advance? with
  | none => simp [advanced, rejectAt] at result
  | some pair =>
      rcases pair with ⟨token, next⟩
      simp only [advanced] at result
      rcases advance?_state_shape advanced with ⟨found, nextEq⟩
      have scan := recoverAtomAux_success_ordinary_sound token.span
        (next.remainingCount + 1) token.span next expression output result
      rw [nextEq] at scan
      exact .recovered (tokenAt_of_peek?_eq_some found) scan

end ExpressionAtomInternals

end Solcore.Syntax.Parser
