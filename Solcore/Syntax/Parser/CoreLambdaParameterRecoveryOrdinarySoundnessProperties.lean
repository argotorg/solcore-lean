import Solcore.Syntax.DeclarativeCoreLambdaParameterRecoveryOutcomeProperties
import Solcore.Syntax.Parser.DelimitedRejectionPrimitiveProperties
import Solcore.Syntax.Parser.Parameter

/-! Exact executable ordinary successes of parameter recovery. -/

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
  rcases symbol_eq_ok_of_isSymbol_eq_true value .parameter present with
    ⟨token, parsed⟩
  exact ⟨token.span, (symbol_ok_tokenAt value .parameter parsed).1⟩

namespace FunctionParameterInternals

/-- A true executable scan guard gives its exact declarative stop. -/
theorem functionParameterRecoveryStops_of_boundary
    (input : State)
    (boundary : (input.atEnd || isSymbol input .comma ||
      isSymbol input .rightParen) = true) :
    DeclarativeGrammar.FunctionParameterRecoveryStops
      input.declarativeRemainder := by
  by_cases atEnd : input.window.endIndex ≤ input.cursor
  · exact .windowEnd atEnd
  · have atEndFalse : input.atEnd = false := by
      unfold State.atEnd
      exact decide_eq_false atEnd
    by_cases comma : isSymbol input .comma = true
    · rcases tokenAt_of_isSymbol_eq_true .comma comma with
        ⟨span, token⟩
      exact .comma token
    · have commaFalse := Bool.eq_false_iff.mpr comma
      have rightParen : isSymbol input .rightParen = true := by
        simpa [atEndFalse, commaFalse] using boundary
      rcases tokenAt_of_isSymbol_eq_true .rightParen rightParen with
        ⟨span, token⟩
      exact .rightParen token

/-- Failed advancement is exact window-end or missing-carrier evidence. -/
theorem functionParameterRecoveryStops_of_advance?_eq_none
    (input : State) (advanced : input.advance? = none) :
    DeclarativeGrammar.FunctionParameterRecoveryStops
      input.declarativeRemainder := by
  by_cases atEnd : input.window.endIndex ≤ input.cursor
  · exact .windowEnd atEnd
  · have inside : input.cursor < input.window.endIndex := by omega
    apply DeclarativeGrammar.FunctionParameterRecoveryStops.missingToken
      inside
    unfold State.advance? State.peek? at advanced
    simpa [State.declarativeRemainder, inside] using advanced

/-- A present non-boundary token forces scan continuation. -/
theorem no_functionParameterRecoveryStops_of_nonBoundary_token
    {input : State} {token : Token}
    (boundary : (input.atEnd || isSymbol input .comma ||
      isSymbol input .rightParen) = false)
    (found : input.peek? = some token) :
    ¬ DeclarativeGrammar.FunctionParameterRecoveryStops
      input.declarativeRemainder := by
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
      simp [guard] at boundary
  | rightParen present =>
      have guard : isSymbol input .rightParen = true :=
        isSymbol_eq_true_of_tokenAt .rightParen (by
          simpa [State.declarativeRemainder] using present)
      simp [guard] at boundary
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
theorem recoverParameterAux_success_ordinary_sound (first : SourceSpan) :
    ∀ fuel last input parameter output,
      recoverParameterAux first last fuel input = .ok parameter output →
      DeclarativeGrammar.FunctionParameterRecoveryScanParses first last
        input.declarativeRemainder parameter output.declarativeRemainder := by
  intro fuel
  induction fuel with
  | zero =>
      intro last input parameter output result
      simp [recoverParameterAux] at result
  | succ fuel inductionHypothesis =>
      intro last input parameter output result
      unfold recoverParameterAux at result
      by_cases boundary : (input.atEnd || isSymbol input .comma ||
          isSymbol input .rightParen) = true
      · simp only [boundary, if_true] at result
        unfold finishRecoveredParameter at result
        cases result
        simpa [State.emit, State.declarativeRemainder] using
          (DeclarativeGrammar.FunctionParameterRecoveryScanParses.stop
            (first := first) (last := last)
            (functionParameterRecoveryStops_of_boundary input boundary))
      · have boundaryFalse : (input.atEnd || isSymbol input .comma ||
            isSymbol input .rightParen) = false :=
          Bool.eq_false_iff.mpr boundary
        simp only [boundaryFalse, Bool.false_eq_true, if_false] at result
        cases advanced : input.advance? with
        | none =>
            simp only [advanced] at result
            unfold finishRecoveredParameter at result
            cases result
            simpa [State.emit, State.declarativeRemainder] using
              (DeclarativeGrammar.FunctionParameterRecoveryScanParses.stop
                (first := first) (last := last)
                (functionParameterRecoveryStops_of_advance?_eq_none input
                  advanced))
        | some pair =>
            rcases pair with ⟨token, next⟩
            simp only [advanced] at result
            rcases advance?_state_shape advanced with ⟨found, nextEq⟩
            have tail := inductionHypothesis token.span next parameter output
              result
            rw [nextEq] at tail
            exact .next
              (no_functionParameterRecoveryStops_of_nonBoundary_token
                boundaryFalse found)
              (tokenAt_of_peek?_eq_some found) tail

/-- Every complete executable function recovery includes its first token. -/
theorem recoverParameter_success_ordinary_sound
    {input output : State} {parameter : FunctionParameter}
    (result : recoverParameter input = .ok parameter output) :
    DeclarativeGrammar.FunctionParameterRecoveryParses
      input.declarativeRemainder parameter output.declarativeRemainder := by
  unfold recoverParameter at result
  cases advanced : input.advance? with
  | none => simp [advanced, rejectAt] at result
  | some pair =>
      rcases pair with ⟨token, next⟩
      simp only [advanced] at result
      rcases advance?_state_shape advanced with ⟨found, nextEq⟩
      have scan := recoverParameterAux_success_ordinary_sound token.span
        (next.remainingCount + 1) token.span next parameter output result
      rw [nextEq] at scan
      exact .recovered (tokenAt_of_peek?_eq_some found) scan

end FunctionParameterInternals

namespace LambdaParameterInternals

/-- Executable lambda recovery is the exact span-preserving retag. -/
theorem recoverLambdaParameter_success_ordinary_sound
    {input output : State} {parameter : LambdaParameter}
    (result : recoverLambdaParameter input = .ok parameter output) :
    DeclarativeGrammar.LambdaParameterRecoveryParses
      input.declarativeRemainder parameter output.declarativeRemainder := by
  unfold recoverLambdaParameter at result
  cases recoveredResult : FunctionParameterInternals.recoverParameter input with
  | invariant error => simp [recoveredResult] at result
  | reject failure rejected => simp [recoveredResult] at result
  | ok recovered afterRecovery =>
      simp only [recoveredResult] at result
      cases result
      exact .recovered
        (FunctionParameterInternals.recoverParameter_success_ordinary_sound
          recoveredResult)

end LambdaParameterInternals
end Solcore.Syntax.Parser
