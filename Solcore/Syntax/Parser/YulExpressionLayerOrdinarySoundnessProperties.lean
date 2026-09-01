import Solcore.Syntax.Parser.YulExpressionRecoveryOrdinarySoundnessProperties

/-! Ordinary-success reflection for one recovering inline-Yul layer. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

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

/-- Every successful recovering layer follows either an ordinary core success
or the exact final-reject, first-token, recovery-scan branch. -/
theorem layer_success_ordinary_sound
    (nested : Parser YulExpr)
    (ordinaryParses : DeclarativeGrammar.Remainder → YulExpr →
      DeclarativeGrammar.Remainder → Prop)
    (nestedRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    (nestedSuccessSound : ∀ {input next : State} {value : YulExpr},
      nested input = .ok value next → ordinaryParses
        input.declarativeRemainder value next.declarativeRemainder)
    (nestedRejectSound : ∀ {input rejected : State} {failure : Failure},
      nested input = .reject failure rejected → nestedRejects
        input.declarativeRemainder rejected.declarativeRemainder)
    (nestedShape : Parser.PreservesTokenWindow nested)
    {input output : State} {expression : YulExpr}
    (result : layer nested input = .ok expression output) :
    DeclarativeGrammar.YulExpressionLayerOrdinaryParses ordinaryParses
      nestedRejects input.declarativeRemainder expression
        output.declarativeRemainder := by
  unfold layer at result
  cases coreResult : yulExpressionCore nested input with
  | ok coreExpression afterCore =>
      simp only [coreResult] at result
      cases result
      exact .core (yulExpressionCore_success_ordinary_sound nested
        ordinaryParses nestedRejects nestedSuccessSound nestedRejectSound
          nestedShape coreResult)
  | invariant error => simp [coreResult] at result
  | reject failure failedState =>
      simp only [coreResult] at result
      have failedEq := yulExpressionCore_reject_state_eq nested coreResult
      have coreRejected := yulExpressionCore_reject_final_sound nested
        coreResult
      subst failedState
      change (if isBoundary input then .reject failure input else
        match input.advance? with
        | some (token, afterToken) =>
            recoverAux token.span token.span (afterToken.remainingCount + 1)
              (afterToken.emit failure.toDiagnostic)
        | none => .reject failure input) = .ok expression output at result
      by_cases boundary : isBoundary input = true
      · simp only [boundary, if_true] at result
        contradiction
      · have boundaryFalse : isBoundary input = false :=
          Bool.eq_false_iff.mpr boundary
        simp only [boundaryFalse, Bool.false_eq_true, if_false] at result
        cases advanced : input.advance? with
        | none => simp [advanced] at result
        | some pair =>
            rcases pair with ⟨token, afterToken⟩
            simp only [advanced] at result
            rcases advance?_state_shape advanced with ⟨found, afterEq⟩
            have current := tokenAt_of_peek?_eq_some found
            have continues :=
              no_yulExpressionRejects_of_nonBoundary_token boundaryFalse found
            have scan := recoverAux_success_ordinary_sound token.span
              (afterToken.remainingCount + 1) token.span
                (afterToken.emit failure.toDiagnostic) expression output result
            rw [afterEq] at scan
            exact .recovered coreRejected continues current scan

end YulExpressionInternals

end Solcore.Syntax.Parser
