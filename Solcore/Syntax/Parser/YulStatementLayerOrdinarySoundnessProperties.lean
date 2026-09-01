import Solcore.Syntax.Parser.YulStatementRecoveryOrdinarySoundnessProperties
import Solcore.Syntax.Parser.Yul.StatementRecoveryFuelTotalityProperties

/-! Ordinary-success reflection for one outer recovering Yul-statement layer. -/

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

private theorem reject_state_eq {α : Type} {leftFailure rightFailure : Failure}
    {leftState rightState : State}
    (result : (Reply.reject leftFailure leftState : Reply α) =
      .reject rightFailure rightState) : leftState = rightState := by
  injection result

/-- Every successful recovering statement layer is either an ordinary
terminated success or the exact rewind/first-token/recovery-scan outcome. -/
theorem yulStatementLayer_success_ordinary_sound
    (nested : Parser YulStmt)
    (terminatedOrdinary : DeclarativeGrammar.Remainder → YulStmt →
      DeclarativeGrammar.Remainder → Prop)
    (terminatedRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    (terminatedSuccessSound : ∀ {input output : State}
      {statement : YulStmt},
      yulStatementTerminated nested input = .ok statement output →
        terminatedOrdinary input.declarativeRemainder statement
          output.declarativeRemainder)
    (terminatedRejectSound : ∀ {input rejected : State}
      {failure : Failure},
      yulStatementTerminated nested input = .reject failure rejected →
        terminatedRejects input.declarativeRemainder
          rejected.declarativeRemainder)
    (terminatedShape :
      Parser.PreservesTokenWindow (yulStatementTerminated nested))
    {input output : State} {statement : YulStmt}
    (result : yulStatementLayer nested input = .ok statement output) :
    DeclarativeGrammar.YulStatementLayerOrdinaryParses terminatedOrdinary
      terminatedRejects input.declarativeRemainder statement
        output.declarativeRemainder := by
  unfold yulStatementLayer at result
  cases terminatedResult : yulStatementTerminated nested input with
  | ok parsed afterTerminated =>
      simp only [terminatedResult] at result
      cases result
      exact .terminated (terminatedSuccessSound terminatedResult)
  | invariant error => simp [terminatedResult] at result
  | reject failure failedState =>
      simp only [terminatedResult] at result
      have rejectedGrammar := terminatedRejectSound terminatedResult
      have shape := terminatedShape input
      rw [terminatedResult] at shape
      have failedShape : failedState.tokens = input.tokens ∧
          failedState.window = input.window := by
        simpa only [Reply.PreservesTokenWindow] using shape
      let rewound : State := { failedState with cursor := input.cursor }
      change (if rewound.atEnd || isSymbol rewound .rightBrace then
        .reject failure rewound else
        match rewound.advance? with
        | some (token, afterToken) =>
            recoverYulStatementAux token.span token.span
              (afterToken.remainingCount + 1)
              (afterToken.emit failure.toDiagnostic)
        | none => .reject failure rewound) = .ok statement output at result
      by_cases boundary :
          (rewound.atEnd || isSymbol rewound .rightBrace) = true
      · simp only [boundary, if_true] at result
        contradiction
      · have boundaryFalse :
            (rewound.atEnd || isSymbol rewound .rightBrace) = false :=
          Bool.eq_false_iff.mpr boundary
        simp only [boundaryFalse, Bool.false_eq_true, if_false] at result
        cases advanced : rewound.advance? with
        | none => simp [advanced] at result
        | some pair =>
            rcases pair with ⟨token, afterToken⟩
            simp only [advanced] at result
            rcases advance?_state_shape advanced with ⟨found, afterEq⟩
            have current := tokenAt_of_peek?_eq_some found
            have continues := no_yulStatementRejects_of_nonBoundary_token
              boundaryFalse found
            have scan := recoverYulStatementAux_success_ordinary_sound
              token.span (afterToken.remainingCount + 1) token.span
              (afterToken.emit failure.toDiagnostic) statement output result
            rw [afterEq] at scan
            exact .recovered rejectedGrammar
              (by
                simpa [rewound, State.declarativeRemainder, failedShape.1,
                  failedShape.2] using continues)
              (by
                simpa [rewound, State.declarativeRemainder, failedShape.1,
                  failedShape.2] using current)
              (by
                simpa [rewound, State.declarativeRemainder, State.emit,
                  failedShape.1, failedShape.2] using scan)

/-- Every executable outer-layer rejection is the exact non-consuming Yul
statement recovery boundary. -/
theorem yulStatementLayer_reject_sound
    (nested : Parser YulStmt)
    (terminatedShape :
      Parser.PreservesTokenWindow (yulStatementTerminated nested))
    {input rejected : State} {failure : Failure}
    (result : yulStatementLayer nested input = .reject failure rejected) :
    DeclarativeGrammar.YulStatementRejects input.declarativeRemainder
      rejected.declarativeRemainder := by
  unfold yulStatementLayer at result
  cases terminatedResult : yulStatementTerminated nested input with
  | ok statement output => simp [terminatedResult] at result
  | invariant error => simp [terminatedResult] at result
  | reject primaryFailure failedState =>
      simp only [terminatedResult] at result
      have shape := terminatedShape input
      rw [terminatedResult] at shape
      have failedShape : failedState.tokens = input.tokens ∧
          failedState.window = input.window := by
        simpa only [Reply.PreservesTokenWindow] using shape
      let rewound : State := { failedState with cursor := input.cursor }
      change (if rewound.atEnd || isSymbol rewound .rightBrace then
        .reject primaryFailure rewound else
        match rewound.advance? with
        | some (token, afterToken) =>
            recoverYulStatementAux token.span token.span
              (afterToken.remainingCount + 1)
              (afterToken.emit primaryFailure.toDiagnostic)
        | none => .reject primaryFailure rewound) =
          .reject failure rejected at result
      by_cases boundary :
          (rewound.atEnd || isSymbol rewound .rightBrace) = true
      · simp only [boundary, if_true] at result
        have stateEq := reject_state_eq result
        rw [← stateEq]
        simpa [rewound, State.declarativeRemainder, failedShape.1,
          failedShape.2] using
            yulStatementRejects_of_boundary rewound boundary
      · have boundaryFalse :
            (rewound.atEnd || isSymbol rewound .rightBrace) = false :=
          Bool.eq_false_iff.mpr boundary
        simp only [boundaryFalse, Bool.false_eq_true, if_false] at result
        cases advanced : rewound.advance? with
        | none =>
            simp only [advanced] at result
            have stateEq := reject_state_eq result
            rw [← stateEq]
            simpa [rewound, State.declarativeRemainder, failedShape.1,
              failedShape.2] using
                yulStatementRejects_of_advance?_eq_none rewound advanced
        | some pair =>
            rcases pair with ⟨token, afterToken⟩
            simp only [advanced] at result
            rcases recoverYulStatementAux_production_exists_ok token.span
                token.span (afterToken.emit primaryFailure.toDiagnostic) with
              ⟨statement, final, recovered⟩
            have sameRemaining :
                (afterToken.emit primaryFailure.toDiagnostic).remainingCount =
                  afterToken.remainingCount := rfl
            rw [sameRemaining] at recovered
            rw [recovered] at result
            contradiction

end Solcore.Syntax.Parser
