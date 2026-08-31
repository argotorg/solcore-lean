import Solcore.Syntax.Parser.ParameterRecoveryTotalityProperties

/-! Valid-input totality and strict progress for lambda parameters. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

namespace FunctionParameterInternals

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

private theorem recoverParameterAux_cursorMonotoneOnSuccess
    (first last : SourceSpan) :
    ∀ fuel, Parser.CursorMonotoneOnSuccess
      (recoverParameterAux first last fuel) := by
  intro fuel
  induction fuel generalizing last with
  | zero => simp [recoverParameterAux, Parser.CursorMonotoneOnSuccess]
  | succ fuel inductionHypothesis =>
      intro input value final parsed
      unfold recoverParameterAux at parsed
      split at parsed
      · unfold finishRecoveredParameter at parsed
        cases parsed
        exact Nat.le_refl _
      · cases advanced : input.advance? with
        | none =>
            simp only [advanced] at parsed
            unfold finishRecoveredParameter at parsed
            cases parsed
            exact Nat.le_refl _
        | some pair =>
            rcases pair with ⟨token, next⟩
            simp only [advanced] at parsed
            exact Nat.le_trans (by
              simp [(advance?_state_shape advanced).2])
              (inductionHypothesis token.span next value final parsed)

theorem recoverParameter_cursor_lt_onSuccess {input final : State}
    {value : FunctionParameter}
    (parsed : recoverParameter input = .ok value final) :
    input.cursor < final.cursor := by
  unfold recoverParameter at parsed
  cases advanced : input.advance? with
  | none => simp [advanced, rejectAt] at parsed
  | some pair =>
      rcases pair with ⟨token, next⟩
      simp only [advanced] at parsed
      exact Nat.lt_of_lt_of_le (by
        simp [(advance?_state_shape advanced).2])
        (recoverParameterAux_cursorMonotoneOnSuccess token.span token.span
          (next.remainingCount + 1) next value final parsed)

end FunctionParameterInternals

namespace LambdaParameterInternals

theorem recoverLambdaParameter_ordinary :
    Parser.Ordinary recoverLambdaParameter := by
  intro input
  rcases FunctionParameterInternals.recoverParameter_ordinary input with
    ⟨value, next, result⟩ | ⟨failure, next, result⟩
  · exact Or.inl ⟨{ span := value.span, value := .error }, next, by
      simp [recoverLambdaParameter, result]⟩
  · exact Or.inr ⟨failure, next, by
      simp [recoverLambdaParameter, result]⟩

theorem recoverLambdaParameter_invariantFreeOnValid :
    Parser.InvariantFreeOnValid recoverLambdaParameter :=
  recoverLambdaParameter_ordinary.invariantFreeOnValid

theorem recoverLambdaParameter_ne_invariant (input : State)
    (error : ParserInvariantError) :
    recoverLambdaParameter input ≠ .invariant error :=
  recoverLambdaParameter_ordinary.ne_invariant input error

theorem recoverLambdaParameter_cursor_lt_onSuccess {input final : State}
    {value : LambdaParameter}
    (parsed : recoverLambdaParameter input = .ok value final) :
    input.cursor < final.cursor := by
  unfold recoverLambdaParameter at parsed
  cases result : FunctionParameterInternals.recoverParameter input with
  | ok recovered next =>
      simp only [result] at parsed
      cases parsed
      exact FunctionParameterInternals.recoverParameter_cursor_lt_onSuccess
        result
  | reject failure next => simp [result] at parsed
  | invariant error => simp [result] at parsed

end LambdaParameterInternals

/-- Recovery discharges the public wrapper once core totality is supplied. -/
theorem lambdaParameter_invariantFreeOnValid_of_core
    (coreFree : Parser.InvariantFreeOnValid
      LambdaParameterInternals.lambdaParameterCore) :
    Parser.InvariantFreeOnValid lambdaParameter := by
  intro input inputValid
  rcases coreFree input inputValid with
    ⟨value, next, coreResult⟩ | ⟨failure, failedState, coreResult⟩
  · exact Or.inl ⟨value, next, by
      simp only [lambdaParameter, coreResult]⟩
  · let rewound : State := { failedState with cursor := input.cursor }
    by_cases boundary : rewound.atEnd || isSymbol rewound .comma ||
        isSymbol rewound .rightParen
    · exact Or.inr ⟨failure, rewound, by
        simp only [lambdaParameter, coreResult]
        change (if rewound.atEnd || isSymbol rewound .comma ||
            isSymbol rewound .rightParen then Reply.reject failure rewound
          else _) = _
        rw [if_pos boundary]⟩
    · rcases LambdaParameterInternals.recoverLambdaParameter_ordinary
          (rewound.emit failure.toDiagnostic) with
        ⟨value, final, recoveryResult⟩ |
        ⟨recoveryFailure, final, recoveryResult⟩
      · exact Or.inl ⟨value, final, by
          simp only [lambdaParameter, coreResult]
          change (if rewound.atEnd || isSymbol rewound .comma ||
              isSymbol rewound .rightParen then _
            else LambdaParameterInternals.recoverLambdaParameter
              (rewound.emit failure.toDiagnostic)) = _
          rw [if_neg boundary, recoveryResult]⟩
      · exact Or.inr ⟨recoveryFailure, final, by
          simp only [lambdaParameter, coreResult]
          change (if rewound.atEnd || isSymbol rewound .comma ||
              isSymbol rewound .rightParen then _
            else LambdaParameterInternals.recoverLambdaParameter
              (rewound.emit failure.toDiagnostic)) = _
          rw [if_neg boundary, recoveryResult]⟩

theorem lambdaParameter_ne_invariant_of_core
    (coreFree : Parser.InvariantFreeOnValid
      LambdaParameterInternals.lambdaParameterCore)
    (input : State) (inputValid : input.ValidFor)
    (error : ParserInvariantError) :
    lambdaParameter input ≠ .invariant error :=
  (lambdaParameter_invariantFreeOnValid_of_core coreFree).ne_invariant
    input inputValid error

theorem lambdaParameter_cursor_lt_onSuccess_of_core
    (coreStrict : ∀ {input final : State} {value : LambdaParameter},
      LambdaParameterInternals.lambdaParameterCore input = .ok value final →
        input.cursor < final.cursor)
    {input final : State} {value : LambdaParameter}
    (parsed : lambdaParameter input = .ok value final) :
    input.cursor < final.cursor := by
  unfold lambdaParameter at parsed
  cases coreResult : LambdaParameterInternals.lambdaParameterCore input with
  | ok coreValue next =>
      simp only [coreResult] at parsed
      cases parsed
      exact coreStrict coreResult
  | invariant error => simp [coreResult] at parsed
  | reject failure failedState =>
      simp only [coreResult] at parsed
      let rewound : State := { failedState with cursor := input.cursor }
      change (if rewound.atEnd || isSymbol rewound .comma ||
          isSymbol rewound .rightParen then .reject failure rewound
        else LambdaParameterInternals.recoverLambdaParameter
          (rewound.emit failure.toDiagnostic)) = .ok value final at parsed
      split at parsed
      · contradiction
      · simpa [rewound, State.emit] using
          LambdaParameterInternals.recoverLambdaParameter_cursor_lt_onSuccess
            parsed

/-- Conditional full contract; only the non-recovering core remains. -/
theorem lambdaParameter_elementTotalityContract_of_core
    (coreFree : Parser.InvariantFreeOnValid
      LambdaParameterInternals.lambdaParameterCore)
    (coreStrict : ∀ {input final : State} {value : LambdaParameter},
      LambdaParameterInternals.lambdaParameterCore input = .ok value final →
        input.cursor < final.cursor) :
    ElementTotalityContract lambdaParameter := {
  validFor := lambdaParameter_validFor.mono (fun _ _ _ => trivial)
  preservesTokenWindow := lambdaParameter_preservesTokenWindow
  cursorLtOnSuccess := lambdaParameter_cursor_lt_onSuccess_of_core coreStrict
  invariantFree := lambdaParameter_ne_invariant_of_core coreFree
}

end Solcore.Syntax.Parser
