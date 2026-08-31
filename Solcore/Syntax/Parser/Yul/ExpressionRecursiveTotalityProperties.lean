import Solcore.Syntax.Parser.InvariantFreeProperties
import Solcore.Syntax.Parser.Yul.ExpressionFuelTotalityProperties

/-! Recursive-family and public totality for inline-Yul expressions. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

private theorem yulAdvance_state_shape {input next : State} {token : Token}
    (advanced : input.advance? = some (token, next)) :
    next = { input with cursor := input.cursor + 1 } := by
  unfold State.advance? at advanced
  cases found : input.peek? with
  | none => simp [found] at advanced
  | some current =>
      simp only [found, Option.map_some] at advanced
      cases advanced
      rfl

namespace YulExpressionInternals

/-- Every successful recovering layer consumes at least one input token. -/
theorem layer_cursor_lt_onSuccess
    (nested : Parser YulExpr) {input final : State} {value : YulExpr}
    (parsed : layer nested input = .ok value final) :
    input.cursor < final.cursor := by
  unfold layer at parsed
  cases coreResult : yulExpressionCore nested input with
  | invariant error => simp [coreResult] at parsed
  | ok expression next =>
      simp only [coreResult] at parsed
      cases parsed
      exact yulExpressionCore_cursor_lt_onSuccess nested coreResult
  | reject failure failedState =>
      simp only [coreResult] at parsed
      let rewound := { failedState with cursor := input.cursor }
      split at parsed
      · contradiction
      · cases advanced : rewound.advance? with
        | none =>
            rw [advanced] at parsed
            contradiction
        | some pair =>
            rcases pair with ⟨token, afterToken⟩
            rw [advanced] at parsed
            have recoveryMonotone := recoverAux_cursorMonotoneOnSuccess
              token.span token.span (afterToken.remainingCount + 1)
              (afterToken.emit failure.toDiagnostic) value final parsed
            have shape := yulAdvance_state_shape advanced
            have afterCursor : afterToken.cursor = input.cursor + 1 := by
              simp [shape, rewound]
            have emittedCursor :
                (afterToken.emit failure.toDiagnostic).cursor =
                  afterToken.cursor := rfl
            rw [emittedCursor, afterCursor] at recoveryMonotone
            omega

/-- Strict progress also holds uniformly across the recursive fuel family. -/
theorem withFuel_cursor_lt_onSuccess
    (fuel : Nat) {input final : State} {value : YulExpr}
    (parsed : withFuel fuel input = .ok value final) :
    input.cursor < final.cursor := by
  cases fuel with
  | zero =>
      unfold withFuel at parsed
      contradiction
  | succ fuel =>
      exact layer_cursor_lt_onSuccess (withFuel fuel) parsed

/-- Each recursive parser is total exactly below its own fuel index. -/
theorem withFuel_fuelElementTotalityContract : ∀ fuel,
    FuelElementTotalityContract (withFuel fuel) fuel := by
  intro fuel
  induction fuel with
  | zero =>
      exact {
        validFor := (withFuel_validFor 0).mono (fun _ _ _ => trivial)
        preservesTokenWindow := withFuel_preservesTokenWindow 0
        cursorLtOnSuccess := withFuel_cursor_lt_onSuccess 0
        ordinary := by
          intro input inputValid adequate
          omega
      }
  | succ fuel inductionHypothesis =>
      exact {
        validFor := (withFuel_validFor (fuel + 1)).mono
          (fun _ _ _ => trivial)
        preservesTokenWindow := withFuel_preservesTokenWindow (fuel + 1)
        cursorLtOnSuccess := withFuel_cursor_lt_onSuccess (fuel + 1)
        ordinary := by
          intro input inputValid adequate
          simpa only [withFuel] using
            layer_ordinary_of_elementFuel (withFuel fuel) fuel
              inductionHypothesis input inputValid
                (by simpa [Nat.succ_eq_add_one] using adequate)
      }

theorem withFuel_ordinary_of_remainingCount_lt
    (fuel : Nat) (input : State) (inputValid : input.ValidFor)
    (adequate : input.remainingCount < fuel) :
    (∃ expression next, withFuel fuel input = .ok expression next) ∨
    (∃ failure next, withFuel fuel input = .reject failure next) :=
  (withFuel_fuelElementTotalityContract fuel).ordinary input inputValid
    adequate

theorem withFuel_ne_invariant_of_remainingCount_lt
    (fuel : Nat) (input : State) (inputValid : input.ValidFor)
    (adequate : input.remainingCount < fuel)
    (error : ParserInvariantError) :
    withFuel fuel input ≠ .invariant error :=
  (withFuel_fuelElementTotalityContract fuel).ne_invariant input inputValid
    adequate error

end YulExpressionInternals

/-- Production fuel makes the public recursive Yul parser ordinary. -/
theorem yulExpression_invariantFreeOnValid :
    Parser.InvariantFreeOnValid yulExpression := by
  intro input inputValid
  unfold yulExpression
  exact YulExpressionInternals.withFuel_ordinary_of_remainingCount_lt
    (input.remainingCount + 1) input inputValid (by omega)

theorem yulExpression_ne_invariant
    (input : State) (inputValid : input.ValidFor)
    (error : ParserInvariantError) :
    yulExpression input ≠ .invariant error :=
  yulExpression_invariantFreeOnValid.ne_invariant input inputValid error

/-- Every successful public Yul expression consumes its leading token. -/
theorem yulExpression_cursor_lt_onSuccess
    {input final : State} {value : YulExpr}
    (parsed : yulExpression input = .ok value final) :
    input.cursor < final.cursor := by
  unfold yulExpression at parsed
  exact YulExpressionInternals.withFuel_cursor_lt_onSuccess
    (input.remainingCount + 1) parsed

/-- Public inline-Yul expressions satisfy the complete element contract. -/
theorem yulExpression_elementTotalityContract :
    ElementTotalityContract yulExpression := {
  validFor := yulExpression_validFor.mono (fun _ _ _ => trivial)
  preservesTokenWindow := yulExpression_preservesTokenWindow
  cursorLtOnSuccess := yulExpression_cursor_lt_onSuccess
  invariantFree := fun input inputValid error =>
    yulExpression_ne_invariant input inputValid error
}

end Solcore.Syntax.Parser
