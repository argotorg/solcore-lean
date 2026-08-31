import Solcore.Syntax.Parser.PatternCoreFuelContractProperties
import Solcore.Syntax.Parser.PatternRecoveryTotalityProperties

/-! Fuel-aware totality for one recovering pattern layer. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

private theorem patternAdvance_state_shape {input next : State} {token : Token}
    (advanced : input.advance? = some (token, next)) :
    next = { input with cursor := input.cursor + 1 } := by
  unfold State.advance? at advanced
  cases found : input.peek? with
  | none => simp [found] at advanced
  | some current =>
      simp only [found, Option.map_some] at advanced
      cases advanced
      rfl

namespace PatternInternals

theorem patternLayer_ordinary_of_elementFuel
    (nested : Parser Pattern) (expression : Parser Expr)
    (nestedFuel expressionFuel : Nat)
    (nestedContract : FuelElementTotalityContract nested nestedFuel)
    (expressionContract :
      FuelElementTotalityContract expression expressionFuel)
    (input : State) (inputValid : input.ValidFor)
    (nestedAdequate : input.remainingCount < nestedFuel + 1)
    (expressionAdequate : input.remainingCount < expressionFuel + 1) :
    (∃ pattern next, patternLayer nested expression input = .ok pattern next) ∨
    (∃ failure next,
      patternLayer nested expression input = .reject failure next) := by
  rcases patternCore_ordinary_of_elementFuel nested expression nestedFuel
      expressionFuel nestedContract expressionContract input inputValid
      nestedAdequate expressionAdequate with
    ⟨pattern, next, coreResult⟩ | ⟨failure, failedState, coreResult⟩
  · exact Or.inl ⟨pattern, next, by
      simp only [patternLayer, coreResult]⟩
  · let rewound := { failedState with cursor := input.cursor }
    by_cases boundary : isPatternBoundary rewound
    · exact Or.inr ⟨failure, rewound, by
        simp only [patternLayer, coreResult, rewound, boundary, ↓reduceIte]⟩
    · cases advanced : rewound.advance? with
      | none => exact Or.inr ⟨failure, rewound, by
          simp only [patternLayer, coreResult, rewound, boundary,
            Bool.false_eq_true, ↓reduceIte, advanced]⟩
      | some pair =>
          rcases pair with ⟨token, afterToken⟩
          rcases recoverPatternAux_production_exists_ok token.span token.span
              (afterToken.emit failure.toDiagnostic) with
            ⟨recovered, final, recoveredResult⟩
          have recoveredAtProductionFuel :
              recoverPatternAux token.span token.span
                (afterToken.remainingCount + 1)
                (afterToken.emit failure.toDiagnostic) = .ok recovered final := by
            have emitRemaining :
                (afterToken.emit failure.toDiagnostic).remainingCount =
                  afterToken.remainingCount := rfl
            rw [emitRemaining] at recoveredResult
            exact recoveredResult
          exact Or.inl ⟨recovered, final, by
            simp only [patternLayer, coreResult, rewound, boundary,
              Bool.false_eq_true, ↓reduceIte, advanced,
              recoveredAtProductionFuel]⟩

theorem patternLayer_ne_invariant_of_elementFuel
    (nested : Parser Pattern) (expression : Parser Expr)
    (nestedFuel expressionFuel : Nat)
    (nestedContract : FuelElementTotalityContract nested nestedFuel)
    (expressionContract :
      FuelElementTotalityContract expression expressionFuel)
    (input : State) (inputValid : input.ValidFor)
    (nestedAdequate : input.remainingCount < nestedFuel + 1)
    (expressionAdequate : input.remainingCount < expressionFuel + 1)
    (error : ParserInvariantError) :
    patternLayer nested expression input ≠ .invariant error := by
  intro failed
  rcases patternLayer_ordinary_of_elementFuel nested expression nestedFuel
      expressionFuel nestedContract expressionContract input inputValid
      nestedAdequate expressionAdequate with
    ⟨pattern, next, result⟩ | ⟨failure, next, result⟩ <;>
      rw [result] at failed <;> contradiction

theorem patternLayer_cursor_lt_onSuccess
    (nested : Parser Pattern) (expression : Parser Expr)
    (nestedMonotone : Parser.CursorMonotoneOnSuccess nested)
    (expressionMonotone : Parser.CursorMonotoneOnSuccess expression)
    {input final : State} {value : Pattern}
    (parsed : patternLayer nested expression input = .ok value final) :
    input.cursor < final.cursor := by
  unfold patternLayer at parsed
  cases coreResult : patternCore nested expression input with
  | invariant error => simp [coreResult] at parsed
  | ok pattern next =>
      simp only [coreResult] at parsed
      cases parsed
      exact patternCore_cursor_lt_onSuccess nested expression nestedMonotone
        expressionMonotone coreResult
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
            have recoveryMonotone := recoverPatternAux_cursorMonotoneOnSuccess
              token.span token.span
              (afterToken.remainingCount + 1)
              (afterToken.emit failure.toDiagnostic) value final parsed
            have shape := patternAdvance_state_shape advanced
            have afterCursor : afterToken.cursor = input.cursor + 1 := by
              simp [shape, rewound]
            have emittedCursor :
                (afterToken.emit failure.toDiagnostic).cursor =
                  afterToken.cursor := rfl
            rw [emittedCursor, afterCursor] at recoveryMonotone
            omega

theorem patternLayer_fuelElementTotalityContract
    (nested : Parser Pattern) (expression : Parser Expr)
    (nestedFuel expressionFuel : Nat)
    (nestedContract : FuelElementTotalityContract nested nestedFuel)
    (expressionContract :
      FuelElementTotalityContract expression expressionFuel)
    (expressionValid : SourceFile → Expr → Prop)
    (nestedValid : nested.ValidFor (Pattern.ValidFor expressionValid))
    (expressionValidFor : expression.ValidFor expressionValid)
    (spanValid : ∀ {file : SourceFile} {value : Expr},
      expressionValid file value → value.span.ValidFor file)
    (expressionStarts :
      Parser.StartsAtCurrentTokenOnSuccess expression (·.span)) :
    FuelElementTotalityContract (patternLayer nested expression)
      (Nat.min (nestedFuel + 1) (expressionFuel + 1)) := {
  validFor := (patternLayer_validFor nested expression expressionValid
    nestedValid nestedContract.preservesTokenWindow expressionValidFor
    spanValid expressionStarts expressionContract.preservesTokenWindow).mono
      (fun _ _ _ => trivial)
  preservesTokenWindow := patternLayer_preservesTokenWindow nested expression
    nestedContract.preservesTokenWindow expressionContract.preservesTokenWindow
  cursorLtOnSuccess := patternLayer_cursor_lt_onSuccess nested expression
    (fun _ _ _ result => Nat.le_of_lt
      (nestedContract.cursorLtOnSuccess result))
    (fun _ _ _ result => Nat.le_of_lt
      (expressionContract.cursorLtOnSuccess result))
  ordinary := by
    intro state stateValid adequate
    apply patternLayer_ordinary_of_elementFuel nested expression nestedFuel
      expressionFuel nestedContract expressionContract state stateValid
    · exact Nat.lt_of_lt_of_le adequate
        (Nat.min_le_left (nestedFuel + 1) (expressionFuel + 1))
    · exact Nat.lt_of_lt_of_le adequate
        (Nat.min_le_right (nestedFuel + 1) (expressionFuel + 1))
}

end PatternInternals

end Solcore.Syntax.Parser
