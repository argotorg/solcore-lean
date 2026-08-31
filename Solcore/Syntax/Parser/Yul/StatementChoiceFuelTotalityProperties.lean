import Solcore.Syntax.Parser.Yul.StatementFallbackFuelTotalityProperties

/-! Fuel-total transactional and state-selected Yul statement choices. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

private theorem adequate_left {left right count : Nat}
    (adequate : count < Nat.min left right) : count < left :=
  Nat.lt_of_lt_of_le adequate (Nat.min_le_left left right)

private theorem adequate_right {left right count : Nat}
    (adequate : count < Nat.min left right) : count < right :=
  Nat.lt_of_lt_of_le adequate (Nat.min_le_right left right)

/-- Strict branch progress survives diagnostic-replacing fallback. -/
theorem recognizedYulStatementOrFallback_cursor_lt_onSuccess_of_strict
    (primary fallback : Parser YulStmt)
    (primaryStrict : ∀ {input next : State} {value : YulStmt},
      primary input = .ok value next → input.cursor < next.cursor)
    (fallbackStrict : ∀ {input next : State} {value : YulStmt},
      fallback input = .ok value next → input.cursor < next.cursor)
    {input final : State} {value : YulStmt}
    (parsed : recognizedYulStatementOrFallback primary fallback input =
      .ok value final) :
    input.cursor < final.cursor := by
  unfold recognizedYulStatementOrFallback at parsed
  cases primaryResult : primary input with
  | invariant error => simp [primaryResult] at parsed
  | ok primaryValue next =>
      simp only [primaryResult] at parsed
      cases parsed
      exact primaryStrict primaryResult
  | reject failure rejected =>
      simp only [primaryResult] at parsed
      cases fallbackResult : fallback input with
      | invariant error => simp [fallbackResult] at parsed
      | reject fallbackFailure fallbackRejected =>
          simp [fallbackResult] at parsed
      | ok fallbackValue next =>
          simp only [fallbackResult] at parsed
          cases parsed
          have progress : input.cursor < next.cursor :=
            fallbackStrict fallbackResult
          change input.cursor < next.cursor
          exact progress

/-- Selecting a parser from the initial state preserves bounded totality. -/
theorem stateChoice_fuelTotalityContract
    (condition : State → Bool) (first second : Parser YulStmt)
    (firstFuel secondFuel : Nat)
    (firstContract : FuelYulStatementTotalityContract first firstFuel)
    (secondContract : FuelYulStatementTotalityContract second secondFuel) :
    FuelYulStatementTotalityContract
      (fun input => if condition input then first input else second input)
      (Nat.min firstFuel secondFuel) := {
  toYulStatementParserContracts := {
    validFor := by
      intro input inputValid
      by_cases selected : condition input = true
      · simpa [selected] using firstContract.validFor input inputValid
      · simpa [selected] using secondContract.validFor input inputValid
    preservesTokens := by
      intro input value next result
      by_cases selected : condition input = true
      · exact firstContract.preservesTokens input value next
          (by simpa [selected] using result)
      · exact secondContract.preservesTokens input value next
          (by simpa [selected] using result)
    cursorMonotone := by
      intro input value next result
      by_cases selected : condition input = true
      · exact firstContract.cursorMonotone input value next
          (by simpa [selected] using result)
      · exact secondContract.cursorMonotone input value next
          (by simpa [selected] using result)
    startsAtToken := by
      intro input value next result
      by_cases selected : condition input = true
      · exact firstContract.startsAtToken input value next
          (by simpa [selected] using result)
      · exact secondContract.startsAtToken input value next
          (by simpa [selected] using result)
  }
  preservesTokenWindow := by
    intro input
    by_cases selected : condition input = true
    · simpa [selected] using firstContract.preservesTokenWindow input
    · simpa [selected] using secondContract.preservesTokenWindow input
  ordinary := by
    intro input inputValid adequate
    by_cases selected : condition input = true
    · simpa [selected] using firstContract.ordinary input inputValid
        (adequate_left adequate)
    · simpa [selected] using secondContract.ordinary input inputValid
        (adequate_right adequate)
}

theorem stateChoice_cursor_lt_onSuccess_of_strict
    (condition : State → Bool) (first second : Parser YulStmt)
    (firstStrict : ∀ {input next : State} {value : YulStmt},
      first input = .ok value next → input.cursor < next.cursor)
    (secondStrict : ∀ {input next : State} {value : YulStmt},
      second input = .ok value next → input.cursor < next.cursor)
    {input final : State} {value : YulStmt}
    (parsed : (fun state => if condition state then first state
      else second state) input = .ok value final) :
    input.cursor < final.cursor := by
  by_cases selected : condition input = true
  · exact firstStrict (by simpa [selected] using parsed)
  · exact secondStrict (by simpa [selected] using parsed)

/-- Transactional choice is ordinary below both alternative fuel bounds. -/
theorem orElse_fuelTotalityContract
    (first second : Parser YulStmt) (firstFuel secondFuel : Nat)
    (firstContract : FuelYulStatementTotalityContract first firstFuel)
    (secondContract : FuelYulStatementTotalityContract second secondFuel) :
    FuelYulStatementTotalityContract (orElse first second)
      (Nat.min firstFuel secondFuel) := {
  toYulStatementParserContracts := {
    validFor := Parser.orElse_validFor firstContract.validFor
      secondContract.validFor
    preservesTokens := Parser.orElse_preservesTokensOnSuccess
      firstContract.preservesTokens secondContract.preservesTokens
    cursorMonotone := Parser.orElse_cursorMonotoneOnSuccess
      firstContract.cursorMonotone secondContract.cursorMonotone
    startsAtToken := Parser.orElse_startsAtCurrentTokenOnSuccess
      firstContract.startsAtToken secondContract.startsAtToken
  }
  preservesTokenWindow := Parser.orElse_preservesTokenWindow
    firstContract.preservesTokenWindow secondContract.preservesTokenWindow
  ordinary := by
    intro input inputValid adequate
    rcases firstContract.ordinary input inputValid (adequate_left adequate) with
      ⟨value, next, firstResult⟩ | ⟨failure, rejected, firstResult⟩
    · exact Or.inl ⟨value, next, by
        simp only [orElse, firstResult]⟩
    · rcases secondContract.ordinary input inputValid
          (adequate_right adequate) with
        ⟨value, next, secondResult⟩ |
        ⟨failure, rejected, secondResult⟩
      · exact Or.inl ⟨value, next, by
          simp only [orElse, firstResult, secondResult]⟩
      · exact Or.inr ⟨failure, rejected, by
          simp only [orElse, firstResult, secondResult]⟩
}

theorem orElse_cursor_lt_onSuccess_of_strict
    (first second : Parser YulStmt)
    (firstStrict : ∀ {input next : State} {value : YulStmt},
      first input = .ok value next → input.cursor < next.cursor)
    (secondStrict : ∀ {input next : State} {value : YulStmt},
      second input = .ok value next → input.cursor < next.cursor)
    {input final : State} {value : YulStmt}
    (parsed : orElse first second input = .ok value final) :
    input.cursor < final.cursor := by
  unfold orElse at parsed
  cases firstResult : first input with
  | invariant error => simp [firstResult] at parsed
  | ok firstValue next =>
      simp only [firstResult] at parsed
      cases parsed
      exact firstStrict firstResult
  | reject failure rejected =>
      simp only [firstResult] at parsed
      exact secondStrict parsed

end Solcore.Syntax.Parser
