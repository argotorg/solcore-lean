import Solcore.Syntax.Parser.TermStatementFallbackFuelTotalityProperties
import Solcore.Syntax.Parser.TermStatementTotalityProperties

/-! Fuel-total fallback and state-selected Core statement choices. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.TermInternals

private theorem adequate_left {left right count : Nat}
    (adequate : count < Nat.min left right) : count < left :=
  Nat.lt_of_lt_of_le adequate (Nat.min_le_left left right)

private theorem adequate_right {left right count : Nat}
    (adequate : count < Nat.min left right) : count < right :=
  Nat.lt_of_lt_of_le adequate (Nat.min_le_right left right)

namespace FuelStatementTotalityContract

/-- An unconditionally total branch is fuel-total at any chosen bound. -/
theorem ofTotality
    {valueValid : SourceFile → Statement → Prop}
    {parser : Parser Statement}
    (contract : StatementTotalityContract valueValid parser) (fuel : Nat) :
    FuelStatementTotalityContract valueValid parser fuel := {
  toStatementParserContract := contract.toStatementParserContract
  ordinary := fun input inputValid _ => contract.invariantFree input inputValid
}

end FuelStatementTotalityContract

/-- Recognized fallback is ordinary below both branch fuel bounds. -/
theorem recognizedStatementOrFallback_ordinary_of_fuels
    {valueValid : SourceFile → Statement → Prop}
    (primary fallback : Parser Statement) (primaryFuel fallbackFuel : Nat)
    (primaryContract :
      FuelStatementTotalityContract valueValid primary primaryFuel)
    (fallbackContract :
      FuelStatementTotalityContract valueValid fallback fallbackFuel)
    (input : State) (inputValid : input.ValidFor)
    (adequate : input.remainingCount < Nat.min primaryFuel fallbackFuel) :
    (∃ value next,
      recognizedStatementOrFallback primary fallback input = .ok value next) ∨
    (∃ failure next,
      recognizedStatementOrFallback primary fallback input =
        .reject failure next) := by
  rcases primaryContract.ordinary input inputValid (adequate_left adequate) with
    ⟨value, next, primaryResult⟩ |
    ⟨failure, rejected, primaryResult⟩
  · exact Or.inl ⟨value, next, by
      simp only [recognizedStatementOrFallback, primaryResult]⟩
  · rcases fallbackContract.ordinary input inputValid
        (adequate_right adequate) with
      ⟨value, next, fallbackResult⟩ |
      ⟨fallbackFailure, fallbackRejected, fallbackResult⟩
    · let reset : State := {
        next with diagnosticsRev := input.diagnosticsRev
      }
      exact Or.inl ⟨value, reset.emit failure.toDiagnostic, by
        simp only [recognizedStatementOrFallback, primaryResult,
          fallbackResult, reset]⟩
    · exact Or.inr ⟨failure, input, by
        simp only [recognizedStatementOrFallback, primaryResult,
          fallbackResult]⟩

theorem recognizedStatementOrFallback_fuelTotalityContract
    {valueValid : SourceFile → Statement → Prop}
    (primary fallback : Parser Statement) (primaryFuel fallbackFuel : Nat)
    (primaryContract :
      FuelStatementTotalityContract valueValid primary primaryFuel)
    (fallbackContract :
      FuelStatementTotalityContract valueValid fallback fallbackFuel) :
    FuelStatementTotalityContract valueValid
      (recognizedStatementOrFallback primary fallback)
      (Nat.min primaryFuel fallbackFuel) := {
  toStatementParserContract := recognizedStatementOrFallback_contract
    primary fallback primaryContract.toStatementParserContract
      fallbackContract.toStatementParserContract
  ordinary := recognizedStatementOrFallback_ordinary_of_fuels primary fallback
    primaryFuel fallbackFuel primaryContract fallbackContract
}

theorem recognizedStatementOrFallback_cursor_lt_onSuccess_of_strict
    (primary fallback : Parser Statement)
    (primaryStrict : ∀ {input next : State} {value : Statement},
      primary input = .ok value next → input.cursor < next.cursor)
    (fallbackStrict : ∀ {input next : State} {value : Statement},
      fallback input = .ok value next → input.cursor < next.cursor)
    {input final : State} {value : Statement}
    (parsed : recognizedStatementOrFallback primary fallback input =
      .ok value final) :
    input.cursor < final.cursor := by
  unfold recognizedStatementOrFallback at parsed
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

/-- State-selected dispatch preserves both branch contracts and fuel bounds. -/
theorem stateChoice_fuelTotalityContract
    {valueValid : SourceFile → Statement → Prop}
    (condition : State → Bool) (first second : Parser Statement)
    (firstFuel secondFuel : Nat)
    (firstContract :
      FuelStatementTotalityContract valueValid first firstFuel)
    (secondContract :
      FuelStatementTotalityContract valueValid second secondFuel) :
    FuelStatementTotalityContract valueValid
      (fun input => if condition input then first input else second input)
      (Nat.min firstFuel secondFuel) := {
  toStatementParserContract := {
    validFor := by
      intro input inputValid
      by_cases selected : condition input = true
      · simpa [selected] using firstContract.validFor input inputValid
      · simpa [selected] using secondContract.validFor input inputValid
    preservesTokenWindow := by
      intro input
      by_cases selected : condition input = true
      · simpa [selected] using firstContract.preservesTokenWindow input
      · simpa [selected] using secondContract.preservesTokenWindow input
    cursorMonotoneOnSuccess := by
      intro input value next result
      by_cases selected : condition input = true
      · exact firstContract.cursorMonotoneOnSuccess input value next
          (by simpa [selected] using result)
      · exact secondContract.cursorMonotoneOnSuccess input value next
          (by simpa [selected] using result)
    startsAtCurrentTokenOnSuccess := by
      intro input value next result
      by_cases selected : condition input = true
      · exact firstContract.startsAtCurrentTokenOnSuccess input value next
          (by simpa [selected] using result)
      · exact secondContract.startsAtCurrentTokenOnSuccess input value next
          (by simpa [selected] using result)
  }
  ordinary := by
    intro input inputValid adequate
    by_cases selected : condition input = true
    · simpa [selected] using firstContract.ordinary input inputValid
        (adequate_left adequate)
    · simpa [selected] using secondContract.ordinary input inputValid
        (adequate_right adequate)
}

theorem stateChoice_cursor_lt_onSuccess_of_strict
    (condition : State → Bool) (first second : Parser Statement)
    (firstStrict : ∀ {input next : State} {value : Statement},
      first input = .ok value next → input.cursor < next.cursor)
    (secondStrict : ∀ {input next : State} {value : Statement},
      second input = .ok value next → input.cursor < next.cursor)
    {input final : State} {value : Statement}
    (parsed : (fun state => if condition state then first state
      else second state) input = .ok value final) :
    input.cursor < final.cursor := by
  by_cases selected : condition input = true
  · exact firstStrict (by simpa [selected] using parsed)
  · exact secondStrict (by simpa [selected] using parsed)

end Solcore.Syntax.Parser.TermInternals
