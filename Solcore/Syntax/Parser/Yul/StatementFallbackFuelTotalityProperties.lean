import Solcore.Syntax.Parser.Yul.StatementLeafTotalityProperties

/-! Fuel-aware totality across Yul statement fallback and termination. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Syntax/state laws paired with a bounded ordinary Yul statement parser. -/
structure FuelYulStatementTotalityContract
    (parser : Parser YulStmt) (fuel : Nat) : Prop
    extends YulStatementParserContracts parser where
  preservesTokenWindow : Parser.PreservesTokenWindow parser
  ordinary : ∀ input, input.ValidFor → input.remainingCount < fuel →
    (∃ value next, parser input = .ok value next) ∨
      (∃ failure next, parser input = .reject failure next)

namespace FuelYulStatementTotalityContract

/-- A Yul statement contract at a larger fuel bound proves every smaller bound. -/
theorem weaken {parser : Parser YulStmt} {smallFuel largeFuel : Nat}
    (contract : FuelYulStatementTotalityContract parser largeFuel)
    (bound : smallFuel ≤ largeFuel) :
    FuelYulStatementTotalityContract parser smallFuel := {
  toYulStatementParserContracts := contract.toYulStatementParserContracts
  preservesTokenWindow := contract.preservesTokenWindow
  ordinary := fun input inputValid adequate =>
    contract.ordinary input inputValid
      (Nat.lt_of_lt_of_le adequate bound)
}

theorem ne_invariant {parser : Parser YulStmt} {fuel : Nat}
    (contract : FuelYulStatementTotalityContract parser fuel)
    (input : State) (inputValid : input.ValidFor)
    (adequate : input.remainingCount < fuel)
    (error : ParserInvariantError) :
    parser input ≠ .invariant error := by
  intro failed
  rcases contract.ordinary input inputValid adequate with
    ⟨value, next, result⟩ | ⟨failure, next, result⟩ <;>
    rw [result] at failed <;> contradiction

/-- An unconditionally total leaf is fuel-total for every chosen bound. -/
theorem ofTotality {parser : Parser YulStmt}
    (contract : YulStatementTotalityContract parser) (fuel : Nat) :
    FuelYulStatementTotalityContract parser fuel := {
  toYulStatementParserContracts := contract.toYulStatementParserContracts
  preservesTokenWindow := contract.preservesTokenWindow
  ordinary := fun input inputValid _ => contract.invariantFree input inputValid
}

end FuelYulStatementTotalityContract

/-- Recognized fallback is ordinary below both branch fuel bounds. -/
theorem recognizedYulStatementOrFallback_ordinary_of_fuels
    (primary fallback : Parser YulStmt) (primaryFuel fallbackFuel : Nat)
    (primaryContract :
      FuelYulStatementTotalityContract primary primaryFuel)
    (fallbackContract :
      FuelYulStatementTotalityContract fallback fallbackFuel)
    (input : State) (inputValid : input.ValidFor)
    (adequate : input.remainingCount < Nat.min primaryFuel fallbackFuel) :
    (∃ value next,
      recognizedYulStatementOrFallback primary fallback input =
        .ok value next) ∨
    (∃ failure next,
      recognizedYulStatementOrFallback primary fallback input =
        .reject failure next) := by
  have primaryAdequate : input.remainingCount < primaryFuel :=
    Nat.lt_of_lt_of_le adequate (Nat.min_le_left primaryFuel fallbackFuel)
  have fallbackAdequate : input.remainingCount < fallbackFuel :=
    Nat.lt_of_lt_of_le adequate (Nat.min_le_right primaryFuel fallbackFuel)
  rcases primaryContract.ordinary input inputValid primaryAdequate with
    ⟨value, next, primaryResult⟩ |
    ⟨failure, rejected, primaryResult⟩
  · exact Or.inl ⟨value, next, by
      simp only [recognizedYulStatementOrFallback, primaryResult]⟩
  · rcases fallbackContract.ordinary input inputValid fallbackAdequate with
      ⟨value, next, fallbackResult⟩ |
      ⟨fallbackFailure, fallbackRejected, fallbackResult⟩
    · let reset : State := {
        next with diagnosticsRev := input.diagnosticsRev
      }
      exact Or.inl ⟨value, reset.emit failure.toDiagnostic, by
        simp only [recognizedYulStatementOrFallback, primaryResult,
          fallbackResult, reset]⟩
    · exact Or.inr ⟨failure, input, by
        simp only [recognizedYulStatementOrFallback, primaryResult,
          fallbackResult]⟩

/-- Complete branch contracts compose through recognized fallback. -/
theorem recognizedYulStatementOrFallback_fuelTotalityContract
    (primary fallback : Parser YulStmt) (primaryFuel fallbackFuel : Nat)
    (primaryContract :
      FuelYulStatementTotalityContract primary primaryFuel)
    (fallbackContract :
      FuelYulStatementTotalityContract fallback fallbackFuel) :
    FuelYulStatementTotalityContract
      (recognizedYulStatementOrFallback primary fallback)
      (Nat.min primaryFuel fallbackFuel) := {
  toYulStatementParserContracts := {
    validFor := recognizedYulStatementOrFallback_validFor primary fallback
      primaryContract.validFor fallbackContract.validFor
    preservesTokens :=
      recognizedYulStatementOrFallback_preservesTokensOnSuccess_of_success
        primary fallback primaryContract.preservesTokens
          fallbackContract.preservesTokens
    cursorMonotone :=
      recognizedYulStatementOrFallback_cursorMonotoneOnSuccess primary
        fallback primaryContract.cursorMonotone fallbackContract.cursorMonotone
    startsAtToken :=
      recognizedYulStatementOrFallback_startsAtCurrentTokenOnSuccess primary
        fallback primaryContract.startsAtToken fallbackContract.startsAtToken
  }
  preservesTokenWindow :=
    recognizedYulStatementOrFallback_preservesTokenWindow primary fallback
      primaryContract.preservesTokenWindow
        fallbackContract.preservesTokenWindow
  ordinary := recognizedYulStatementOrFallback_ordinary_of_fuels primary
    fallback primaryFuel fallbackFuel primaryContract fallbackContract
}

/-- Optional semicolon consumption has only ordinary outcomes. -/
theorem optionalYulSemicolon_ordinary (value : YulStmt) :
    Parser.Ordinary (optionalYulSemicolon value) := by
  intro input
  unfold optionalYulSemicolon
  simp only [getState, bind]
  split
  · rcases (symbol_ordinary .semicolon .yulStatement) input with
      ⟨marker, next, markerResult⟩ |
      ⟨failure, rejected, markerResult⟩
    · exact Or.inl ⟨value, next, by simp only [markerResult, pure]⟩
    · exact Or.inr ⟨failure, rejected, by simp only [markerResult]⟩
  · exact Or.inl ⟨value, input, rfl⟩

/-- Optional termination preserves the core statement's fuel bound. -/
theorem yulStatementTerminated_ordinary_of_coreFuel
    (nested : Parser YulStmt) (fuel : Nat)
    (coreContract : FuelYulStatementTotalityContract
      (yulStatementCore nested) fuel)
    (input : State) (inputValid : input.ValidFor)
    (adequate : input.remainingCount < fuel) :
    (∃ value next,
      yulStatementTerminated nested input = .ok value next) ∨
    (∃ failure next,
      yulStatementTerminated nested input = .reject failure next) := by
  rcases coreContract.ordinary input inputValid adequate with
    ⟨value, afterCore, coreResult⟩ |
    ⟨failure, rejected, coreResult⟩
  · rcases optionalYulSemicolon_ordinary value afterCore with
      ⟨terminated, next, terminatedResult⟩ |
      ⟨failure, rejected, terminatedResult⟩
    · exact Or.inl ⟨terminated, next, by
        simp only [yulStatementTerminated, bind, coreResult,
          terminatedResult]⟩
    · exact Or.inr ⟨failure, rejected, by
        simp only [yulStatementTerminated, bind, coreResult,
          terminatedResult]⟩
  · exact Or.inr ⟨failure, rejected, by
      simp only [yulStatementTerminated, bind, coreResult]⟩

theorem yulStatementTerminated_fuelTotalityContract
    (nested : Parser YulStmt) (fuel : Nat)
    (nestedValid : nested.ValidFor YulStmt.ValidFor)
    (nestedPreserves : Parser.PreservesTokensOnSuccess nested)
    (coreContract : FuelYulStatementTotalityContract
      (yulStatementCore nested) fuel) :
    FuelYulStatementTotalityContract
      (yulStatementTerminated nested) fuel := {
  toYulStatementParserContracts := {
    validFor := yulStatementTerminated_validFor nested nestedValid
      nestedPreserves
    preservesTokens := yulStatementTerminated_preservesTokensOnSuccess nested
      nestedValid nestedPreserves
    cursorMonotone := yulStatementTerminated_cursorMonotoneOnSuccess nested
      nestedValid nestedPreserves
    startsAtToken := yulStatementTerminated_startsAtCurrentTokenOnSuccess
      nested nestedValid nestedPreserves
  }
  preservesTokenWindow := yulStatementTerminated_preservesTokenWindow nested
    coreContract.preservesTokenWindow
  ordinary := yulStatementTerminated_ordinary_of_coreFuel nested fuel
    coreContract
}

end Solcore.Syntax.Parser
