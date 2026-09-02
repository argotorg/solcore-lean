import Solcore.Syntax.DeclarativeNestingOutcomeProperties
import Solcore.Syntax.Parser.Nesting

/-! Exact correspondence between executable and declarative nesting scans. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- The executable checker always exposes one exact declarative outcome. -/
theorem checkNesting_reflects_outcome (tokens : List Token) :
    ∃ result,
      DeclarativeGrammar.NestingOutcome tokens result ∧
        checkNesting tokens = result.map nestingOverflowDiagnostic := by
  rcases DeclarativeGrammar.nestingOutcome_total tokens with
    clears | ⟨overflow, exceeds⟩
  · exact ⟨none, clears, checkNesting_eq_map_of_outcome clears⟩
  · exact ⟨some overflow, exceeds,
      checkNesting_eq_map_of_outcome exceeds⟩

/-- Executable success is equivalent to a clear declarative nesting scan. -/
theorem checkNesting_none_iff_nestingClears (tokens : List Token) :
    checkNesting tokens = none ↔
      DeclarativeGrammar.NestingClears tokens := by
  constructor
  · intro checked
    rcases checkNesting_reflects_outcome tokens with
      ⟨result, outcome, equation⟩
    rw [checked] at equation
    cases result with
    | none => exact outcome
    | some overflow => simp at equation
  · intro clears
    simpa using checkNesting_eq_map_of_outcome clears

/-- An executable diagnostic is exactly the mapped first declarative
overflow, including its span, dimension, and canonical bound. -/
theorem checkNesting_some_iff_nestingExceeds
    (tokens : List Token) (diagnostic : ParseDiagnostic) :
    checkNesting tokens = some diagnostic ↔
      ∃ overflow,
        DeclarativeGrammar.NestingExceeds tokens overflow ∧
          diagnostic = nestingOverflowDiagnostic overflow := by
  constructor
  · intro checked
    rcases checkNesting_reflects_outcome tokens with
      ⟨result, outcome, equation⟩
    rw [checked] at equation
    cases result with
    | none => simp at equation
    | some overflow =>
        exact ⟨overflow, outcome, Option.some.inj equation⟩
  · rintro ⟨overflow, exceeds, rfl⟩
    simpa using checkNesting_eq_map_of_outcome exceeds

/-- Package both ordinary executable nesting outcomes. -/
theorem checkNesting_ordinaryOutcome_sound (tokens : List Token) :
    (checkNesting tokens = none →
      DeclarativeGrammar.NestingClears tokens) ∧
    (∀ diagnostic, checkNesting tokens = some diagnostic →
      ∃ overflow,
        DeclarativeGrammar.NestingExceeds tokens overflow ∧
          diagnostic = nestingOverflowDiagnostic overflow) :=
  ⟨(checkNesting_none_iff_nestingClears tokens).mp,
    fun diagnostic =>
      (checkNesting_some_iff_nestingExceeds tokens diagnostic).mp⟩

end Solcore.Syntax.Parser
