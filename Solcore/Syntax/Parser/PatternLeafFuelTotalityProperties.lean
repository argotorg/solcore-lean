import Solcore.Syntax.Parser.DelimitedFuelTotalityProperties
import Solcore.Syntax.Parser.PatternLeafTotalityProperties

/-! Recursive-fuel totality for comptime pattern leaves. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.PatternInternals

/--
Consuming the `comptime` marker places the recursive expression call below its
fixed fuel bound.
-/
theorem comptimePattern_ordinary_of_elementFuel
    (expression : Parser Expr) (expressionFuel : Nat)
    (contract : FuelElementTotalityContract expression expressionFuel)
    (input : State) (inputValid : input.ValidFor)
    (adequate : input.remainingCount < expressionFuel + 1) :
    (∃ pattern next, comptimePattern expression input = .ok pattern next) ∨
    (∃ failure next,
      comptimePattern expression input = .reject failure next) := by
  rcases (contextual_ordinary .comptime .pattern) input with
    ⟨marker, afterMarker, markerResult⟩ |
    ⟨failure, rejected, markerResult⟩
  · have markerValid := contextual_validFor .comptime .pattern
      input inputValid
    rw [markerResult] at markerValid
    have markerWindow := contextual_preservesTokenWindow
      .comptime .pattern input
    rw [markerResult] at markerWindow
    have markerProgress : input.cursor < afterMarker.cursor :=
      acceptToken_cursor_lt_onSuccess (.contextual .comptime) .pattern
        (·.isContextual .comptime) markerResult
    have expressionAdequate :
        afterMarker.remainingCount < expressionFuel :=
      remainingCount_lt_after_strict_progress markerValid.2.1
        markerWindow.2 markerProgress adequate
    rcases contract.ordinary afterMarker markerValid.2.1
        expressionAdequate with
      ⟨value, next, valueResult⟩ | ⟨failure, rejected, valueResult⟩
    · exact Or.inl ⟨{
          span := SourceSpan.cover marker.span value.span
          value := .comptime marker.span value
        }, next, by
          simp only [comptimePattern, markerResult, valueResult]⟩
    · exact Or.inr ⟨failure, rejected, by
        simp only [comptimePattern, markerResult, valueResult]⟩
  · exact Or.inr ⟨failure, rejected, by
      simp only [comptimePattern, markerResult]⟩

theorem comptimePattern_ne_invariant_of_elementFuel
    (expression : Parser Expr) (expressionFuel : Nat)
    (contract : FuelElementTotalityContract expression expressionFuel)
    (input : State) (inputValid : input.ValidFor)
    (adequate : input.remainingCount < expressionFuel + 1)
    (error : ParserInvariantError) :
    comptimePattern expression input ≠ .invariant error := by
  intro failed
  rcases comptimePattern_ordinary_of_elementFuel expression expressionFuel
      contract input inputValid adequate with
    ⟨pattern, next, result⟩ | ⟨failure, next, result⟩ <;>
    rw [result] at failed <;> contradiction

end Solcore.Syntax.Parser.PatternInternals
