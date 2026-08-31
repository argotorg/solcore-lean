import Solcore.Syntax.Parser.PatternArgumentsFuelTotalityProperties

/-! Fuel-aware totality for leading-dot constructor patterns. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.PatternInternals

theorem dotConstructorPattern_ordinary_of_elementFuel
    (nested : Parser Pattern) (nestedFuel : Nat)
    (contract : FuelElementTotalityContract nested nestedFuel)
    (input : State) (inputValid : input.ValidFor)
    (adequate : input.remainingCount < nestedFuel + 1) :
    (∃ pattern next,
      dotConstructorPattern nested input = .ok pattern next) ∨
    (∃ failure next,
      dotConstructorPattern nested input = .reject failure next) := by
  rcases (symbol_ordinary .dot .pattern) input with
    ⟨dot, afterDot, dotResult⟩ | ⟨failure, rejected, dotResult⟩
  · have dotValid := symbol_validFor .dot .pattern input inputValid
    rw [dotResult] at dotValid
    have dotWindow := symbol_preservesTokenWindow .dot .pattern input
    rw [dotResult] at dotWindow
    have afterDotAdequate : afterDot.remainingCount < nestedFuel :=
      remainingCount_lt_after_strict_progress dotValid.2.1 dotWindow.2
        (acceptToken_cursor_lt_onSuccess (.symbol .dot) .pattern
          (· == .symbol .dot) dotResult) adequate
    rcases patternName_ordinary afterDot with
      ⟨name, afterName, nameResult⟩ | ⟨failure, rejected, nameResult⟩
    · have nameValid := patternName_validFor afterDot dotValid.2.1
      rw [nameResult] at nameValid
      have nameWindow := patternName_preservesTokenWindow afterDot
      rw [nameResult] at nameWindow
      have afterNameAdequate : afterName.remainingCount < nestedFuel :=
        remainingCount_lt_of_cursor_le nameWindow.2
          (Nat.le_of_lt (patternName_cursor_lt_onSuccess nameResult))
          afterDotAdequate
      rcases optionalConstructorArguments_ordinary_of_elementFuel nested
          nestedFuel contract afterName nameValid.2.1 (by omega) with
        ⟨arguments, final, argumentsResult⟩ |
        ⟨failure, rejected, argumentsResult⟩
      · let endSpan := arguments.map (fun values => values.span) |>.getD name.span
        exact Or.inl ⟨{
            span := SourceSpan.cover dot.span endSpan
            value := .constructor (some dot.span) [] name arguments
          }, final, by
            simp only [dotConstructorPattern, bind, dotResult, nameResult,
              argumentsResult, pure]
            rfl⟩
      · exact Or.inr ⟨failure, rejected, by
          simp only [dotConstructorPattern, bind, dotResult, nameResult,
            argumentsResult]⟩
    · exact Or.inr ⟨failure, rejected, by
        simp only [dotConstructorPattern, bind, dotResult, nameResult]⟩
  · exact Or.inr ⟨failure, rejected, by
      simp only [dotConstructorPattern, bind, dotResult]⟩

theorem dotConstructorPattern_ne_invariant_of_elementFuel
    (nested : Parser Pattern) (nestedFuel : Nat)
    (contract : FuelElementTotalityContract nested nestedFuel)
    (input : State) (inputValid : input.ValidFor)
    (adequate : input.remainingCount < nestedFuel + 1)
    (error : ParserInvariantError) :
    dotConstructorPattern nested input ≠ .invariant error := by
  intro failed
  rcases dotConstructorPattern_ordinary_of_elementFuel nested nestedFuel
      contract input inputValid adequate with
    ⟨pattern, next, result⟩ | ⟨failure, next, result⟩ <;>
    rw [result] at failed <;> contradiction

end Solcore.Syntax.Parser.PatternInternals
