import Solcore.Syntax.Parser.DelimitedFuelTotalityProperties
import Solcore.Syntax.Parser.Expression.AtomLeafTotalityProperties

/-! Fuel-aware totality for recursive delimited expression atoms. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ExpressionAtomInternals

/-- Optional leading-dot arguments inherit bounded delimited totality. -/
theorem optionalDotConstructorArguments_ordinary_of_elementFuel
    (nested : Parser Expr) (nestedFuel : Nat)
    (contract : FuelElementTotalityContract nested nestedFuel)
    (input : State) (inputValid : input.ValidFor)
    (adequate : input.remainingCount < nestedFuel + 1) :
    (∃ arguments next,
      optionalDotConstructorArguments nested input = .ok arguments next) ∨
    (∃ failure next,
      optionalDotConstructorArguments nested input = .reject failure next) := by
  by_cases present : isSymbol input .leftParen
  · rcases delimitedWithPolicy_ordinary_of_elementFuel .leftParen .rightParen
        true false nested .expression .expression nestedFuel contract input
        inputValid adequate with
      ⟨values, next, valuesResult⟩ | ⟨failure, rejected, valuesResult⟩
    · exact Or.inl ⟨some values, next, by
        simp only [optionalDotConstructorArguments, getState, bind, present,
          ↓reduceIte, delimitedNoTrailing, valuesResult, pure]⟩
    · exact Or.inr ⟨failure, rejected, by
        simp only [optionalDotConstructorArguments, getState, bind, present,
          ↓reduceIte, delimitedNoTrailing, valuesResult]⟩
  · have absent : isSymbol input .leftParen = false := by
      cases found : isSymbol input .leftParen with
      | false => rfl
      | true => exact False.elim (present found)
    exact Or.inl ⟨none, input, by
      simp only [optionalDotConstructorArguments, getState, bind, absent,
        Bool.false_eq_true, ↓reduceIte, pure]⟩

theorem optionalDotConstructorArguments_ne_invariant_of_elementFuel
    (nested : Parser Expr) (nestedFuel : Nat)
    (contract : FuelElementTotalityContract nested nestedFuel)
    (input : State) (inputValid : input.ValidFor)
    (adequate : input.remainingCount < nestedFuel + 1)
    (error : ParserInvariantError) :
    optionalDotConstructorArguments nested input ≠ .invariant error := by
  intro failed
  rcases optionalDotConstructorArguments_ordinary_of_elementFuel nested
      nestedFuel contract input inputValid adequate with
    ⟨arguments, next, result⟩ | ⟨failure, next, result⟩ <;>
    rw [result] at failed <;> contradiction

/-- A leading-dot constructor spends its outer fuel before recursive arguments. -/
theorem dotConstructor_ordinary_of_elementFuel
    (nested : Parser Expr) (nestedFuel : Nat)
    (contract : FuelElementTotalityContract nested nestedFuel)
    (input : State) (inputValid : input.ValidFor)
    (adequate : input.remainingCount < nestedFuel + 1) :
    (∃ expression next, dotConstructor nested input = .ok expression next) ∨
    (∃ failure next, dotConstructor nested input = .reject failure next) := by
  rcases (symbol_ordinary .dot .expression) input with
    ⟨dot, afterDot, dotResult⟩ | ⟨failure, rejected, dotResult⟩
  · have dotValid := symbol_validFor .dot .expression input inputValid
    rw [dotResult] at dotValid
    have dotWindow := symbol_preservesTokenWindow .dot .expression input
    rw [dotResult] at dotWindow
    have afterDotAdequate : afterDot.remainingCount < nestedFuel :=
      remainingCount_lt_after_strict_progress dotValid.2.1 dotWindow.2
        (acceptToken_cursor_lt_onSuccess (.symbol .dot) .expression
          (· == .symbol .dot) dotResult) adequate
    rcases expressionName_ordinary afterDot with
      ⟨name, afterName, nameResult⟩ | ⟨failure, rejected, nameResult⟩
    · have nameValid := expressionName_validFor afterDot dotValid.2.1
      rw [nameResult] at nameValid
      have nameWindow := expressionName_preservesTokenWindow afterDot
      rw [nameResult] at nameWindow
      have afterNameAdequate : afterName.remainingCount < nestedFuel :=
        remainingCount_lt_of_cursor_le nameWindow.2
          (Nat.le_of_lt (expressionName_cursor_lt_onSuccess nameResult))
          afterDotAdequate
      rcases optionalDotConstructorArguments_ordinary_of_elementFuel nested
          nestedFuel contract afterName nameValid.2.1 (by omega) with
        ⟨arguments, final, argumentsResult⟩ |
        ⟨failure, rejected, argumentsResult⟩
      · let endSpan := arguments.map (fun values => values.span) |>.getD name.span
        exact Or.inl ⟨{
            span := SourceSpan.cover dot.span endSpan
            value := .dotConstructor dot.span name arguments
          }, final, by
            simp only [dotConstructor, bind, dotResult, nameResult,
              argumentsResult, pure]
            rfl⟩
      · exact Or.inr ⟨failure, rejected, by
          simp only [dotConstructor, bind, dotResult, nameResult,
            argumentsResult]⟩
    · exact Or.inr ⟨failure, rejected, by
        simp only [dotConstructor, bind, dotResult, nameResult]⟩
  · exact Or.inr ⟨failure, rejected, by
      simp only [dotConstructor, bind, dotResult]⟩

theorem dotConstructor_ne_invariant_of_elementFuel
    (nested : Parser Expr) (nestedFuel : Nat)
    (contract : FuelElementTotalityContract nested nestedFuel)
    (input : State) (inputValid : input.ValidFor)
    (adequate : input.remainingCount < nestedFuel + 1)
    (error : ParserInvariantError) :
    dotConstructor nested input ≠ .invariant error := by
  intro failed
  rcases dotConstructor_ordinary_of_elementFuel nested nestedFuel contract
      input inputValid adequate with
    ⟨expression, next, result⟩ | ⟨failure, next, result⟩ <;>
    rw [result] at failed <;> contradiction

/-- Array literals inherit bounded no-trailing delimited totality. -/
theorem arrayLiteral_ordinary_of_elementFuel
    (nested : Parser Expr) (nestedFuel : Nat)
    (contract : FuelElementTotalityContract nested nestedFuel)
    (input : State) (inputValid : input.ValidFor)
    (adequate : input.remainingCount < nestedFuel + 1) :
    (∃ expression next, arrayLiteral nested input = .ok expression next) ∨
    (∃ failure next, arrayLiteral nested input = .reject failure next) := by
  rcases delimitedWithPolicy_ordinary_of_elementFuel .leftBracket .rightBracket
      true false nested .expression .expression nestedFuel contract input
      inputValid adequate with
    ⟨values, next, valuesResult⟩ | ⟨failure, rejected, valuesResult⟩
  · exact Or.inl ⟨{
        span := values.span
        value := .array values
      }, next, by
        unfold arrayLiteral
        simp only [delimitedNoTrailing, valuesResult, bind, pure]⟩
  · exact Or.inr ⟨failure, rejected, by
      unfold arrayLiteral
      simp only [delimitedNoTrailing, valuesResult, bind]⟩

theorem arrayLiteral_ne_invariant_of_elementFuel
    (nested : Parser Expr) (nestedFuel : Nat)
    (contract : FuelElementTotalityContract nested nestedFuel)
    (input : State) (inputValid : input.ValidFor)
    (adequate : input.remainingCount < nestedFuel + 1)
    (error : ParserInvariantError) :
    arrayLiteral nested input ≠ .invariant error := by
  intro failed
  rcases arrayLiteral_ordinary_of_elementFuel nested nestedFuel contract input
      inputValid adequate with
    ⟨expression, next, result⟩ | ⟨failure, next, result⟩ <;>
    rw [result] at failed <;> contradiction

end Solcore.Syntax.Parser.ExpressionAtomInternals
