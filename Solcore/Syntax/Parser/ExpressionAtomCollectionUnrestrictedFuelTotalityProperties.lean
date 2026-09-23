import Solcore.Syntax.Parser.DelimitedUnrestrictedFuelTotalityProperties
import Solcore.Syntax.Parser.Expression.Atom

/-! Dot constructors and arrays use the actual no-trailing list policy under
the three-field unrestricted child contract. Only successful endIndex and
strict progress are assumed; child source, tokens, diagnostics, and rejection
States remain unconstrained. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ExpressionAtomInternals

theorem optionalDotConstructorArguments_ordinary_of_unrestrictedElementFuel
    (nested : Parser Expr) (nestedFuel : Nat)
    (contract : UnrestrictedFuelElementContract nested nestedFuel)
    (input : State) (adequate : input.remainingCount < nestedFuel + 1) :
    (∃ arguments next, optionalDotConstructorArguments nested input = .ok arguments next) ∨
    (∃ failure next, optionalDotConstructorArguments nested input = .reject failure next) := by
  cases present : isSymbol input .leftParen with
  | false => exact .inl ⟨none, input, by
      simp only [optionalDotConstructorArguments, getState, bind, present, Bool.false_eq_true, if_false, pure]⟩
  | true =>
      rcases delimitedWithPolicy_ordinary_of_unrestrictedElementFuel .leftParen .rightParen true false
        nested .expression .expression nestedFuel contract input adequate with
        ⟨values, next, result⟩ | ⟨failure, rejected, result⟩
      · exact .inl ⟨some values, next, by
          simp only [optionalDotConstructorArguments, getState, bind, present, if_true,
            delimitedNoTrailing, result, pure]⟩
      · exact .inr ⟨failure, rejected, by
          simp only [optionalDotConstructorArguments, getState, bind, present, if_true,
            delimitedNoTrailing, result]⟩

theorem optionalDotConstructorArguments_ne_invariant_of_unrestrictedElementFuel
    (nested : Parser Expr) (nestedFuel : Nat)
    (contract : UnrestrictedFuelElementContract nested nestedFuel)
    (input : State) (adequate : input.remainingCount < nestedFuel + 1) (error : ParserInvariantError) :
    optionalDotConstructorArguments nested input ≠ .invariant error := by
  intro failed
  rcases optionalDotConstructorArguments_ordinary_of_unrestrictedElementFuel nested nestedFuel contract input adequate with
    ⟨value, next, result⟩ | ⟨failure, next, result⟩ <;> rw [result] at failed <;> contradiction

theorem dotConstructor_ordinary_of_unrestrictedElementFuel
    (nested : Parser Expr) (nestedFuel : Nat)
    (contract : UnrestrictedFuelElementContract nested nestedFuel)
    (input : State) (adequate : input.remainingCount < nestedFuel + 1) :
    (∃ value next, dotConstructor nested input = .ok value next) ∨
    (∃ failure next, dotConstructor nested input = .reject failure next) := by
  rcases symbol_ordinary .dot .expression input with
    ⟨dot, afterDot, dotResult⟩ | ⟨failure, rejected, dotResult⟩
  · have afterDotAdequate := symbol_remainingCount_lt_of_success .dot .expression dotResult adequate
    rcases expressionName_ordinary afterDot with
      ⟨name, afterName, nameResult⟩ | ⟨failure, rejected, nameResult⟩
    · have nameWindow := expressionName_preservesTokenWindow afterDot
      rw [nameResult] at nameWindow
      have afterNameAdequate : afterName.remainingCount < nestedFuel :=
        remainingCount_lt_of_endIndex_eq (congrArg TokenWindow.endIndex nameWindow.2)
          (Nat.le_of_lt (expressionName_cursor_lt_onSuccess nameResult)) afterDotAdequate
      rcases optionalDotConstructorArguments_ordinary_of_unrestrictedElementFuel nested nestedFuel contract
        afterName (by omega) with ⟨arguments, final, argumentResult⟩ | ⟨failure, rejected, argumentResult⟩
      · let endSpan := arguments.map (fun values => values.span) |>.getD name.span
        exact .inl ⟨{
            span := SourceSpan.cover dot.span endSpan
            value := .dotConstructor dot.span name arguments
          }, final, by simp only [dotConstructor, bind, dotResult, nameResult, argumentResult, pure]; rfl⟩
      · exact .inr ⟨failure, rejected, by simp only [dotConstructor, bind, dotResult, nameResult, argumentResult]⟩
    · exact .inr ⟨failure, rejected, by simp only [dotConstructor, bind, dotResult, nameResult]⟩
  · exact .inr ⟨failure, rejected, by simp only [dotConstructor, bind, dotResult]⟩

theorem dotConstructor_ne_invariant_of_unrestrictedElementFuel
    (nested : Parser Expr) (nestedFuel : Nat)
    (contract : UnrestrictedFuelElementContract nested nestedFuel)
    (input : State) (adequate : input.remainingCount < nestedFuel + 1) (error : ParserInvariantError) :
    dotConstructor nested input ≠ .invariant error := by
  intro failed
  rcases dotConstructor_ordinary_of_unrestrictedElementFuel nested nestedFuel contract input adequate with
    ⟨value, next, result⟩ | ⟨failure, next, result⟩ <;> rw [result] at failed <;> contradiction

theorem arrayLiteral_ordinary_of_unrestrictedElementFuel
    (nested : Parser Expr) (nestedFuel : Nat)
    (contract : UnrestrictedFuelElementContract nested nestedFuel)
    (input : State) (adequate : input.remainingCount < nestedFuel + 1) :
    (∃ value next, arrayLiteral nested input = .ok value next) ∨
    (∃ failure next, arrayLiteral nested input = .reject failure next) := by
  rcases delimitedWithPolicy_ordinary_of_unrestrictedElementFuel .leftBracket .rightBracket true false
    nested .expression .expression nestedFuel contract input adequate with
    ⟨values, next, result⟩ | ⟨failure, rejected, result⟩
  · exact .inl ⟨{ span := values.span, value := .array values }, next, by
      simp only [arrayLiteral, bind, delimitedNoTrailing, result, pure]⟩
  · exact .inr ⟨failure, rejected, by simp only [arrayLiteral, bind, delimitedNoTrailing, result]⟩

theorem arrayLiteral_ne_invariant_of_unrestrictedElementFuel
    (nested : Parser Expr) (nestedFuel : Nat)
    (contract : UnrestrictedFuelElementContract nested nestedFuel)
    (input : State) (adequate : input.remainingCount < nestedFuel + 1) (error : ParserInvariantError) :
    arrayLiteral nested input ≠ .invariant error := by
  intro failed
  rcases arrayLiteral_ordinary_of_unrestrictedElementFuel nested nestedFuel contract input adequate with
    ⟨value, next, result⟩ | ⟨failure, next, result⟩ <;> rw [result] at failed <;> contradiction

end Solcore.Syntax.Parser.ExpressionAtomInternals
