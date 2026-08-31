import Solcore.Syntax.Parser.DelimitedFuelTotalityProperties
import Solcore.Syntax.Parser.DelimitedNonemptyProperties
import Solcore.Syntax.Parser.PatternLeafFuelTotalityProperties

/-! Fuel-aware totality for recursive constructor-pattern arguments. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.PatternInternals

/-- A syntactically nonempty argument parse satisfies its defensive refinement. -/
theorem requirePatternArguments_ok_of_delimitedNoTrailing_false_ok
    (nested : Parser Pattern)
    {input afterDelimited : State} {parsed : DelimitedList Pattern}
    (parsedResult : delimitedNoTrailing .leftParen .rightParen false nested
      .pattern .pattern input = .ok parsed afterDelimited) :
    ∃ nonempty,
      requirePatternArguments parsed afterDelimited =
        .ok nonempty afterDelimited := by
  have nonempty := delimitedNoTrailing_false_elements_ne_nil_onSuccess
    .leftParen .rightParen nested .pattern .pattern parsedResult
  unfold requirePatternArguments
  cases elements : parsed.elements with
  | nil => exact False.elim (nonempty elements)
  | cons head tail => exact ⟨_, rfl⟩

theorem constructorArguments_ordinary_of_elementFuel
    (nested : Parser Pattern) (nestedFuel : Nat)
    (contract : FuelElementTotalityContract nested nestedFuel)
    (input : State) (inputValid : input.ValidFor)
    (adequate : input.remainingCount < nestedFuel + 1) :
    (∃ arguments next,
      constructorArguments nested input = .ok arguments next) ∨
    (∃ failure next,
      constructorArguments nested input = .reject failure next) := by
  rcases delimitedWithPolicy_ordinary_of_elementFuel
      .leftParen .rightParen false false nested .pattern .pattern
      nestedFuel contract input inputValid adequate with
    ⟨parsed, afterDelimited, parsedResult⟩ |
    ⟨failure, rejected, parsedResult⟩
  · have noTrailingResult :
        delimitedNoTrailing .leftParen .rightParen false nested
          .pattern .pattern input = .ok parsed afterDelimited := by
      simpa only [delimitedNoTrailing] using parsedResult
    rcases requirePatternArguments_ok_of_delimitedNoTrailing_false_ok
        nested noTrailingResult with ⟨nonempty, nonemptyResult⟩
    exact Or.inl ⟨nonempty, afterDelimited, by
      simp only [constructorArguments, bind, noTrailingResult,
        nonemptyResult]⟩
  · exact Or.inr ⟨failure, rejected, by
      simp only [constructorArguments, bind, delimitedNoTrailing,
        parsedResult]⟩

theorem constructorArguments_ne_invariant_of_elementFuel
    (nested : Parser Pattern) (nestedFuel : Nat)
    (contract : FuelElementTotalityContract nested nestedFuel)
    (input : State) (inputValid : input.ValidFor)
    (adequate : input.remainingCount < nestedFuel + 1)
    (error : ParserInvariantError) :
    constructorArguments nested input ≠ .invariant error := by
  intro failed
  rcases constructorArguments_ordinary_of_elementFuel nested nestedFuel
      contract input inputValid adequate with
    ⟨arguments, next, result⟩ | ⟨failure, next, result⟩ <;>
    rw [result] at failed <;> contradiction

theorem optionalConstructorArguments_ordinary_of_elementFuel
    (nested : Parser Pattern) (nestedFuel : Nat)
    (contract : FuelElementTotalityContract nested nestedFuel)
    (input : State) (inputValid : input.ValidFor)
    (adequate : input.remainingCount < nestedFuel + 1) :
    (∃ arguments next,
      optionalConstructorArguments nested input = .ok arguments next) ∨
    (∃ failure next,
      optionalConstructorArguments nested input = .reject failure next) := by
  by_cases present : isSymbol input .leftParen
  · rcases constructorArguments_ordinary_of_elementFuel nested nestedFuel
        contract input inputValid adequate with
      ⟨arguments, next, argumentsResult⟩ |
      ⟨failure, rejected, argumentsResult⟩
    · exact Or.inl ⟨some arguments, next, by
        simp only [optionalConstructorArguments, present, ↓reduceIte,
          orElse, argumentsResult, pure, bind]⟩
    · exact Or.inl ⟨none, input, by
        simp only [optionalConstructorArguments, present, ↓reduceIte,
          orElse, argumentsResult, pure, bind]⟩
  · have absent : isSymbol input .leftParen = false := by
      cases found : isSymbol input .leftParen with
      | false => rfl
      | true => exact False.elim (present found)
    exact Or.inl ⟨none, input, by
      simp only [optionalConstructorArguments, absent, Bool.false_eq_true,
        ↓reduceIte]⟩

theorem optionalConstructorArguments_ne_invariant_of_elementFuel
    (nested : Parser Pattern) (nestedFuel : Nat)
    (contract : FuelElementTotalityContract nested nestedFuel)
    (input : State) (inputValid : input.ValidFor)
    (adequate : input.remainingCount < nestedFuel + 1)
    (error : ParserInvariantError) :
    optionalConstructorArguments nested input ≠ .invariant error := by
  intro failed
  rcases optionalConstructorArguments_ordinary_of_elementFuel nested
      nestedFuel contract input inputValid adequate with
    ⟨arguments, next, result⟩ | ⟨failure, next, result⟩ <;>
    rw [result] at failed <;> contradiction

end Solcore.Syntax.Parser.PatternInternals
