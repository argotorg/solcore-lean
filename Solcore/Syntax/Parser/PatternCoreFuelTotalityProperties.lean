import Solcore.Syntax.Parser.PatternConstructorFuelTotalityProperties
import Solcore.Syntax.Parser.PatternLeafFuelTotalityProperties
import Solcore.Syntax.Parser.PatternQualifiedFuelTotalityProperties
import Solcore.Syntax.Parser.PatternTupleTotalityProperties

/-! Fuel-aware totality for canonical pattern-layer dispatch. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.PatternInternals

/--
Every non-recovering pattern branch is ordinary when both recursive consumers
receive one unit beyond their fixed fuel bounds.
-/
theorem patternCore_ordinary_of_elementFuel
    (nested : Parser Pattern) (expression : Parser Expr)
    (nestedFuel expressionFuel : Nat)
    (nestedContract : FuelElementTotalityContract nested nestedFuel)
    (expressionContract :
      FuelElementTotalityContract expression expressionFuel)
    (input : State) (inputValid : input.ValidFor)
    (nestedAdequate : input.remainingCount < nestedFuel + 1)
    (expressionAdequate : input.remainingCount < expressionFuel + 1) :
    (∃ pattern next, patternCore nested expression input = .ok pattern next) ∨
    (∃ failure next,
      patternCore nested expression input = .reject failure next) := by
  unfold patternCore
  split
  · exact wildcardPattern_ordinary input
  · split
    · exact literalPattern_ordinary input
    · split
      · exact booleanBinderPattern_ordinary input
      · split
        · exact parenthesizedPattern_ordinary_of_elementFuel nested nestedFuel
            nestedContract input inputValid nestedAdequate
        · split
          · exact dotConstructorPattern_ordinary_of_elementFuel nested
              nestedFuel nestedContract input inputValid nestedAdequate
          · split
            · exact comptimePattern_ordinary_of_elementFuel expression
                expressionFuel expressionContract input inputValid
                expressionAdequate
            · split
              · exact qualifiedPattern_ordinary_of_elementFuel nested nestedFuel
                  nestedContract input inputValid nestedAdequate
              · exact Or.inr ⟨_, input, rfl⟩

theorem patternCore_ne_invariant_of_elementFuel
    (nested : Parser Pattern) (expression : Parser Expr)
    (nestedFuel expressionFuel : Nat)
    (nestedContract : FuelElementTotalityContract nested nestedFuel)
    (expressionContract :
      FuelElementTotalityContract expression expressionFuel)
    (input : State) (inputValid : input.ValidFor)
    (nestedAdequate : input.remainingCount < nestedFuel + 1)
    (expressionAdequate : input.remainingCount < expressionFuel + 1)
    (error : ParserInvariantError) :
    patternCore nested expression input ≠ .invariant error := by
  intro failed
  rcases patternCore_ordinary_of_elementFuel nested expression nestedFuel
      expressionFuel nestedContract expressionContract input inputValid
      nestedAdequate expressionAdequate with
    ⟨pattern, next, result⟩ | ⟨failure, next, result⟩ <;>
      rw [result] at failed <;> contradiction

end Solcore.Syntax.Parser.PatternInternals
