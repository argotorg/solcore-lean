import Solcore.Syntax.Parser.DelimitedNonemptyProperties
import Solcore.Syntax.Parser.DelimitedTotalityProperties
import Solcore.Syntax.Parser.InvariantFreeProperties
import Solcore.Syntax.Parser.PrimitiveTotalityProperties
import Solcore.Syntax.Parser.Signature

/-! Valid-input totality for canonical generic parameter lists. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Nonempty delimiter syntax discharges the defensive refinement invariant. -/
theorem genericParameters_ordinary
    (input : State) (inputValid : input.ValidFor) :
    (∃ values next, genericParameters input = .ok values next) ∨
      (∃ failure next,
        genericParameters input = .reject failure next) := by
  rcases delimited_ordinary .less .greater false (identifier .parameter)
      .parameter .topLevel (identifier_elementTotalityContract .parameter)
      input inputValid with
    ⟨values, afterValues, valuesResult⟩ |
    ⟨failure, rejected, valuesResult⟩
  · rcases values with ⟨span, elements⟩
    have nonempty := delimited_false_elements_ne_nil_onSuccess .less .greater
      (identifier .parameter) .parameter .topLevel valuesResult
    cases elements with
    | nil => exact False.elim (nonempty rfl)
    | cons head tail =>
        exact Or.inl ⟨{
          span
          elements := { head, tail }
        }, afterValues, by
          simp only [genericParameters, bind, valuesResult]
          rfl⟩
  · exact Or.inr ⟨failure, rejected, by
      simp only [genericParameters, bind, valuesResult]⟩

theorem genericParameters_invariantFreeOnValid :
    Parser.InvariantFreeOnValid genericParameters :=
  genericParameters_ordinary

theorem genericParameters_ne_invariant
    (input : State) (inputValid : input.ValidFor)
    (error : ParserInvariantError) :
    genericParameters input ≠ .invariant error :=
  genericParameters_invariantFreeOnValid.ne_invariant input inputValid error

/-- Optional generic parameters are total in both selected and absent paths. -/
theorem optionalGenericParameters_ordinary
    (input : State) (inputValid : input.ValidFor) :
    (∃ values next, optionalGenericParameters input = .ok values next) ∨
      (∃ failure next,
        optionalGenericParameters input = .reject failure next) := by
  by_cases present : isSymbol input .less
  · rcases genericParameters_ordinary input inputValid with
      ⟨values, next, valuesResult⟩ |
      ⟨failure, rejected, valuesResult⟩
    · exact Or.inl ⟨some values, next, by
        simp only [optionalGenericParameters, getState, bind, present,
          ↓reduceIte, valuesResult, pure]⟩
    · exact Or.inr ⟨failure, rejected, by
        simp only [optionalGenericParameters, getState, bind, present,
          ↓reduceIte, valuesResult]⟩
  · have absent : isSymbol input .less = false := by
      cases found : isSymbol input .less with
      | false => rfl
      | true => exact False.elim (present found)
    exact Or.inl ⟨none, input, by
      simp only [optionalGenericParameters, getState, bind, absent,
        Bool.false_eq_true, ↓reduceIte, pure]⟩

theorem optionalGenericParameters_invariantFreeOnValid :
    Parser.InvariantFreeOnValid optionalGenericParameters :=
  optionalGenericParameters_ordinary

theorem optionalGenericParameters_ne_invariant
    (input : State) (inputValid : input.ValidFor)
    (error : ParserInvariantError) :
    optionalGenericParameters input ≠ .invariant error :=
  optionalGenericParameters_invariantFreeOnValid.ne_invariant
    input inputValid error

end Solcore.Syntax.Parser
