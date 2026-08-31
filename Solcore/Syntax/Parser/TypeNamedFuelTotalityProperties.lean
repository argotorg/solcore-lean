import Solcore.Syntax.Parser.DelimitedFuelTotalityProperties
import Solcore.Syntax.Parser.TypeNamedTotalityProperties

/-! Fuel-aware totality for recursive named-type parsing. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/--
Optional named-type arguments are ordinary when their delimited elements have
one less unit of recursive fuel available at the opening delimiter.
-/
theorem parseNamedTypeArguments_ordinary_of_elementFuel
    (nested : Parser TypeExpr) (elementFuel : Nat)
    (contract : FuelElementTotalityContract nested elementFuel)
    (input : State) (inputValid : input.ValidFor)
    (adequate : input.remainingCount < elementFuel + 1) :
    (∃ arguments next,
      parseNamedTypeArguments nested input = .ok arguments next) ∨
    (∃ failure next,
      parseNamedTypeArguments nested input = .reject failure next) := by
  by_cases present : isSymbol input .less
  · rcases delimited_ordinary_of_elementFuel .less .greater false nested
        .typeExpr .typeExpr elementFuel contract input inputValid adequate with
      ⟨parsed, afterDelimited, parsedResult⟩ |
      ⟨failure, rejected, parsedResult⟩
    · rcases requireNonempty_ok_of_delimited_false_ok .less .greater nested
          .typeExpr .typeExpr parsedResult with
        ⟨nonempty, nonemptyResult⟩
      exact Or.inl ⟨some nonempty, afterDelimited, by
        simp only [parseNamedTypeArguments, getState, bind, present,
          ↓reduceIte, parsedResult, nonemptyResult, pure]⟩
    · exact Or.inr ⟨failure, rejected, by
        simp only [parseNamedTypeArguments, getState, bind, present,
          ↓reduceIte, parsedResult]⟩
  · have absent : isSymbol input .less = false := by
      cases found : isSymbol input .less with
      | false => rfl
      | true => exact False.elim (present found)
    exact Or.inl ⟨none, input, by
      simp only [parseNamedTypeArguments, getState, bind, absent,
        Bool.false_eq_true, ↓reduceIte, pure]⟩

theorem parseNamedTypeArguments_ne_invariant_of_elementFuel
    (nested : Parser TypeExpr) (elementFuel : Nat)
    (contract : FuelElementTotalityContract nested elementFuel)
    (input : State) (inputValid : input.ValidFor)
    (adequate : input.remainingCount < elementFuel + 1)
    (error : ParserInvariantError) :
    parseNamedTypeArguments nested input ≠ .invariant error := by
  intro failed
  rcases parseNamedTypeArguments_ordinary_of_elementFuel nested elementFuel
      contract input inputValid adequate with
    ⟨arguments, next, result⟩ | ⟨failure, next, result⟩ <;>
    rw [result] at failed <;> contradiction

/--
A named type is ordinary with one fuel unit beyond its nested elements. Its
qualified name strictly consumes the unit before optional generic arguments.
-/
theorem parseNamedType_ordinary_of_elementFuel
    (nested : Parser TypeExpr) (elementFuel : Nat)
    (contract : FuelElementTotalityContract nested elementFuel)
    (input : State) (inputValid : input.ValidFor)
    (adequate : input.remainingCount < elementFuel + 1) :
    (∃ value next, parseNamedType nested input = .ok value next) ∨
    (∃ failure next, parseNamedType nested input = .reject failure next) := by
  rcases (qualifiedName_ordinary .typeExpr .typeExpr) input with
    ⟨name, afterName, nameResult⟩ | ⟨failure, rejected, nameResult⟩
  · have nameValid := qualifiedName_validFor .typeExpr .typeExpr
      input inputValid
    rw [nameResult] at nameValid
    have nameWindow := qualifiedName_preservesTokenWindow .typeExpr .typeExpr
      input
    rw [nameResult] at nameWindow
    have afterNameAdequate : afterName.remainingCount < elementFuel :=
      remainingCount_lt_after_strict_progress nameValid.2.1 nameWindow.2
        (qualifiedName_cursor_lt_onSuccess .typeExpr .typeExpr nameResult)
        adequate
    rcases parseNamedTypeArguments_ordinary_of_elementFuel nested elementFuel
        contract afterName nameValid.2.1 (by omega) with
      ⟨arguments, afterArguments, argumentsResult⟩ |
      ⟨failure, rejected, argumentsResult⟩
    · rcases finishNamedType_ordinary name arguments afterArguments with
        ⟨value, final, finished⟩ | ⟨failure, rejected, finished⟩
      · exact Or.inl ⟨value, final, by
          simp only [parseNamedType, bind, nameResult, argumentsResult,
            finished]⟩
      · exact Or.inr ⟨failure, rejected, by
          simp only [parseNamedType, bind, nameResult, argumentsResult,
            finished]⟩
    · exact Or.inr ⟨failure, rejected, by
        simp only [parseNamedType, bind, nameResult, argumentsResult]⟩
  · exact Or.inr ⟨failure, rejected, by
      simp only [parseNamedType, bind, nameResult]⟩

theorem parseNamedType_ne_invariant_of_elementFuel
    (nested : Parser TypeExpr) (elementFuel : Nat)
    (contract : FuelElementTotalityContract nested elementFuel)
    (input : State) (inputValid : input.ValidFor)
    (adequate : input.remainingCount < elementFuel + 1)
    (error : ParserInvariantError) :
    parseNamedType nested input ≠ .invariant error := by
  intro failed
  rcases parseNamedType_ordinary_of_elementFuel nested elementFuel contract
      input inputValid adequate with
    ⟨value, next, result⟩ | ⟨failure, next, result⟩ <;>
    rw [result] at failed <;> contradiction

end Solcore.Syntax.Parser
