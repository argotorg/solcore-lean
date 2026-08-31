import Solcore.Syntax.Parser.PatternArgumentsFuelTotalityProperties
import Solcore.Syntax.Parser.QualifiedNameTotalityProperties

/-! Fuel-aware totality for qualified binder and constructor patterns. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.PatternInternals

/-- A qualified name's nonempty carrier remains nonempty after reversal. -/
theorem qualifiedName_components_reverse_ne_nil (path : QualifiedName) :
    path.value.components.toList.reverse ≠ [] := by
  rcases path.value.components with ⟨head, tail⟩
  simp [NonemptyList.toList]

theorem qualifiedPattern_ordinary_of_elementFuel
    (nested : Parser Pattern) (nestedFuel : Nat)
    (contract : FuelElementTotalityContract nested nestedFuel)
    (input : State) (inputValid : input.ValidFor)
    (adequate : input.remainingCount < nestedFuel + 1) :
    (∃ pattern next, qualifiedPattern nested input = .ok pattern next) ∨
    (∃ failure next,
      qualifiedPattern nested input = .reject failure next) := by
  rcases (qualifiedName_ordinary .pattern .pattern) input with
    ⟨path, afterPath, pathResult⟩ |
    ⟨failure, rejected, pathResult⟩
  · have pathValid := qualifiedName_validFor .pattern .pattern input inputValid
    rw [pathResult] at pathValid
    have pathWindow := qualifiedName_preservesTokenWindow .pattern .pattern input
    rw [pathResult] at pathWindow
    have afterPathAdequate : afterPath.remainingCount < nestedFuel + 1 :=
      remainingCount_lt_of_cursor_le pathWindow.2
        (qualifiedName_cursorMonotoneOnSuccess .pattern .pattern input path
          afterPath pathResult) adequate
    rcases optionalConstructorArguments_ordinary_of_elementFuel nested
        nestedFuel contract afterPath pathValid.2.1 afterPathAdequate with
      ⟨arguments, final, argumentsResult⟩ |
      ⟨failure, rejected, argumentsResult⟩
    · let components := path.value.components.toList
      cases reversed : components.reverse with
      | nil =>
          exact False.elim
            (qualifiedName_components_reverse_ne_nil path (by
              simpa only [components] using reversed))
      | cons name qualifiersRev =>
          simp only [qualifiedPattern, bind, pathResult, argumentsResult,
            components, reversed]
          split <;> exact Or.inl ⟨_, final, rfl⟩
    · exact Or.inr ⟨failure, rejected, by
        simp only [qualifiedPattern, bind, pathResult, argumentsResult]⟩
  · exact Or.inr ⟨failure, rejected, by
      simp only [qualifiedPattern, bind, pathResult]⟩

theorem qualifiedPattern_ne_invariant_of_elementFuel
    (nested : Parser Pattern) (nestedFuel : Nat)
    (contract : FuelElementTotalityContract nested nestedFuel)
    (input : State) (inputValid : input.ValidFor)
    (adequate : input.remainingCount < nestedFuel + 1)
    (error : ParserInvariantError) :
    qualifiedPattern nested input ≠ .invariant error := by
  intro failed
  rcases qualifiedPattern_ordinary_of_elementFuel nested nestedFuel contract
      input inputValid adequate with
    ⟨pattern, next, result⟩ | ⟨failure, next, result⟩ <;>
      rw [result] at failed <;> contradiction

end Solcore.Syntax.Parser.PatternInternals
