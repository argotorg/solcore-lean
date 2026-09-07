import Solcore.Syntax.Parser.DelimitedUnrestrictedFuelTotalityProperties
import Solcore.Syntax.Parser.TypeNamedTotalityProperties

/-! Adequate-fuel named types have ordinary outcomes on arbitrary states.
Optional absence is a silent success, nonempty arguments are structural, and
the qualified-name cursor bound is transported without input validity. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

theorem parseNamedTypeArguments_ordinary_of_unrestrictedElementFuel
    (nested : Parser TypeExpr) (elementFuel : Nat)
    (contract : UnrestrictedFuelElementContract nested elementFuel)
    (input : State) (adequate : input.remainingCount < elementFuel + 1) :
    (∃ arguments next, parseNamedTypeArguments nested input = .ok arguments next) ∨
      (∃ failure next, parseNamedTypeArguments nested input = .reject failure next) := by
  by_cases present : isSymbol input .less
  · rcases delimited_ordinary_of_unrestrictedElementFuel .less .greater false nested
        .typeExpr .typeExpr elementFuel contract input adequate with
      ⟨parsed, afterDelimited, parsedResult⟩ | ⟨failure, rejected, parsedResult⟩
    · rcases requireNonempty_ok_of_delimited_false_ok .less .greater nested
          .typeExpr .typeExpr parsedResult with ⟨nonempty, nonemptyResult⟩
      exact Or.inl ⟨some nonempty, afterDelimited, by
        simp only [parseNamedTypeArguments, getState, bind, present,
          ↓reduceIte, parsedResult, nonemptyResult, pure]⟩
    · exact Or.inr ⟨failure, rejected, by
        simp only [parseNamedTypeArguments, getState, bind, present, ↓reduceIte, parsedResult]⟩
  · have absent : isSymbol input .less = false := Bool.eq_false_iff.mpr present
    exact Or.inl ⟨none, input, by
      simp only [parseNamedTypeArguments, getState, bind, absent,
        Bool.false_eq_true, ↓reduceIte, pure]⟩

theorem parseNamedTypeArguments_ne_invariant_of_unrestrictedElementFuel
    (nested : Parser TypeExpr) (elementFuel : Nat)
    (contract : UnrestrictedFuelElementContract nested elementFuel)
    (input : State) (adequate : input.remainingCount < elementFuel + 1)
    (error : ParserInvariantError) : parseNamedTypeArguments nested input ≠ .invariant error := by
  intro failed
  rcases parseNamedTypeArguments_ordinary_of_unrestrictedElementFuel nested elementFuel contract input adequate with
    ⟨arguments, next, result⟩ | ⟨failure, next, result⟩ <;>
    rw [result] at failed <;> contradiction

theorem parseNamedType_ordinary_of_unrestrictedElementFuel
    (nested : Parser TypeExpr) (elementFuel : Nat)
    (contract : UnrestrictedFuelElementContract nested elementFuel)
    (input : State) (adequate : input.remainingCount < elementFuel + 1) :
    (∃ value next, parseNamedType nested input = .ok value next) ∨
      (∃ failure next, parseNamedType nested input = .reject failure next) := by
  rcases (qualifiedName_ordinary .typeExpr .typeExpr) input with
    ⟨name, afterName, nameResult⟩ | ⟨failure, rejected, nameResult⟩
  · have nameWindow := qualifiedName_preservesTokenWindow .typeExpr .typeExpr input
    rw [nameResult] at nameWindow
    have afterNameAdequate : afterName.remainingCount < elementFuel + 1 :=
      remainingCount_lt_of_endIndex_eq (congrArg TokenWindow.endIndex nameWindow.2)
        (Nat.le_of_lt (qualifiedName_cursor_lt_onSuccess .typeExpr .typeExpr nameResult)) adequate
    rcases parseNamedTypeArguments_ordinary_of_unrestrictedElementFuel nested elementFuel
        contract afterName afterNameAdequate with
      ⟨arguments, afterArguments, argumentsResult⟩ | ⟨failure, rejected, argumentsResult⟩
    · rcases finishNamedType_ordinary name arguments afterArguments with
        ⟨value, final, finished⟩ | ⟨failure, rejected, finished⟩
      · exact Or.inl ⟨value, final, by
          simp only [parseNamedType, bind, nameResult, argumentsResult, finished]⟩
      · exact Or.inr ⟨failure, rejected, by
          simp only [parseNamedType, bind, nameResult, argumentsResult, finished]⟩
    · exact Or.inr ⟨failure, rejected, by
        simp only [parseNamedType, bind, nameResult, argumentsResult]⟩
  · exact Or.inr ⟨failure, rejected, by simp only [parseNamedType, bind, nameResult]⟩

theorem parseNamedType_ne_invariant_of_unrestrictedElementFuel
    (nested : Parser TypeExpr) (elementFuel : Nat)
    (contract : UnrestrictedFuelElementContract nested elementFuel)
    (input : State) (adequate : input.remainingCount < elementFuel + 1)
    (error : ParserInvariantError) : parseNamedType nested input ≠ .invariant error := by
  intro failed
  rcases parseNamedType_ordinary_of_unrestrictedElementFuel nested elementFuel contract input adequate with
    ⟨value, next, result⟩ | ⟨failure, next, result⟩ <;>
    rw [result] at failed <;> contradiction

end Solcore.Syntax.Parser
