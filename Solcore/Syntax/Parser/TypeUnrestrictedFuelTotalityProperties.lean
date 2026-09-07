import Solcore.Syntax.Parser.TypeFunctionUnrestrictedFuelTotalityProperties
import Solcore.Syntax.Parser.TypeNamedUnrestrictedFuelTotalityProperties
import Solcore.Syntax.Parser.TypeSimpleUnrestrictedFuelTotalityProperties
import Solcore.Syntax.Parser.TypeSuccessContextProperties
import Solcore.Syntax.Parser.TypeStrictProperties

/-! The production resource bound suffices on every state, independently of
token provenance, active-window validity, or accumulated diagnostic spans.
Only actual token consumption and successful child progress are used. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

theorem typeExprWithFuel_ordinary_of_remainingCount_lt_unrestricted :
    ∀ fuel input, input.remainingCount < fuel →
      (∃ value next, typeExprWithFuel fuel input = .ok value next) ∨
      (∃ failure next, typeExprWithFuel fuel input = .reject failure next) := by
  intro fuel
  induction fuel with
  | zero => intro input adequate; omega
  | succ fuel ih =>
      intro input adequate
      let children : UnrestrictedFuelElementContract (typeExprWithFuel fuel) fuel := {
        endIndexOnSuccess := fun result =>
          congrArg TokenWindow.endIndex (typeExprWithFuel_success_context fuel result).2
        cursorLtOnSuccess := typeExprWithFuel_cursor_lt_onSuccess fuel
        ordinary := ih
      }
      simp only [typeExprWithFuel]
      split
      · exact parseFunctionType_ordinary_of_unrestrictedElementFuel
          (typeExprWithFuel fuel) fuel children input (by omega)
      · split
        · exact parseComptimeType_ordinary_of_unrestrictedElementFuel
            (typeExprWithFuel fuel) fuel children input (by omega)
        · split
          · exact parseMappingType_ordinary_of_unrestrictedElementFuel
              (typeExprWithFuel fuel) fuel children input (by omega)
          · split
            · exact parseProxyType_ordinary_of_unrestrictedElementFuel
                (typeExprWithFuel fuel) fuel children input (by omega)
            · split
              · exact parseTupleType_ordinary_of_unrestrictedElementFuel
                  (typeExprWithFuel fuel) fuel children input (by omega)
              · split
                · exact parseNamedType_ordinary_of_unrestrictedElementFuel
                    (typeExprWithFuel fuel) fuel children input (by omega)
                · exact Or.inr ⟨_, input, rfl⟩

theorem typeExprWithFuel_ne_invariant_of_remainingCount_lt_unrestricted
    (fuel : Nat) (input : State) (adequate : input.remainingCount < fuel)
    (error : ParserInvariantError) : typeExprWithFuel fuel input ≠ .invariant error := by
  intro failed
  rcases typeExprWithFuel_ordinary_of_remainingCount_lt_unrestricted fuel input adequate with
    ⟨value, next, result⟩ | ⟨failure, next, result⟩ <;> rw [result] at failed <;> contradiction

theorem typeExpr_ordinary : Parser.Ordinary typeExpr := by
  intro input
  exact typeExprWithFuel_ordinary_of_remainingCount_lt_unrestricted
    (input.remainingCount + 1) input (by omega)

theorem typeExpr_ne_invariant_unrestricted (input : State) (error : ParserInvariantError) :
    typeExpr input ≠ .invariant error := by
  exact typeExprWithFuel_ne_invariant_of_remainingCount_lt_unrestricted
    (input.remainingCount + 1) input (by omega) error

theorem typeExprWithFuel_unrestrictedFuelElementContract (fuel : Nat) :
    UnrestrictedFuelElementContract (typeExprWithFuel fuel) fuel where
  endIndexOnSuccess result :=
    congrArg TokenWindow.endIndex (typeExprWithFuel_success_context fuel result).2
  cursorLtOnSuccess := typeExprWithFuel_cursor_lt_onSuccess fuel
  ordinary := typeExprWithFuel_ordinary_of_remainingCount_lt_unrestricted fuel

theorem typeExpr_unrestrictedFuelElementContract (fuel : Nat) :
    UnrestrictedFuelElementContract typeExpr fuel where
  endIndexOnSuccess result :=
    congrArg TokenWindow.endIndex (typeExpr_success_context result).2
  cursorLtOnSuccess := typeExpr_cursor_lt_onSuccess
  ordinary input _ := typeExpr_ordinary input

end Solcore.Syntax.Parser
