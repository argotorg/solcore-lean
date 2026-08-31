import Solcore.Syntax.Parser.TypeFunctionFuelTotalityProperties
import Solcore.Syntax.Parser.TypeNamedFuelTotalityProperties
import Solcore.Syntax.Parser.TypeSimpleFuelTotalityProperties

/-! Adequate-fuel and public totality for the recursive type parser. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- More fuel than remaining tokens rules out recursive type fuel exhaustion. -/
theorem typeExprWithFuel_ordinary_of_remainingCount_lt :
    ∀ fuel input, input.ValidFor → input.remainingCount < fuel →
      (∃ value next, typeExprWithFuel fuel input = .ok value next) ∨
      (∃ failure next,
        typeExprWithFuel fuel input = .reject failure next) := by
  intro fuel
  induction fuel with
  | zero =>
      intro input inputValid adequate
      omega
  | succ fuel inductionHypothesis =>
      intro input inputValid adequate
      let nestedContract :
          FuelElementTotalityContract (typeExprWithFuel fuel) fuel := {
        validFor := (typeExprWithFuel_validFor fuel).mono
          (fun _file _value _valueValid => trivial)
        preservesTokenWindow := typeExprWithFuel_preservesTokenWindow fuel
        cursorLtOnSuccess := typeExprWithFuel_cursor_lt_onSuccess fuel
        ordinary := inductionHypothesis
      }
      simp only [typeExprWithFuel]
      split
      · exact parseFunctionType_ordinary_of_elementFuel
          (typeExprWithFuel fuel) fuel nestedContract input inputValid
          (by simpa [Nat.succ_eq_add_one] using adequate)
      · split
        · exact parseComptimeType_ordinary_of_elementFuel
            (typeExprWithFuel fuel) fuel nestedContract input inputValid
            (by simpa [Nat.succ_eq_add_one] using adequate)
        · split
          · exact parseMappingType_ordinary_of_elementFuel
              (typeExprWithFuel fuel) fuel nestedContract input inputValid
              (by simpa [Nat.succ_eq_add_one] using adequate)
          · split
            · exact parseProxyType_ordinary_of_elementFuel
                (typeExprWithFuel fuel) fuel nestedContract input inputValid
                (by simpa [Nat.succ_eq_add_one] using adequate)
            · split
              · exact parseTupleType_ordinary_of_elementFuel
                  (typeExprWithFuel fuel) fuel nestedContract input inputValid
                  (by simpa [Nat.succ_eq_add_one] using adequate)
              · split
                · exact parseNamedType_ordinary_of_elementFuel
                    (typeExprWithFuel fuel) fuel nestedContract input inputValid
                    (by simpa [Nat.succ_eq_add_one] using adequate)
                · exact Or.inr ⟨_, input, rfl⟩

theorem typeExprWithFuel_ne_invariant_of_remainingCount_lt
    (fuel : Nat) (input : State) (inputValid : input.ValidFor)
    (adequate : input.remainingCount < fuel)
    (error : ParserInvariantError) :
    typeExprWithFuel fuel input ≠ .invariant error := by
  intro failed
  rcases typeExprWithFuel_ordinary_of_remainingCount_lt fuel input inputValid
      adequate with
    ⟨value, next, result⟩ | ⟨failure, next, result⟩ <;>
    rw [result] at failed <;> contradiction

/-- The production fuel choice makes public type parsing invariant-free. -/
theorem typeExpr_invariantFreeOnValid :
    Parser.InvariantFreeOnValid typeExpr := by
  intro input inputValid
  unfold typeExpr
  exact typeExprWithFuel_ordinary_of_remainingCount_lt
    (input.remainingCount + 1) input inputValid (by omega)

theorem typeExpr_ne_invariant (input : State) (inputValid : input.ValidFor)
    (error : ParserInvariantError) :
    typeExpr input ≠ .invariant error :=
  typeExpr_invariantFreeOnValid.ne_invariant input inputValid error

/-- Public type parsing satisfies the complete recursive element contract. -/
theorem typeExpr_elementTotalityContract :
    ElementTotalityContract typeExpr := {
  validFor := typeExpr_validFor.mono
    (fun _file _value _valueValid => trivial)
  preservesTokenWindow := typeExpr_preservesTokenWindow
  cursorLtOnSuccess := typeExpr_cursor_lt_onSuccess
  invariantFree := fun input inputValid error =>
    typeExpr_ne_invariant input inputValid error
}

end Solcore.Syntax.Parser
