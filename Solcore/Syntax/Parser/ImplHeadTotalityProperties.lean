import Solcore.Syntax.Parser.DelimitedNonemptyProperties
import Solcore.Syntax.Parser.ImplProperties
import Solcore.Syntax.Parser.InvariantFreeProperties
import Solcore.Syntax.Parser.PrimitiveTotalityProperties

/-! Totality helpers for canonical implementation declaration heads. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ImplInternals

/-- A syntactically nonempty implementation argument list refines safely. -/
theorem requireImplArguments_ok_of_delimited_false_ok
    {input afterDelimited : State} {values : DelimitedList TypeExpr}
    (parsed : delimited .less .greater false typeExpr .typeExpr .topLevel
      input = .ok values afterDelimited) :
    ∃ nonempty,
      requireImplArguments values afterDelimited =
        .ok nonempty afterDelimited := by
  have nonempty := delimited_false_elements_ne_nil_onSuccess .less .greater
    typeExpr .typeExpr .topLevel parsed
  unfold requireImplArguments
  cases elements : values.elements with
  | nil => exact False.elim (nonempty elements)
  | cons head tail => exact ⟨_, rfl⟩

/-- The optional leading `default` marker is ordinary on valid input. -/
theorem implDefaultMarker_invariantFreeOnValid :
    Parser.InvariantFreeOnValid implDefaultMarker := by
  unfold implDefaultMarker
  apply Parser.bind_invariantFreeOnValid getState_validFor
    Parser.getState_invariantFreeOnValid
  intro observed
  by_cases present : isKeyword observed .defaultKw
  · simp only [present, if_true]
    apply Parser.bind_invariantFreeOnValid
      (keyword_validFor .defaultKw .topItem)
      (keyword_ordinary .defaultKw .topItem).invariantFreeOnValid
    intro marker
    exact Parser.pure_invariantFreeOnValid (some marker.span)
  · simp only [present, Bool.false_eq_true, if_false]
    exact Parser.pure_invariantFreeOnValid none

theorem implDefaultMarker_ne_invariant
    (input : State) (inputValid : input.ValidFor)
    (error : ParserInvariantError) :
    implDefaultMarker input ≠ .invariant error :=
  implDefaultMarker_invariantFreeOnValid.ne_invariant
    input inputValid error

end Solcore.Syntax.Parser.ImplInternals
