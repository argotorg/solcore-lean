import Solcore.Syntax.DeclarativeTypeDispatchSelectionGrammar

/-! The explicit prioritized selectors determine at most one branch. This is
selection uniqueness, not existence of a successful or rejected type outcome. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

theorem TypeDispatchPairPresent.exact_prefix {input : Remainder}
    {keyword : ContextualKeyword} {symbol : Symbol}
    (present : TypeDispatchPairPresent input keyword symbol) :
    ∃ markerSpan openingSpan afterMarker afterOpening,
      ExactTokenParses (.identifier keyword.spelling) input markerSpan afterMarker ∧
      ExactTokenParses (.symbol symbol) afterMarker openingSpan afterOpening := by
  rcases present with ⟨markerSpan, openingSpan, marker, opening⟩
  exact ⟨markerSpan, openingSpan, _, _, ⟨marker, rfl⟩, ⟨opening, rfl⟩⟩

theorem TypeDispatchSelects.branch_unique {input : Remainder} {left right : TypeDispatchBranch}
    (leftSelected : TypeDispatchSelects input left) (rightSelected : TypeDispatchSelects input right) :
    left = right := by
  cases leftSelected <;> cases rightSelected <;>
    grind only [TokenKindAbsentAt, ContextualSymbolPairAbsentAt, TypeDispatchPairPresent, IdentifierAbsentAt]

end Solcore.Syntax.DeclarativeGrammar
