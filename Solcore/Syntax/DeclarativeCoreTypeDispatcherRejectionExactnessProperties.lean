import Solcore.Syntax.DeclarativeCoreTypeBranchRejectionExactnessProperties

/-! Exact rejection endpoints for one prioritized Core type fuel layer. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

private theorem functionSelected_conflicts_absent
    {nestedRejects : Remainder → Remainder → Prop}
    {input rejected : Remainder}
    (selected : FunctionTypeRejects nestedRejects input rejected)
    (absent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
      (.keyword .functionKw)) : False := by
  rcases selected.keyword_token with ⟨_, token⟩
  exact typeTokenAbsent_conflicts_token absent token

private theorem comptimeSelected_conflicts_absent
    {nestedRejects : Remainder → Remainder → Prop}
    {input rejected : Remainder}
    (selected : ComptimeTypeRejects nestedRejects input rejected)
    (absent : ContextualSymbolPairAbsentAt input .comptime .less) : False := by
  rcases selected.prefix_tokens with ⟨markerSpan, openingSpan, marker,
    opening⟩
  exact absent ⟨markerSpan, openingSpan, marker, opening⟩

private theorem mappingSelected_conflicts_absent
    {nestedRejects : Remainder → Remainder → Prop}
    {input rejected : Remainder}
    (selected : MappingTypeRejects nestedRejects input rejected)
    (absent : ContextualSymbolPairAbsentAt input .mapping .leftParen) :
    False := by
  rcases selected.prefix_tokens with ⟨markerSpan, openingSpan, marker,
    opening⟩
  exact absent ⟨markerSpan, openingSpan, marker, opening⟩

private theorem proxySelected_conflicts_absent
    {nestedRejects : Remainder → Remainder → Prop}
    {input rejected : Remainder}
    (selected : ProxyTypeRejects nestedRejects input rejected)
    (absent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
      (.symbol .at)) : False := by
  cases selected with
  | innerRejected _ marker _ =>
      exact typeTokenAbsent_conflicts_token absent marker.1

private theorem tupleSelected_conflicts_absent
    {nestedRejects : Remainder → Remainder → Prop}
    {input rejected : Remainder}
    (selected : TupleTypeRejects nestedRejects input rejected)
    (absent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
      (.symbol .leftParen)) : False := by
  cases selected with
  | selected _ opening _ =>
      exact typeTokenAbsent_conflicts_token absent opening.1

/-- One prioritized Core type dispatcher layer has one first rejecting
endpoint whenever its recursive child outcomes are exact. -/
theorem TypeExprCoreRejects.output_unique
    {nestedRejects : Remainder → Remainder → Prop}
    (outcomes : ExactDeterministicOutcomeSpec TypeExprParses nestedRejects)
    {input left right : Remainder}
    (leftRejects : TypeExprCoreRejects nestedRejects input left)
    (rightRejects : TypeExprCoreRejects nestedRejects input right) :
    left = right := by
  cases leftRejects <;> cases rightRejects
  all_goals first
    | exact FunctionTypeRejects.output_unique outcomes
        (by assumption) (by assumption)
    | exact ComptimeTypeRejects.output_unique outcomes
        (by assumption) (by assumption)
    | exact MappingTypeRejects.output_unique outcomes
        (by assumption) (by assumption)
    | exact ProxyTypeRejects.output_unique outcomes
        (by assumption) (by assumption)
    | exact TupleTypeRejects.output_unique outcomes
        (by assumption) (by assumption)
    | exact NamedTypeRejects.output_unique outcomes
        (by assumption) (by assumption)
    | exact False.elim
        (functionSelected_conflicts_absent (by assumption) (by assumption))
    | exact False.elim
        (comptimeSelected_conflicts_absent (by assumption) (by assumption))
    | exact False.elim
        (mappingSelected_conflicts_absent (by assumption) (by assumption))
    | exact False.elim
        (proxySelected_conflicts_absent (by assumption) (by assumption))
    | exact False.elim
        (tupleSelected_conflicts_absent (by assumption) (by assumption))
    | exact False.elim
        ((by assumption : IdentifierAbsentAt input) (by assumption))
    | rfl

end Solcore.Syntax.DeclarativeGrammar
