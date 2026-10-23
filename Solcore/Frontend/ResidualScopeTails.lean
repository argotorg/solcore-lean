import Solcore.Frontend.SourceSpecialization

/-! Quantifiers introduced after a particular initializer have an owner on
that exact validator path. This separates the scope captured at allocation
from nested generalized declarations without changing source inference. -/
set_option autoImplicit false
namespace Solcore.Frontend.SourceSpecialization
open SourceInference TypeSystem

theorem ResidualScopeTail.to_path {source : TypedSource}
    {first node : NodeId} {firstVariables variables : List TypeVarId}
    (tail : ResidualScopeTail source first firstVariables node variables)
    (start : ResidualScopePath source first firstVariables) :
    ResidualScopePath source node variables := by
  induction tail with
  | refl => exact start
  | child _ edge ih => exact .child ih edge

theorem ResidualScopeTail.trans {source : TypedSource}
    {first middle last : NodeId} {firstVariables middleVariables lastVariables : List TypeVarId}
    (left : ResidualScopeTail source first firstVariables middle middleVariables)
    (right : ResidualScopeTail source middle middleVariables last lastVariables) :
    ResidualScopeTail source first firstVariables last lastVariables := by
  induction right with
  | refl => exact left
  | child _ edge ih => exact .child ih edge

/-- A variable outside the captured entry scope was added by an actual let
initializer strictly along this suffix. The owner and both path pieces use
one source and the same child-scheduling receipt. -/
theorem ResidualScopeTail.new_quantifier_owner {source : TypedSource}
    {first node : NodeId} {firstVariables variables : List TypeVarId}
    (tail : ResidualScopeTail source first firstVariables node variables)
    {metavariable : TypeVarId} (occurs : metavariable ∈ variables)
    (fresh : metavariable ∉ firstVariables) :
    ∃ parent parentVariables statement binder initializer initializerVariables,
      ResidualScopeTail source first firstVariables parent parentVariables ∧
      source.lookupNode? parent.occurrenceId = some (.statement statement) ∧
      statement.form = .letDecl binder (some initializer) ∧
      (.expression initializer, initializerVariables) ∈
        residualScopeChildren source parent parentVariables ∧
      ResidualScopeTail source (.expression initializer) initializerVariables node variables ∧
      metavariable ∈ binder.scheme.quantified := by
  induction tail with
  | refl => exact False.elim (fresh occurs)
  | @child parent parentVariables node variables prior edge ih =>
    by_cases old : metavariable ∈ parentVariables
    · obtain ⟨owner, ownerVariables, statement, binder, initializer, initializerVariables,
        before, found, form, entered, after, quantified⟩ := ih old
      exact ⟨owner, ownerVariables, statement, binder, initializer, initializerVariables,
        before, found, form, entered, .child after edge, quantified⟩
    · obtain ⟨statement, binder, initializer, found, form, same, quantified⟩ :=
        residualScopeChildren_new_quantifier edge occurs old
      subst node
      exact ⟨parent, parentVariables, statement, binder, initializer, variables,
        prior, found, form, edge, .refl, quantified⟩

end Solcore.Frontend.SourceSpecialization
