import Solcore.Frontend.SourceInference.LocalGeneralizationBoundaries
import Solcore.Frontend.SourceInference.LocalGeneralizationRetiredInterval

/-! Authentic initialized declarations establish their continuation boundary.
Operational local requirements are recovered at the initializer return state,
so the final node table is never treated as an earlier inference ledger. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.Frontend.SourceInference.LocalGeneralizationBoundaries
open TypeSystem Detail
open LocalGeneralizationEvents (Ready)
open LocalReadScopeProgress (ReadAt)

namespace OriginSince

theorem statement {fuel context source initial result}
    (receipt : LocalLetRequirementTiming.Receipt fuel context source initial result)
    (ready : Ready initial) (below : initial.LocalBindersBelowNextLocal) :
    OriginSince initial.nextLocal result.state receipt.binding.1 receipt.value.id :=
  ⟨_, _, _, Nat.le_refl _, .statement receipt ready below, receipt.retired_interval below⟩

theorem header {fuel context source initial result}
    (receipt : LocalHeaderRequirementTiming.Receipt fuel context source initial result)
    (ready : Ready initial) (below : initial.LocalBindersBelowNextLocal) :
    OriginSince initial.nextLocal result.2 receipt.binding.1 receipt.value.id :=
  ⟨_, _, _, Nat.le_refl _, .header receipt ready below, receipt.retired_interval below⟩

end OriginSince

theorem ItemSince.of_header {fuel context source initial result}
    (receipt : LocalHeaderRequirementTiming.Receipt fuel context source initial result)
    (ready : Ready initial) (below : initial.LocalBindersBelowNextLocal) :
    ItemSince initial.nextLocal result.2 result.1 := by
  intro binder initializer same
  rw [receipt.recorded] at same
  cases same
  exact OriginSince.header receipt ready below

theorem StatementSince.of_let {fuel context source initial result}
    (receipt : LocalLetRequirementTiming.Receipt fuel context source initial result)
    (ready : Ready initial) (below : initial.LocalBindersBelowNextLocal) {node : StatementNode}
    (form : node.form = .letDecl receipt.binding.1 (some receipt.value.id)) :
    StatementSince initial.nextLocal result.state node := by
  unfold StatementSince
  rw [form]
  exact OriginSince.statement receipt ready below

/-- The exact lookup requirements at the generalization boundary exclude their
variables from the recorded binder's quantified variables. -/
theorem Boundary.local_generalization {binder : TypedBinder} {initializer : ExpressionId}
    {low high : Nat} {nodes : List Node} (boundary : Boundary binder initializer low high nodes)
    {node : ExpressionNode} (member : .expression node ∈ nodes) {name : String} {localId : Resolved.LocalId}
    (form : node.form = .reference name (.local localId)) :
    ∃ ready : State, ∃ lookup : LocalReadEvents.Lookup,
      ready.nodes = nodes ∧ node.id = lookup.id ∧
      node.form = .reference lookup.name.value (.local lookup.binder.id) ∧
      node.localSchemeInstantiationStart = some lookup.allocated.inference.next ∧
      lookup.batch.1 <+: node.requirements ∧
      RequirementPredicatesCorrespond ready.requirements lookup.predicates lookup.batch.1 ∧
      (∀ requirement ∈ ready.requirements, requirement.id ∈ lookup.batch.1 →
        ∀ metavariable ∈ TypedTraitResolution.predicateVariables (applyPredicate ready requirement.predicate),
          metavariable ∉ binder.scheme.quantified) := by
  cases boundary with
  | statement receipt ready below =>
      obtain ⟨lookup, id, actualForm, start, batchPrefix, predicates, blocked⟩ :=
        receipt.local_generalization ready.wellFormed ready.allocated ready.origins member form
      exact ⟨receipt.ready, lookup, rfl, id, actualForm, start, batchPrefix, predicates, blocked⟩
  | header receipt ready below =>
      obtain ⟨lookup, id, actualForm, start, batchPrefix, predicates, blocked⟩ :=
        receipt.local_generalization ready.wellFormed ready.allocated ready.origins member form
      exact ⟨receipt.ready, lookup, rfl, id, actualForm, start, batchPrefix, predicates, blocked⟩

/-- A continuation read of an initializer-local ID is pulled back to the exact
initializer occurrence before applying the real generalization result. -/
theorem Boundary.retired_read_generalization {binder : TypedBinder} {initializer : ExpressionId}
    {low high : Nat} {nodes : List Node} {state : State}
    (boundary : Boundary binder initializer low high nodes)
    (barrier : LocalReadScopeProgress.Barrier low high nodes state)
    {node : ExpressionNode} (member : .expression node ∈ state.nodes) {name : String} {localId : Resolved.LocalId}
    (form : node.form = .reference name (.local localId))
    (created : low ≤ localId.binderIndex) (retired : localId.binderIndex < high) :
    ∃ ready : State, ∃ original : ExpressionNode, ∃ lookup : LocalReadEvents.Lookup,
      ready.nodes = nodes ∧ .expression original ∈ ready.nodes ∧ original.id = node.id ∧
      original.id = lookup.id ∧ lookup.binder.id = localId ∧ original.form = .reference lookup.name.value (.local lookup.binder.id) ∧
      original.localSchemeInstantiationStart = some lookup.allocated.inference.next ∧
      lookup.batch.1 <+: original.requirements ∧
      RequirementPredicatesCorrespond ready.requirements lookup.predicates lookup.batch.1 ∧
      (∀ requirement ∈ ready.requirements, requirement.id ∈ lookup.batch.1 →
        ∀ metavariable ∈ TypedTraitResolution.predicateVariables (applyPredicate ready requirement.predicate),
          metavariable ∉ binder.scheme.quantified) := by
  obtain ⟨original, present, same, actualName, actualForm⟩ := barrier.read created retired member form
  obtain ⟨ready, lookup, actualNodes, id, reference, start, batchPrefix, predicates, blocked⟩ :=
    boundary.local_generalization present actualForm
  have sameLocal : lookup.binder.id = localId :=
    ReferenceResolution.local.inj (ExpressionForm.reference.inj (reference.symm.trans actualForm)).2
  exact ⟨ready, original, lookup, actualNodes, actualNodes.symm ▸ present, same,
    id, sameLocal, reference, start, batchPrefix, predicates, blocked⟩

end Solcore.Frontend.SourceInference.LocalGeneralizationBoundaries
