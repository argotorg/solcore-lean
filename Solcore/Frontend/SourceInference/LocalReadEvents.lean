import Solcore.Frontend.SourceInference.DirectRequirementProgress

/-! Local references retain the actual inference lookup that issued their
requirements. Later argument coercions may append requirements to the node;
the original batch and its operational classification remain identifiable. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.Frontend.SourceInference
open TypeSystem
namespace LocalReadEvents

structure Lookup where
  fuel : Nat
  context : Context
  expression : Syntax.Expr
  expected : Option Ty
  initial : State
  allocated : State
  id : ExpressionId
  name : Syntax.Identifier
  binder : TypedBinder
  result : InferredExpression × State
  form : expression.value = .identifier name
  allocation : initial.allocateExpressionId = (id, allocated)
  found : allocated.lookupBinder? name.value = some binder
  accepted : Detail.inferExprFuel (fuel + 1) context expression expected initial = .ok result
  wellFormed : initial.RequirementsWellFormed
  directAllocated : initial.DirectRequirementsAllocated

def Lookup.advanced (lookup : Lookup) : State :=
  { lookup.allocated with inference := { lookup.allocated.inference with
      next := (lookup.binder.scheme.instantiateWithSubstitution lookup.allocated.inference.next).next } }

def Lookup.predicates (lookup : Lookup) : List ProgramPredicate :=
  lookup.binder.schemeRequirements.map fun requirement =>
    Detail.applyPredicate lookup.advanced
      (TypedTraitResolution.applySubstitution
        (lookup.binder.scheme.instantiateWithSubstitution lookup.allocated.inference.next).substitution
        requirement.predicate)

def Lookup.batch (lookup : Lookup) : List RequirementId × State :=
  lookup.advanced.addRequirementsWithIds lookup.predicates

/-- The witness is a real successful lookup. Its original fresh requirement
batch remains a prefix even if later argument fitting extends this node. -/
def OriginFields (rows : List Requirement) (next : Nat) (direct : List RequirementId)
    (node : ExpressionNode) : Prop :=
  ∃ lookup : Lookup,
    node.id = lookup.id ∧
    node.form = .reference lookup.name.value (.local lookup.binder.id) ∧
    node.localSchemeInstantiationStart = some lookup.allocated.inference.next ∧
    lookup.batch.1 <+: node.requirements ∧
    RequirementLedgerProgress lookup.result.2.requirements lookup.result.2.nextRequirement
      lookup.result.2.directCallRequirements rows next direct

def Origin (after : State) (node : ExpressionNode) : Prop :=
  OriginFields after.requirements after.nextRequirement after.directCallRequirements node

def AtFields (rows : List Requirement) (next : Nat) (direct : List RequirementId)
    (node : ExpressionNode) : Prop :=
  ∀ name binder, node.form = .reference name (.local binder) → OriginFields rows next direct node

def At (after : State) (node : ExpressionNode) : Prop :=
  AtFields after.requirements after.nextRequirement after.directCallRequirements node

def OriginsFields (nodes : List Node) (rows : List Requirement) (next : Nat) (direct : List RequirementId) : Prop :=
  ∀ node, Node.expression node ∈ nodes → AtFields rows next direct node

def Origins (state : State) : Prop :=
  OriginsFields state.nodes state.requirements state.nextRequirement state.directCallRequirements

theorem Lookup.recorded (lookup : Lookup) :
    Detail.recordExpressionWithExpected lookup.context lookup.expression lookup.id
      (lookup.advanced.resolve
        (lookup.binder.scheme.instantiateWithSubstitution lookup.allocated.inference.next).body)
      (.reference lookup.name.value (.local lookup.binder.id)) lookup.batch.1 lookup.expected
      lookup.batch.2 (some lookup.allocated.inference.next) = .ok lookup.result :=
  Detail.inferExprFuel_success_localIdentifier_record lookup.form lookup.allocation lookup.found lookup.accepted

theorem Lookup.node (lookup : Lookup) :
    ∃ node, Node.expression node ∈ lookup.result.2.nodes ∧ Origin lookup.result.2 node := by
  obtain ⟨fitted, fit, _, recorded⟩ := Detail.recordExpressionWithExpected_success_nodes lookup.recorded
  let node : ExpressionNode := {
    id := fitted.expression.id
    span := lookup.expression.span
    type := fitted.expression.type
    form := .reference lookup.name.value (.local lookup.binder.id)
    requirements := lookup.batch.1 ++ Detail.coercionRequirements fitted.coercions
    coercions := fitted.coercions
    localSchemeInstantiationStart := some lookup.allocated.inference.next }
  refine ⟨node, ?_, lookup, ?_, rfl, rfl, ?_, State.DirectRequirementsProgress.refl lookup.result.2⟩
  · rw [recorded]
    exact List.mem_append_right _ (List.mem_singleton_self _)
  · exact Detail.withExpected_success_expression_id fit
  · exact List.prefix_append _ _

theorem Origin.extend {before after : State} {node : ExpressionNode}
    (origin : Origin before node) (progress : State.DirectRequirementsProgress before after) :
    Origin after node := by
  obtain ⟨lookup, id, form, start, batchPrefix, previous⟩ := origin
  exact ⟨lookup, id, form, start, batchPrefix, State.DirectRequirementsProgress.trans previous progress⟩

theorem Origin.node_extension {state : State} {before after : ExpressionNode}
    (origin : Origin state before)
    (id : after.id = before.id) (form : after.form = before.form)
    (start : after.localSchemeInstantiationStart = before.localSchemeInstantiationStart)
    (requirements : before.requirements <+: after.requirements) : Origin state after := by
  obtain ⟨lookup, actualId, actualForm, actualStart, batchPrefix, progress⟩ := origin
  exact ⟨lookup, id.trans actualId, form.trans actualForm, start.trans actualStart,
    batchPrefix.trans requirements, progress⟩

theorem At.extend {before after : State} {node : ExpressionNode}
    (origin : At before node) (progress : State.DirectRequirementsProgress before after) : At after node :=
  fun name binder form => Origin.extend (origin name binder form) progress

theorem At.node_extension {state : State} {before after : ExpressionNode}
    (origin : At state before)
    (id : after.id = before.id) (form : after.form = before.form)
    (start : after.localSchemeInstantiationStart = before.localSchemeInstantiationStart)
    (requirements : before.requirements <+: after.requirements) : At state after := by
  intro name binder selected
  exact Origin.node_extension (origin name binder (form.symm.trans selected)) id form start requirements

theorem Origins.of_nodes_eq {before after : State}
    (origins : Origins before) (same : after.nodes = before.nodes)
    (progress : State.DirectRequirementsProgress before after) : Origins after := by
  intro node member
  exact At.extend (origins node (same ▸ member)) progress

private theorem correspondence_ids {requirements : List Requirement}
    {predicates : List ProgramPredicate} {ids : List RequirementId}
    (rows : RequirementPredicatesCorrespond requirements predicates ids) :
    ids ⊆ requirements.map Requirement.id := by
  induction rows with
  | nil => simp
  | @cons predicate id predicates ids present tail ih =>
    intro selected member
    rcases List.mem_cons.mp member with same | later
    · subst selected
      exact List.mem_map.mpr ⟨_, present, rfl⟩
    · exact ih later

/-- Operational status follows from the actual local branch, then travels
through the real inference progress to the node's final ledger. -/
theorem Origin.operational {state : State} {node : ExpressionNode}
    (origin : Origin state node) :
    ∃ lookup : Lookup,
      node.id = lookup.id ∧
      node.form = .reference lookup.name.value (.local lookup.binder.id) ∧
      node.localSchemeInstantiationStart = some lookup.allocated.inference.next ∧
      lookup.batch.1 <+: node.requirements ∧
      RequirementPredicatesCorrespond state.requirements lookup.predicates lookup.batch.1 ∧
      (∀ requirement ∈ state.requirements, requirement.id ∈ lookup.batch.1 →
        ∀ cutoff, requirement ∈ Detail.generalizeValueBlockingRequirements state cutoff) := by
  obtain ⟨lookup, id, form, start, batchPrefix, progress⟩ := origin
  have issuedFacts := Detail.inferExprFuel_localIdentifier_operational lookup.form lookup.allocation lookup.found
    lookup.accepted lookup.wellFormed lookup.directAllocated
  change RequirementPredicatesCorrespond lookup.result.2.requirements lookup.predicates lookup.batch.1 ∧ _ at issuedFacts
  refine ⟨lookup, id, form, start, batchPrefix, issuedFacts.1.mono progress.included, ?_⟩
  intro requirement present issued cutoff
  apply Detail.operational_requirement_blocks state cutoff present
  have allocatedEq : lookup.allocated = lookup.initial.allocateExpressionId.2 :=
    (congrArg Prod.snd lookup.allocation).symm
  have advancedWF : lookup.advanced.RequirementsWellFormed := by
    change lookup.allocated.RequirementsWellFormed
    rw [allocatedEq]
    exact lookup.wellFormed
  have advancedDirect : lookup.advanced.DirectRequirementsAllocated := by
    change lookup.allocated.DirectRequirementsAllocated
    rw [allocatedEq]
    exact lookup.directAllocated
  have batchWF := State.addRequirementsWithIds_preserves_requirementsWellFormed
    lookup.advanced lookup.predicates advancedWF
  have resultWF := Detail.recordExpressionWithExpected_preserves_requirementsWellFormed lookup.recorded batchWF
  have batchMember : requirement.id ∈ lookup.result.2.requirements.map Requirement.id :=
    correspondence_ids issuedFacts.1 issued
  intro direct
  have earlier := (progress.existing resultWF requirement.id batchMember).mp direct
  have recorded := lookup.recorded
  rw [Detail.recordExpressionWithExpected_direct_eq recorded] at earlier
  exact State.addRequirementsWithIds_not_direct lookup.advanced lookup.predicates advancedWF advancedDirect issued earlier

end LocalReadEvents
end Solcore.Frontend.SourceInference
