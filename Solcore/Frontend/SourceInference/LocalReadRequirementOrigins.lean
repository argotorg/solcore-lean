import Solcore.Frontend.SourceInference.ExpressionProperties

/-! Requirement identities issued by the actual local-reference branch. -/

set_option autoImplicit false
set_option Elab.async false

namespace Solcore.Frontend.SourceInference
open TypeSystem

namespace State

/-- Every recorded direct-call identity names an allocated ledger row. -/
def DirectRequirementsAllocated (state : State) : Prop :=
  state.directCallRequirements ⊆ state.requirements.map Requirement.id

theorem addRequirementsWithIds_direct_eq (state : State)
    (predicates : List ProgramPredicate) :
    (state.addRequirementsWithIds predicates).2.directCallRequirements =
      state.directCallRequirements := by
  induction predicates generalizing state with
  | nil => rfl
  | cons predicate rest ih =>
    exact ih (state.addRequirementWithId predicate).2

/-- A local lookup's fresh batch cannot contain an earlier direct-call ID. -/
theorem addRequirementsWithIds_not_direct (state : State)
    (predicates : List ProgramPredicate)
    (wellFormed : state.RequirementsWellFormed)
    (allocated : state.DirectRequirementsAllocated)
    {id : RequirementId}
    (member : id ∈ (state.addRequirementsWithIds predicates).1) :
    id ∉ (state.addRequirementsWithIds predicates).2.directCallRequirements := by
  rw [addRequirementsWithIds_direct_eq]
  intro direct
  exact addRequirementsWithIds_ids_fresh state predicates wellFormed id member
    (allocated direct)

/-- Marking a newly allocated direct-call batch does not reclassify any row
that was present before that allocation. -/
theorem addRequirementsWithIds_mark_existing (state : State)
    (predicates : List ProgramPredicate)
    (wellFormed : state.RequirementsWellFormed)
    {id : RequirementId} (prior : id ∈ state.requirements.map Requirement.id) :
    id ∈ ((state.addRequirementsWithIds predicates).2.markDirectCallRequirements
      (state.addRequirementsWithIds predicates).1).directCallRequirements ↔
      id ∈ state.directCallRequirements := by
  change id ∈ (state.addRequirementsWithIds predicates).2.directCallRequirements ++
    (state.addRequirementsWithIds predicates).1 ↔ _
  rw [List.mem_append, addRequirementsWithIds_direct_eq]
  constructor
  · rintro (old | fresh)
    · exact old
    · exact False.elim
        (addRequirementsWithIds_ids_fresh state predicates wellFormed id fresh prior)
  · exact Or.inl

end State

namespace Detail

theorem commitCoercionPlan_direct_eq (state : State)
    (plan : List PlannedCoercionStep) :
    (commitCoercionPlan state plan).2.directCallRequirements =
      state.directCallRequirements := by
  induction plan generalizing state with
  | nil => rfl
  | cons step rest ih =>
    change (commitCoercionPlan
      ((state.addRequirementWithId step.predicate).2.addRequirementsWithIds
        step.methodPredicates).2 rest).2.directCallRequirements = _
    rw [ih, State.addRequirementsWithIds_direct_eq]
    rfl

/-- Coercion requirements remain operational; expected-type fitting never
marks either old or newly issued rows as declaration-call templates. -/
theorem withExpected_direct_eq
    {context : Context} {state : State} {actual : InferredExpression}
    {expected : Option Ty} {result : ExpectationResult}
    (accepted : withExpected context state actual expected = .ok result) :
    result.state.directCallRequirements = state.directCallRequirements := by
  unfold withExpected at accepted
  split at accepted
  · cases accepted
    rfl
  · split at accepted
    · cases accepted
      rfl
    · split at accepted
      all_goals try contradiction
      all_goals
        simp only [bind, Except.bind] at accepted
        split at accepted
        · contradiction
        · split at accepted
          · contradiction
          · cases accepted
            exact commitCoercionPlan_direct_eq _ _

theorem recordExpressionWithExpected_direct_eq
    {context : Context} {source : Syntax.Expr} {id : ExpressionId}
    {type : Ty} {form : ExpressionForm} {requirements : List RequirementId}
    {expected : Option Ty} {state : State}
    {localSchemeInstantiationStart : Option Nat}
    {result : InferredExpression × State}
    (accepted : recordExpressionWithExpected context source id type form
      requirements expected state localSchemeInstantiationStart = .ok result) :
    result.2.directCallRequirements = state.directCallRequirements := by
  obtain ⟨fitted, accepted, _, same⟩ :=
    recordExpressionWithExpected_success_record accepted
  rw [same]
  exact withExpected_direct_eq accepted

/-- Every operational ledger row participates in the executable barrier,
regardless of the initializer's cutoff. -/
theorem operational_requirement_blocks
    (state : State) (cutoff : Nat) {requirement : Requirement}
    (present : requirement ∈ state.requirements)
    (operational : requirement.id ∉ state.directCallRequirements) :
    requirement ∈ generalizeValueBlockingRequirements state cutoff := by
  have split : requirement ∈ state.requirements.take cutoff ++
      state.requirements.drop cutoff := by
    simpa only [List.take_append_drop] using present
  rw [mem_generalizeValueBlockingRequirements_iff]
  rcases List.mem_append.mp split with before | after
  · exact .inl before
  · exact .inr ⟨after, operational⟩

/-- The real local-reference branch reissues each predicate into a fresh
operational row and keeps it in the final ledger after expected-type fitting. -/
theorem inferExprFuel_localIdentifier_operational
    {fuel : Nat} {context : Context} {expression : Syntax.Expr}
    {expected : Option Ty} {initial allocated : State}
    {id : ExpressionId} {name : Syntax.Identifier} {binder : TypedBinder}
    {result : InferredExpression × State}
    (form : expression.value = .identifier name)
    (allocation : initial.allocateExpressionId = (id, allocated))
    (found : allocated.lookupBinder? name.value = some binder)
    (accepted : inferExprFuel (fuel + 1) context expression expected initial = .ok result)
    (wellFormed : initial.RequirementsWellFormed)
    (directAllocated : initial.DirectRequirementsAllocated) :
    let start := allocated.inference.next
    let instantiated := binder.scheme.instantiateWithSubstitution start
    let advanced : State :=
      { allocated with inference := { allocated.inference with next := instantiated.next } }
    let predicates := binder.schemeRequirements.map fun requirement =>
      applyPredicate advanced
        (TypedTraitResolution.applySubstitution instantiated.substitution requirement.predicate)
    let batch := advanced.addRequirementsWithIds predicates
    RequirementPredicatesCorrespond result.2.requirements predicates batch.1 ∧
      (∀ requirement ∈ result.2.requirements, requirement.id ∈ batch.1 →
        ∀ cutoff, requirement ∈ generalizeValueBlockingRequirements result.2 cutoff) := by
  dsimp only
  let start := allocated.inference.next
  let instantiated := binder.scheme.instantiateWithSubstitution start
  let advanced : State :=
    { allocated with inference := { allocated.inference with next := instantiated.next } }
  let predicates := binder.schemeRequirements.map fun requirement =>
    applyPredicate advanced
      (TypedTraitResolution.applySubstitution instantiated.substitution requirement.predicate)
  let batch := advanced.addRequirementsWithIds predicates
  have recorded := inferExprFuel_success_localIdentifier_record form allocation found accepted
  change recordExpressionWithExpected context expression id
    (advanced.resolve instantiated.body) (.reference name.value (.local binder.id))
    batch.1 expected batch.2 (some start) = .ok result at recorded
  have sameAllocated : allocated = initial.allocateExpressionId.2 :=
    (congrArg Prod.snd allocation).symm
  have advancedWellFormed : advanced.RequirementsWellFormed := by
    change allocated.RequirementsWellFormed
    rw [sameAllocated]
    exact wellFormed
  have advancedDirectAllocated : advanced.DirectRequirementsAllocated := by
    change allocated.DirectRequirementsAllocated
    rw [sameAllocated]
    exact directAllocated
  refine ⟨(State.addRequirementsWithIds_correspond advanced predicates).mono
    (recordExpressionWithExpected_requirements_subset recorded), ?_⟩
  intro requirement present issued cutoff
  apply operational_requirement_blocks result.2 cutoff present
  rw [recordExpressionWithExpected_direct_eq recorded]
  exact State.addRequirementsWithIds_not_direct advanced predicates
    advancedWellFormed advancedDirectAllocated issued

end Detail
end Solcore.Frontend.SourceInference
