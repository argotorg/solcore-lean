import Solcore.SourceSemantics.SourceInferenceSelectedPrivacyIssuedRequirements

/-! The complete accepted local-reference branch, including its real
expected-type fit, coercion plan and committed requirement rows. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
open Frontend SourceInference TypeSystem

theorem recordExpressionWithExpected_private
    {protectedVars : List TypeVarId} {context : SourceInference.Context}
    {source : Syntax.Expr} {id : ExpressionId} {type : Ty} {form : ExpressionForm}
    {requirements : List RequirementId} {expected : Option Ty} {state : State}
    {start : Option Nat} {result : InferredExpression × State}
    (catalog : SignatureCatalogWellFormed context.signatures)
    (ready : state.InferenceReady)
    (typeBelow : type.VariablesBelow state.inference.next)
    (expectedBelow : ∀ type ∈ expected, type.VariablesBelow state.inference.next)
    (typeSafe : Safe protectedVars state type)
    (expectedSafe : ∀ type ∈ expected, Safe protectedVars state type)
    (live : LiveBindersSafe protectedVars state)
    (accepted : Detail.recordExpressionWithExpected context source id type form requirements
      expected state start = .ok result) :
    SafeTransport protectedVars state result.2 ∧
    Safe protectedVars result.2 result.1.type ∧
    LiveBindersSafe protectedVars result.2 ∧
    ∀ row ∈ result.2.requirements, row ∉ state.requirements →
      PredicateSafe protectedVars result.2 row.predicate := by
  unfold Detail.recordExpressionWithExpected at accepted
  cases fitted : Detail.withExpected context state {id, type} expected with
  | error error => simp [fitted, bind, Except.bind] at accepted
  | ok fit =>
    simp only [fitted, bind, Except.bind, pure, Pure.pure, Except.pure, Except.ok.injEq] at accepted
    cases accepted
    have main := withExpected_private ready typeBelow expectedBelow typeSafe expectedSafe live fitted
    have issued := withExpected_new_requirements_private catalog ready typeSafe expectedSafe fitted
    exact ⟨main.1, main.2.1, main.2.2.transport rfl (.of_substitution_eq rfl), issued⟩

/-- Every conclusion comes from this accepted source reference. The input
privacy concerns live unquantified binder variables and the actual expectation. -/
theorem inferExprFuel_local_private
    {protectedVars : List TypeVarId} {fuel : Nat} {context : SourceInference.Context}
    {expression : Syntax.Expr} {initial allocated : State} {id : ExpressionId}
    {name : Syntax.Identifier} {binder : TypedBinder} {expected : Option Ty}
    {result : InferredExpression × State}
    (catalog : SignatureCatalogWellFormed context.signatures)
    (form : expression.value = .identifier name)
    (allocation : initial.allocateExpressionId = (id, allocated))
    (found : allocated.lookupBinder? name.value = some binder)
    (accepted : Detail.inferExprFuel (fuel + 1) context expression expected initial = .ok result)
    (ready : initial.InferenceReady)
    (bound : ∀ metavariable ∈ protectedVars, metavariable.index < initial.inference.next)
    (unique : binder.scheme.quantified.Nodup)
    (live : LiveBindersSafe protectedVars initial)
    (expectedBelow : ∀ type ∈ expected, type.VariablesBelow initial.inference.next)
    (expectedSafe : ∀ type ∈ expected, Safe protectedVars initial type) :
    SafeTransport protectedVars initial result.2 ∧
    Safe protectedVars result.2 result.1.type ∧
    LiveBindersSafe protectedVars result.2 ∧
    ∀ row ∈ result.2.requirements, row ∉ initial.requirements →
      PredicateSafe protectedVars result.2 row.predicate := by
  have allocatedEq : allocated = initial.allocateExpressionId.2 := (congrArg Prod.snd allocation).symm
  have readyAllocated : allocated.InferenceReady := by
    rw [allocatedEq]
    exact ⟨ready.solved, ready.bindersBelow⟩
  have boundAllocated : ∀ metavariable ∈ protectedVars, metavariable.index < allocated.inference.next := by
    intro metavariable member
    rw [allocatedEq]
    exact bound metavariable member
  have allocationTransport : SafeTransport protectedVars initial allocated := by
    apply SafeTransport.of_substitution_eq
    rw [allocatedEq]
    rfl
  have liveAllocated : LiveBindersSafe protectedVars allocated := by
    apply live.transport _ allocationTransport
    rw [allocatedEq]
    rfl
  have privacy := lookup_instantiation_safe readyAllocated boundAllocated unique liveAllocated found
  have inference := Detail.localBinderInstantiation_inferenceProperties readyAllocated found
  let advanced := instantiatedState allocated binder.scheme
  let predicates := binder.schemeRequirements.map fun requirement =>
    Detail.applyPredicate advanced
      (TypedTraitResolution.applySubstitution
        (binder.scheme.instantiateWithSubstitution allocated.inference.next).substitution requirement.predicate)
  let recorded := (advanced.addRequirementsWithIds predicates).2
  have advancedReady : advanced.InferenceReady := inference.2.1
  have recordedReady : recorded.InferenceReady :=
    State.InferenceReady.addRequirementsWithIds predicates advancedReady
  have sameInference : recorded.inference = advanced.inference := requirementBatch_inference _ _
  have sameBinders : recorded.localBinders = initial.localBinders := by
    rw [requirementBatch_binders]
    change allocated.localBinders = initial.localBinders
    rw [allocatedEq]
    rfl
  have beforeFit : SafeTransport protectedVars initial recorded := by
    apply SafeTransport.of_substitution_eq
    rw [sameInference]
    change allocated.inference.substitution = initial.inference.substitution
    rw [allocatedEq]
    rfl
  have nextBound : initial.inference.next ≤ recorded.inference.next := by
    rw [sameInference]
    have sameNext : allocated.inference.next = initial.inference.next := by
      rw [allocatedEq]
      rfl
    rw [← sameNext]
    exact inference.1.next_le
  have typeBelow : (advanced.resolve
      (binder.scheme.instantiateWithSubstitution allocated.inference.next).body).VariablesBelow
        recorded.inference.next := by
    rw [sameInference]
    exact inference.2.2
  have typeSafe : Safe protectedVars recorded (advanced.resolve
      (binder.scheme.instantiateWithSubstitution allocated.inference.next).body) := by
    simpa only [Safe, State.resolve, InferState.resolve, sameInference] using privacy.2.1
  have recordAccepted := Detail.inferExprFuel_success_localIdentifier_record form allocation found accepted
  change Detail.recordExpressionWithExpected context expression id
    (advanced.resolve (binder.scheme.instantiateWithSubstitution allocated.inference.next).body)
    (.reference name.value (.local binder.id)) (advanced.addRequirementsWithIds predicates).1 expected
    recorded (some allocated.inference.next) = .ok result at recordAccepted
  have tail := recordExpressionWithExpected_private catalog recordedReady typeBelow
    (fun type member => (expectedBelow type member).weaken nextBound) typeSafe
    (fun type member => beforeFit type (expectedSafe type member))
    (live.transport sameBinders beforeFit) recordAccepted
  refine ⟨beforeFit.trans tail.1, tail.2.1, tail.2.2.1, ?_⟩
  intro row member fresh
  by_cases earlier : row ∈ recorded.requirements
  · rcases requirementBatch_row_origin advanced predicates earlier with old | issued
    · apply False.elim
      apply fresh
      change row ∈ allocated.requirements at old
      rw [allocatedEq] at old
      exact old
    · intro type typeMember
      apply tail.1
      have safe := privacy.2.2 row.predicate issued type typeMember
      simpa only [Safe, State.resolve, InferState.resolve, sameInference] using safe
  · exact tail.2.2.2 row member earlier

end Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
