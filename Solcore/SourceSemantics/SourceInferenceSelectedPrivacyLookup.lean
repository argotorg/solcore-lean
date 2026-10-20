import Solcore.SourceSemantics.SourceInferenceSelectedLocalSchemePrivacy
import Solcore.Frontend.SourceInference.LocalReadRequirementOrigins

/-! The actual local-reference branch preserves protected earlier variables.
The returned type, issued predicates and continuation state come from the
accepted lookup computation, including its real instantiation allocator. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
open Frontend SourceInference TypeSystem

theorem requirementBatch_inference (state : State) (predicates : List ProgramPredicate) :
    (state.addRequirementsWithIds predicates).2.inference = state.inference := by
  induction predicates generalizing state with
  | nil => rfl
  | cons head tail ih => exact ih _

theorem requirementBatch_binders (state : State) (predicates : List ProgramPredicate) :
    (state.addRequirementsWithIds predicates).2.localBinders = state.localBinders := by
  induction predicates generalizing state with
  | nil => rfl
  | cons head tail ih => exact ih _

/-- Every new row has one of the predicates actually passed to allocation. -/
theorem requirementBatch_row_origin (state : State) (predicates : List ProgramPredicate)
    {row : Requirement} (member : row ∈ (state.addRequirementsWithIds predicates).2.requirements) :
    row ∈ state.requirements ∨ row.predicate ∈ predicates := by
  induction predicates generalizing state with
  | nil => exact .inl member
  | cons head tail ih =>
    rcases ih (state.addRequirementWithId head).2 member with old | new
    · rcases List.mem_append.mp old with old | fresh
      · exact .inl old
      · cases List.mem_singleton.mp fresh
        exact .inr List.mem_cons_self
    · exact .inr (List.mem_cons_of_mem _ new)

/-- No privacy premise is imposed on discarded substitution entries. The
live binder and its actual fresh instantiation suffice for this source call. -/
theorem inferExprFuel_local_noExpected_private
    {protectedVars : List TypeVarId} {fuel : Nat} {context : SourceInference.Context}
    {expression : Syntax.Expr} {initial allocated : State} {id : ExpressionId}
    {name : Syntax.Identifier} {binder : TypedBinder} {result : InferredExpression × State}
    (form : expression.value = .identifier name)
    (allocation : initial.allocateExpressionId = (id, allocated))
    (found : allocated.lookupBinder? name.value = some binder)
    (accepted : Detail.inferExprFuel (fuel + 1) context expression none initial = .ok result)
    (ready : initial.InferenceReady)
    (bound : ∀ metavariable ∈ protectedVars, metavariable.index < initial.inference.next)
    (unique : binder.scheme.quantified.Nodup)
    (live : LiveBindersSafe protectedVars initial) :
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
  have liveAllocated : LiveBindersSafe protectedVars allocated := by
    apply live.transport
    · rw [allocatedEq]
      rfl
    · apply SafeTransport.of_substitution_eq
      rw [allocatedEq]
      rfl
  have privacy := lookup_instantiation_safe readyAllocated boundAllocated unique liveAllocated found
  let advanced := instantiatedState allocated binder.scheme
  let predicates := binder.schemeRequirements.map fun requirement =>
    Detail.applyPredicate advanced
      (TypedTraitResolution.applySubstitution
        (binder.scheme.instantiateWithSubstitution allocated.inference.next).substitution requirement.predicate)
  have recorded := Detail.inferExprFuel_success_localIdentifier_record form allocation found accepted
  change Detail.recordExpressionWithExpected context expression id
    (advanced.resolve (binder.scheme.instantiateWithSubstitution allocated.inference.next).body)
    (.reference name.value (.local binder.id)) (advanced.addRequirementsWithIds predicates).1 none
    (advanced.addRequirementsWithIds predicates).2 (some allocated.inference.next) = .ok result at recorded
  simp only [Detail.recordExpressionWithExpected, Detail.withExpected, bind, Except.bind,
    Detail.recordExpression, pure, Pure.pure, Except.pure, Except.ok.injEq] at recorded
  cases recorded
  have sameInference := requirementBatch_inference advanced predicates
  have sameSubstitution : (advanced.addRequirementsWithIds predicates).2.inference.substitution = initial.inference.substitution := by
    rw [sameInference]
    change allocated.inference.substitution = initial.inference.substitution
    rw [allocatedEq]
    rfl
  have transport : SafeTransport protectedVars initial
      (advanced.addRequirementsWithIds predicates).2 := .of_substitution_eq sameSubstitution
  refine ⟨transport, ?_, ?_, ?_⟩
  · simpa only [Safe, State.resolve, InferState.resolve, State.recordNode, requirementBatch_inference, advanced, instantiatedState,
      readyAllocated.solved.apply_idempotent] using privacy.2.1
  · apply live.transport
    · change (advanced.addRequirementsWithIds predicates).2.localBinders = initial.localBinders
      rw [requirementBatch_binders]
      change allocated.localBinders = initial.localBinders
      rw [allocatedEq]
      rfl
    · exact transport
  · intro row member fresh
    have member' : row ∈ (advanced.addRequirementsWithIds predicates).2.requirements := member
    rcases requirementBatch_row_origin advanced predicates member' with old | introduced
    · apply False.elim
      apply fresh
      change row ∈ allocated.requirements at old
      rw [allocatedEq] at old
      exact old
    · have safe := privacy.2.2 row.predicate introduced
      simpa only [PredicateSafe, Safe, State.resolve, InferState.resolve, State.recordNode, sameInference] using safe

end Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
