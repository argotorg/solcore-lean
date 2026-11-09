import Solcore.SourceSemantics.Internal.Selected.State
import Solcore.Frontend.SourceInference.Internal.LocalReadOrigins

/-!
# Privacy of references and coercions

Local lookup, references, arguments, operators and the coercion search keep scheme variables
private.
-/

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceSelectedPrivacyLookup
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
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceSelectedPrivacyContinuation
/-! Privacy for the actual expected-type continuation. Coercion commitment
allocates obligations but does not change type substitution or lexical binders. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
open Frontend SourceInference TypeSystem

private theorem commit_binders (state : State) (plan : List Detail.PlannedCoercionStep) :
    (Detail.commitCoercionPlan state plan).2.localBinders = state.localBinders := by
  induction plan generalizing state with
  | nil => rfl
  | cons step rest ih =>
    simp only [Detail.commitCoercionPlan]
    rw [ih, requirementBatch_binders]
    rfl

/-- This is derived from the successful fit, including the real unifier or
coercion-plan branch. It places no restriction on dead substitution entries. -/
theorem withExpected_private
    {protectedVars : List TypeVarId} {context : SourceInference.Context}
    {state : State} {actual : InferredExpression} {expected : Option Ty}
    {result : Detail.ExpectationResult}
    (ready : state.InferenceReady)
    (actualBelow : actual.type.VariablesBelow state.inference.next)
    (expectedBelow : ∀ type ∈ expected, type.VariablesBelow state.inference.next)
    (actualSafe : Safe protectedVars state actual.type)
    (expectedSafe : ∀ type ∈ expected, Safe protectedVars state type)
    (live : LiveBindersSafe protectedVars state)
    (accepted : Detail.withExpected context state actual expected = .ok result) :
    SafeTransport protectedVars state result.state ∧
    Safe protectedVars result.state result.expression.type ∧
    LiveBindersSafe protectedVars result.state := by
  have resultReady := (Detail.withExpected_inferenceProperties ready actualBelow expectedBelow accepted).2.1
  cases expected with
  | none =>
    simp only [Detail.withExpected, Except.ok.injEq] at accepted
    cases accepted
    exact ⟨.refl _ _, safe_resolved ready actualSafe, live⟩
  | some expected =>
    have expectedSafe := expectedSafe expected (by simp)
    cases unified : state.inference.unify actual.type expected with
    | ok inference =>
      simp only [Detail.withExpected, unified, Except.ok.injEq] at accepted
      cases accepted
      have actualUnify : Detail.unify state actual.type expected =
          .ok {state with inference} := by
        simp [Detail.unify, unified, Detail.liftUnification, bind, Except.bind]
      have transport := ProtectedVariables.unify actualSafe expectedSafe actualUnify
      exact ⟨transport, safe_resolved resultReady (transport _ expectedSafe),
        live.transport rfl transport⟩
    | error error =>
      cases error with
      | occursCheck _ _ => simp [Detail.withExpected, unified] at accepted
      | exhausted => simp [Detail.withExpected, unified] at accepted
      | mismatch left right =>
        simp only [Detail.withExpected, unified] at accepted
        cases planned : Detail.coercionPlan? context state
            (state.resolve actual.type) (state.resolve expected) with
        | error error => simp [planned, bind, Except.bind] at accepted
        | ok option =>
          cases option with
          | none => simp [planned, bind, Except.bind] at accepted
          | some plan =>
            simp only [planned, bind, Except.bind] at accepted
            change Except.ok _ = Except.ok result at accepted
            cases Except.ok.inj accepted
            have transport : SafeTransport protectedVars state
                (Detail.commitCoercionPlan state plan).2 := by
              intro type safe
              simpa only [Safe, Detail.commitCoercionPlan_resolve] using safe
            refine ⟨transport, ?_, live.transport (commit_binders _ _) transport⟩
            simpa only [Safe, Detail.commitCoercionPlan_resolve] using
              safe_resolved ready expectedSafe

end Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceSelectedPrivacyCoercions
/-! The coercion search derives private obligations from its actual source,
ground intermediate types, and the selected closed method catalog. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
open Frontend SourceInference TypeSystem

private theorem safe_of_freeVariables_nil {protectedVars : List TypeVarId}
    {state : State} {type : Ty} (closed : type.freeVariables = []) :
    Safe protectedVars state type :=
  safe_closed _ _ (by intro metavariable occurs; simp [closed] at occurs)

private theorem predicate_formed_private {protectedVars : List TypeVarId}
    {state : State} {context : SourceSemantics.Context} {predicate : ProgramPredicate}
    (formed : PredicateWellFormed context predicate) :
    PredicateSafe protectedVars state predicate := by
  intro type member
  rcases List.mem_cons.mp member with rfl | member
  · exact safe_of_freeVariables_nil
      (StructuralSubstitution.TypeWellFormed.freeVariables_eq_nil formed.subject)
  · exact safe_of_freeVariables_nil
      (StructuralSubstitution.TypeWellFormed.freeVariables_eq_nil (formed.arguments _ member))

private theorem predicate_parameters_private {protectedVars : List TypeVarId}
    {state : State} {predicate : ProgramPredicate} {substitution : ParameterSubstitution}
    (original : PredicateSafe protectedVars state predicate)
    (range : ∀ parameter replacement, (parameter,replacement) ∈ substitution →
      Safe protectedVars state replacement) :
    PredicateSafe protectedVars state (predicate.applyParameters substitution) := by
  intro type member
  rcases List.mem_cons.mp member with rfl | member
  · exact safe_parameterApply range (original _ (by simp))
  · obtain ⟨originalType, originalMember, rfl⟩ := List.mem_map.mp member
    exact safe_parameterApply range (original _ (by simp [originalMember]))

private theorem profile_private {protectedVars : List TypeVarId}
    {state : State} {context : SourceInference.Context} {trait : Resolved.DeclarationId}
    {profile : Detail.CoercionMethodProfile}
    (catalog : SignatureCatalogWellFormed context.signatures)
    (accepted : Detail.coercionMethodProfile? context trait = .ok (some profile)) :
    ∀ predicate ∈ profile.method.wherePredicates, PredicateSafe protectedVars state predicate := by
  unfold Detail.coercionMethodProfile? at accepted
  cases found : context.signatures.trait? trait with
  | none => simp [found, bind, Except.bind] at accepted
  | some signature =>
    simp only [found, pure, Pure.pure, Except.pure, bind, Except.bind] at accepted
    have signatureMember : signature ∈ context.signatures.traits :=
      List.mem_of_find?_eq_some found
    split at accepted
    · cases methods : signature.methods.filter (fun method => method.name == "coerce") with
      | nil => simp [methods] at accepted
      | cons method rest =>
        cases rest with
        | cons second rest => simp [methods] at accepted
        | nil =>
          simp only [methods, Except.ok.injEq, Option.some.injEq] at accepted
          cases accepted
          have methodMember : method ∈ signature.methods :=
            (List.mem_filter.mp (show method ∈ signature.methods.filter
              (fun method => method.name == "coerce") by rw [methods]; simp)).1
          intro predicate member
          exact predicate_formed_private
            (((catalog.traits_semantic signature signatureMember).methods method methodMember).predicates
              predicate member)
    · simp_all

private theorem methodPredicates_private {protectedVars : List TypeVarId}
    {state : State} {profile : Option Detail.CoercionMethodProfile}
    {source target : Ty} {predicates : List ProgramPredicate}
    (profileSafe : ∀ value ∈ profile, ∀ predicate ∈ value.method.wherePredicates,
      PredicateSafe protectedVars state predicate)
    (sourceSafe : Safe protectedVars state source)
    (targetSafe : Safe protectedVars state target)
    (accepted : Detail.coercionMethodPredicates profile source target = .ok predicates) :
    ∀ predicate ∈ predicates, PredicateSafe protectedVars state predicate := by
  cases profile with
  | none => simp [Detail.coercionMethodPredicates] at accepted; subst predicates; simp
  | some profile =>
    simp only [Detail.coercionMethodPredicates] at accepted
    split at accepted
    · simp only [pure, Pure.pure, Except.pure, Except.ok.injEq] at accepted
      subst predicates
      intro predicate member
      obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp member
      apply predicate_parameters_private (profileSafe profile (by simp) original originalMember)
      intro parameter replacement member
      have choice := (List.of_mem_zip member).2
      simp only [List.mem_cons, List.not_mem_nil, or_false] at choice
      rcases choice with rfl | rfl
      · exact sourceSafe
      · exact targetSafe
    · simp [throw, Functor.map, Except.map] at accepted

private def EdgeSafe (protectedVars : List TypeVarId) (state : State)
    (edge : Detail.CoercionEdge) : Prop :=
  Safe protectedVars state edge.source ∧ Safe protectedVars state edge.target ∧
    PredicateSafe protectedVars state edge.predicate

private theorem ground_private {protectedVars : List TypeVarId} {state : State} {type : Ty}
    (ground : Detail.isGroundCoercionTarget type = true) : Safe protectedVars state type := by
  simp only [Detail.isGroundCoercionTarget, Bool.and_eq_true] at ground
  have closed : type.freeVariables = [] := by simpa using ground.1
  exact safe_of_freeVariables_nil closed

private theorem coercionRuleEdge_private {protectedVars : List TypeVarId} {state : State}
    {trait : Resolved.DeclarationId} {source : Ty} {rule : ProgramImplRule}
    {edge : Detail.CoercionEdge}
    (sourceSafe : Safe protectedVars state source)
    (accepted : Detail.coercionRuleEdge? trait source rule = some edge) :
    EdgeSafe protectedVars state edge := by
  by_cases traitMismatch : (rule.head.trait != ProgramTraitId.declaration trait) = true
  · simp [Detail.coercionRuleEdge?, traitMismatch] at accepted
  · simp only [Detail.coercionRuleEdge?, traitMismatch] at accepted
    cases arguments : (TypedTraitResolution.freshenRuleFor rule {
        trait := ProgramTraitId.declaration trait, subject := source, arguments := [source]
      }).head.arguments with
    | nil => simp [arguments, bind, Option.bind] at accepted
    | cons target rest =>
      cases rest with
      | cons second tail => simp [arguments, bind, Option.bind] at accepted
      | nil =>
        simp only [arguments, bind, Option.bind] at accepted
        cases unified : (Unification.unify [{
            left := (TypedTraitResolution.freshenRuleFor rule {
              trait := ProgramTraitId.declaration trait, subject := source, arguments := [source]
            }).head.subject
            right := source
          }]).toOption with
        | none => simp [unified] at accepted
        | some substitution =>
          simp only [unified] at accepted
          by_cases blocked : substitution.domain.any source.freeVariables.contains = true
          · simp [blocked] at accepted
          · by_cases ground : Detail.isGroundCoercionTarget (substitution.apply target) = true
            · simp [blocked, ground] at accepted
              subst edge
              have targetSafe : Safe protectedVars state (substitution.apply target) := ground_private ground
              refine ⟨sourceSafe, targetSafe, ?_⟩
              intro type member
              simp only [List.mem_cons, List.not_mem_nil, or_false] at member
              rcases member with rfl | rfl
              · exact sourceSafe
              · exact targetSafe
            · simp [blocked, ground] at accepted


private theorem assumptionEdges_private {protectedVars : List TypeVarId} {state : State}
    {context : SourceInference.Context} {trait : Resolved.DeclarationId} {source : Ty}
    {edge : Detail.CoercionEdge} (sourceSafe : Safe protectedVars state source)
    (member : edge ∈ Detail.assumptionCoercionEdges context state trait source) :
    EdgeSafe protectedVars state edge := by
  unfold Detail.assumptionCoercionEdges at member
  obtain ⟨assumption, _, produced⟩ := List.mem_filterMap.mp member
  dsimp only at produced
  split at produced
  · cases produced
  · rename_i matching
    have subject : (Detail.applyPredicate state assumption).subject = source := by
      simp only [Bool.or_eq_true, bne_iff_ne, not_or] at matching
      exact Classical.not_not.mp matching.2
    split at produced
    · rename_i target arguments
      split at produced
      · rename_i ground
        cases Option.some.inj produced
        have targetSafe : Safe protectedVars state target := ground_private ground
        refine ⟨sourceSafe, targetSafe, ?_⟩
        intro type member
        rw [subject, arguments] at member
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl
        · exact sourceSafe
        · exact targetSafe
      · cases produced
    · cases produced

private def FullEdgeSafe (protectedVars : List TypeVarId) (state : State)
    (edge : Detail.CoercionEdge) : Prop :=
  EdgeSafe protectedVars state edge ∧
    ∀ predicate ∈ edge.methodPredicates, PredicateSafe protectedVars state predicate

private theorem attachMethods_private {protectedVars : List TypeVarId} {state : State}
    {profile : Option Detail.CoercionMethodProfile}
    (profileSafe : ∀ value ∈ profile, ∀ predicate ∈ value.method.wherePredicates,
      PredicateSafe protectedVars state predicate)
    (edges : List Detail.CoercionEdge)
    (rawSafe : ∀ edge ∈ edges, EdgeSafe protectedVars state edge)
    {results : List Detail.CoercionEdge}
    (accepted : edges.mapM (fun edge => do
      let methodPredicates ← Detail.coercionMethodPredicates profile edge.source edge.target
      pure { edge with methodPredicates }) = Except.ok results) :
    ∀ edge ∈ results, FullEdgeSafe protectedVars state edge := by
  induction edges generalizing results with
  | nil => simp at accepted; subst results; simp
  | cons head tail ih =>
    simp only [List.mapM_cons] at accepted
    cases methods : Detail.coercionMethodPredicates profile head.source head.target with
    | error error => simp [methods, bind, Except.bind] at accepted
    | ok predicates =>
      simp only [methods, bind, Except.bind, pure, Pure.pure, Except.pure] at accepted
      cases tails : tail.mapM (fun edge => do
          let methodPredicates ← Detail.coercionMethodPredicates profile edge.source edge.target
          pure { edge with methodPredicates }) with
      | error error =>
        dsimp only [bind, Except.bind, pure, Pure.pure, Except.pure] at tails
        simp [tails] at accepted
      | ok rest =>
        dsimp only [bind, Except.bind, pure, Pure.pure, Except.pure] at tails
        simp only [tails, Except.ok.injEq] at accepted
        subst results
        intro edge member
        rcases List.mem_cons.mp member with rfl | member
        · have raw := rawSafe head (by simp)
          exact ⟨raw, methodPredicates_private profileSafe raw.1 raw.2.1 methods⟩
        · exact ih (fun edge member => rawSafe edge (by simp [member])) tails edge member

private theorem coercionEdges_private {protectedVars : List TypeVarId} {state : State}
    {context : SourceInference.Context} {profile : Option Detail.CoercionMethodProfile}
    {trait : Resolved.DeclarationId} {source : Ty} {edges : List Detail.CoercionEdge}
    (profileSafe : ∀ value ∈ profile, ∀ predicate ∈ value.method.wherePredicates,
      PredicateSafe protectedVars state predicate)
    (sourceSafe : Safe protectedVars state source)
    (accepted : Detail.coercionEdges context state profile trait source = .ok edges) :
    ∀ edge ∈ edges, FullEdgeSafe protectedVars state edge := by
  apply attachMethods_private profileSafe _ _ accepted
  intro edge member
  rw [List.mem_eraseDups, List.mem_append] at member
  rcases member with rules | assumptions
  · obtain ⟨rule, _, produced⟩ := List.mem_filterMap.mp rules
    exact coercionRuleEdge_private sourceSafe produced
  · exact assumptionEdges_private sourceSafe assumptions


def PlannedStepSafe (protectedVars : List TypeVarId) (state : State)
    (step : Detail.PlannedCoercionStep) : Prop :=
  Safe protectedVars state step.source ∧ Safe protectedVars state step.target ∧
    PredicateSafe protectedVars state step.predicate ∧
    ∀ predicate ∈ step.methodPredicates, PredicateSafe protectedVars state predicate

private def PathSafe (protectedVars : List TypeVarId) (state : State)
    (path : Detail.CoercionPath) : Prop :=
  Safe protectedVars state path.current ∧ ∀ step ∈ path.steps, PlannedStepSafe protectedVars state step

private theorem viable_member {context : SourceInference.Context} {state : State}
    (edges : List Detail.CoercionEdge) {edge : Detail.CoercionEdge}
    (member : edge ∈ (Detail.viableCoercionEdges context state edges).viable) : edge ∈ edges := by
  induction edges with
  | nil => cases member
  | cons head tail ih =>
    unfold Detail.viableCoercionEdges at member
    cases viable : Detail.coercionEvidenceViable context state head.predicate head.methodPredicates with
    | error error =>
      simp only [viable] at member
      exact List.mem_cons_of_mem _ (ih member)
    | ok value =>
      cases value with
      | false =>
        simp only [viable] at member
        exact List.mem_cons_of_mem _ (ih member)
      | true =>
        simp only [viable, List.mem_cons] at member
        rcases member with rfl | member
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (ih member)

private theorem expandPath_private {protectedVars : List TypeVarId} {state : State}
    {context : SourceInference.Context} {profile : Option Detail.CoercionMethodProfile}
    {trait : Resolved.DeclarationId} {path : Detail.CoercionPath}
    {result : Detail.CoercionExpansion}
    (profileSafe : ∀ value ∈ profile, ∀ predicate ∈ value.method.wherePredicates,
      PredicateSafe protectedVars state predicate)
    (pathSafe : PathSafe protectedVars state path)
    (accepted : Detail.expandCoercionPath context state profile trait path = .ok result) :
    ∀ next ∈ result.paths, PathSafe protectedVars state next := by
  unfold Detail.expandCoercionPath at accepted
  cases edges : Detail.coercionEdges context state profile trait path.current with
  | error error => simp [edges, bind, Except.bind] at accepted
  | ok candidates =>
    simp only [edges, bind, Except.bind, pure, Pure.pure, Except.pure, Except.ok.injEq] at accepted
    cases accepted
    intro next member
    obtain ⟨edge, edgeMember, rfl⟩ := List.mem_map.mp member
    have safe := coercionEdges_private profileSafe pathSafe.1 edges edge
      (List.mem_filter.mp (viable_member _ edgeMember)).1
    refine ⟨safe.1.2.1, ?_⟩
    intro step stepMember
    rcases List.mem_append.mp stepMember with old | fresh
    · exact pathSafe.2 step old
    · cases List.mem_singleton.mp fresh
      exact ⟨safe.1.1, safe.1.2.1, safe.1.2.2, safe.2⟩

private theorem expandPaths_private {protectedVars : List TypeVarId} {state : State}
    {context : SourceInference.Context} {profile : Option Detail.CoercionMethodProfile}
    {trait : Resolved.DeclarationId} (paths : List Detail.CoercionPath)
    {result : Detail.CoercionExpansion}
    (profileSafe : ∀ value ∈ profile, ∀ predicate ∈ value.method.wherePredicates,
      PredicateSafe protectedVars state predicate)
    (pathsSafe : ∀ path ∈ paths, PathSafe protectedVars state path)
    (accepted : Detail.expandCoercionPaths context state profile trait paths = .ok result) :
    ∀ next ∈ result.paths, PathSafe protectedVars state next := by
  induction paths generalizing result with
  | nil => simp [Detail.expandCoercionPaths] at accepted; subst result; simp
  | cons head tail ih =>
    simp only [Detail.expandCoercionPaths] at accepted
    cases headResult : Detail.expandCoercionPath context state profile trait head with
    | error error => simp [headResult, bind, Except.bind] at accepted
    | ok first =>
      simp only [headResult, bind, Except.bind] at accepted
      cases tailResult : Detail.expandCoercionPaths context state profile trait tail with
      | error error => simp [tailResult] at accepted
      | ok rest =>
        simp only [tailResult, pure, Pure.pure, Except.pure, Except.ok.injEq] at accepted
        cases accepted
        intro next member
        rcases List.mem_append.mp member with firstMember | restMember
        · exact expandPath_private profileSafe (pathsSafe _ (by simp)) headResult _ firstMember
        · exact ih (fun path member => pathsSafe path (by simp [member])) tailResult _ restMember

private theorem selectPath_private {protectedVars : List TypeVarId} {state : State}
    {source target : Ty} {paths : List Detail.CoercionPath}
    {steps : List Detail.PlannedCoercionStep}
    (pathsSafe : ∀ path ∈ paths, PathSafe protectedVars state path)
    (accepted : Detail.selectCoercionPath source target paths = .ok (some steps)) :
    ∀ step ∈ steps, PlannedStepSafe protectedVars state step := by
  unfold Detail.selectCoercionPath at accepted
  cases found : (paths.filter fun path => path.current == target).eraseDups with
  | nil => simp [found] at accepted
  | cons path rest =>
    cases rest with
    | cons second tail => simp [found] at accepted
    | nil =>
      simp only [found, Except.ok.injEq, Option.some.injEq] at accepted
      subst steps
      have member : path ∈ paths :=
        (List.mem_filter.mp (List.mem_eraseDups.mp
          (show path ∈ (paths.filter fun path => path.current == target).eraseDups by rw [found]; simp))).1
      exact (pathsSafe path member).2

private theorem finish_not_some {blocked : List Error} {steps : List Detail.PlannedCoercionStep}
    (accepted : Detail.finishCoercionSearch blocked = .ok (some steps)) : False := by
  cases blocked <;> simp [Detail.finishCoercionSearch] at accepted

private theorem searchPaths_private {protectedVars : List TypeVarId} {state : State}
    {context : SourceInference.Context} {profile : Option Detail.CoercionMethodProfile}
    {trait : Resolved.DeclarationId} {source target : Ty}
    (fuel : Nat) {frontier : List Detail.CoercionPath} {blocked : List Error}
    {steps : List Detail.PlannedCoercionStep}
    (profileSafe : ∀ value ∈ profile, ∀ predicate ∈ value.method.wherePredicates,
      PredicateSafe protectedVars state predicate)
    (frontierSafe : ∀ path ∈ frontier, PathSafe protectedVars state path)
    (accepted : Detail.searchCoercionPaths context state profile trait source target
      fuel frontier blocked = .ok (some steps)) :
    ∀ step ∈ steps, PlannedStepSafe protectedVars state step := by
  induction fuel generalizing frontier blocked with
  | zero =>
    simp only [Detail.searchCoercionPaths] at accepted
    cases expanded : Detail.expandCoercionPaths context state profile trait frontier with
    | error error => simp [expanded, bind, Except.bind] at accepted
    | ok beyond =>
      simp only [expanded, bind, Except.bind] at accepted
      split at accepted
      · exact (finish_not_some accepted).elim
      · cases accepted
  | succ fuel ih =>
    simp only [Detail.searchCoercionPaths] at accepted
    cases expanded : Detail.expandCoercionPaths context state profile trait frontier with
    | error error => simp [expanded, bind, Except.bind] at accepted
    | ok next =>
      simp only [expanded, bind, Except.bind] at accepted
      have nextSafe := expandPaths_private frontier profileSafe frontierSafe expanded
      cases selected : Detail.selectCoercionPath source target next.paths with
      | error error => simp [selected] at accepted
      | ok option =>
        cases option with
        | some chosen =>
          simp only [selected, pure, Pure.pure, Except.pure,
            Except.ok.injEq, Option.some.injEq] at accepted
          subst steps
          exact selectPath_private nextSafe selected
        | none =>
          simp only [selected] at accepted
          split at accepted
          · exact (finish_not_some accepted).elim
          · exact ih nextSafe accepted


/-- Every obligation in a successful search is private. This follows the
actual direct/search/fallback choice and permits legacy profiles without a
named method. No solver entailment is used as a type-formation premise. -/
theorem coercionPlan_private {protectedVars : List TypeVarId} {state : State}
    {context : SourceInference.Context} {source target : Ty}
    {steps : List Detail.PlannedCoercionStep}
    (catalog : SignatureCatalogWellFormed context.signatures)
    (sourceSafe : Safe protectedVars state source)
    (targetSafe : Safe protectedVars state target)
    (accepted : Detail.coercionPlan? context state source target = .ok (some steps)) :
    ∀ step ∈ steps, PlannedStepSafe protectedVars state step := by
  unfold Detail.coercionPlan? at accepted
  cases traitResult : Detail.conventionalTraitWithArity? context "Coerce" 2 with
  | error error => simp [traitResult, bind, Except.bind] at accepted
  | ok option =>
    cases option with
    | none => simp [traitResult, bind, Except.bind] at accepted
    | some trait =>
      simp only [traitResult, bind, Except.bind] at accepted
      cases profileResult : Detail.coercionMethodProfile? context trait with
      | error error => simp [profileResult] at accepted
      | ok profile =>
        simp only [profileResult] at accepted
        have profileSafe : ∀ value ∈ profile, ∀ predicate ∈ value.method.wherePredicates,
            PredicateSafe protectedVars state predicate := by
          intro value member
          have equal : profile = some value := Option.mem_def.mp member
          rw [equal] at profileResult
          exact profile_private catalog profileResult
        cases methodResult : Detail.coercionMethodPredicates profile source target with
        | error error => simp [methodResult] at accepted
        | ok methods =>
          simp only [methodResult] at accepted
          have methodsSafe := methodPredicates_private profileSafe sourceSafe targetSafe methodResult
          let direct : ProgramPredicate := {trait, subject := source, arguments := [target]}
          let directStep : Detail.PlannedCoercionStep := {
            source, target, predicate := direct, methodPredicates := methods
          }
          have directSafe : PlannedStepSafe protectedVars state directStep := by
            refine ⟨sourceSafe, targetSafe, ?_, methodsSafe⟩
            intro type member
            simp only [directStep, direct, List.mem_cons, List.not_mem_nil, or_false] at member
            rcases member with rfl | rfl
            · exact sourceSafe
            · exact targetSafe
          change (match Detail.coercionEvidenceViable context state direct methods with
            | .ok true => Except.ok (some [directStep])
            | .ok false => do
                match ← Detail.searchCoercionPaths context state profile trait source target
                  context.coercionDepth [{current := source, visited := [source], steps := []}] [] with
                | some searched => pure (some searched)
                | none => pure (some [directStep])
            | .error error => Except.error error) = Except.ok (some steps) at accepted
          cases viable : Detail.coercionEvidenceViable context state direct methods with
          | error error => simp [viable] at accepted
          | ok value =>
            cases value with
            | true =>
              simp only [viable, Except.ok.injEq, Option.some.injEq] at accepted
              subst steps
              intro step member
              cases List.mem_singleton.mp member
              exact directSafe
            | false =>
              simp only [viable] at accepted
              cases searched : Detail.searchCoercionPaths context state profile trait source target
                  context.coercionDepth [{current := source, visited := [source], steps := []}] [] with
              | error error => simp [searched, bind, Except.bind] at accepted
              | ok found =>
                cases found with
                | none =>
                  simp only [searched, bind, Except.bind, pure, Pure.pure, Except.pure,
                    Except.ok.injEq, Option.some.injEq] at accepted
                  subst steps
                  intro step member
                  cases List.mem_singleton.mp member
                  exact directSafe
                | some chosen =>
                  simp only [searched, bind, Except.bind, pure, Pure.pure, Except.pure,
                    Except.ok.injEq, Option.some.injEq] at accepted
                  subst steps
                  apply searchPaths_private _ profileSafe _ searched
                  intro path member
                  cases List.mem_singleton.mp member
                  exact ⟨sourceSafe, by simp⟩

end Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceSelectedPrivacyIssuedRequirements
/-! Actual committed coercion rows and expected-type continuations preserve
privacy of every newly generated predicate. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
open Frontend SourceInference TypeSystem

private theorem commit_inference (state : State) (steps : List Detail.PlannedCoercionStep) :
    (Detail.commitCoercionPlan state steps).2.inference = state.inference := by
  induction steps generalizing state with
  | nil => rfl
  | cons step rest ih =>
    simp only [Detail.commitCoercionPlan]
    rw [ih, requirementBatch_inference]
    rfl

/-- A newly committed row is the actual primary predicate or one of the
actual method predicates of a selected step. -/
theorem commitCoercionPlan_requirement_origin (state : State)
    (steps : List Detail.PlannedCoercionStep) {row : Requirement}
    (member : row ∈ (Detail.commitCoercionPlan state steps).2.requirements) :
    row ∈ state.requirements ∨ ∃ step ∈ steps,
      row.predicate = step.predicate ∨ row.predicate ∈ step.methodPredicates := by
  induction steps generalizing state with
  | nil => exact .inl member
  | cons step rest ih =>
    rcases ih _ member with old | fresh
    · rcases requirementBatch_row_origin _ _ old with old | method
      · rcases List.mem_append.mp old with old | primary
        · exact .inl old
        · cases List.mem_singleton.mp primary
          exact .inr ⟨step, List.mem_cons_self, .inl rfl⟩
      · exact .inr ⟨step, List.mem_cons_self, .inr method⟩
    · obtain ⟨origin, originMember, occurrence⟩ := fresh
      exact .inr ⟨origin, List.mem_cons_of_mem _ originMember, occurrence⟩

/-- The final allocation preserves the private predicate derived by search. -/
theorem commitCoercionPlan_new_private {protectedVars : List TypeVarId} {state : State}
    {steps : List Detail.PlannedCoercionStep}
    (stepsSafe : ∀ step ∈ steps, PlannedStepSafe protectedVars state step)
    {row : Requirement}
    (member : row ∈ (Detail.commitCoercionPlan state steps).2.requirements)
    (fresh : row ∉ state.requirements) :
    PredicateSafe protectedVars (Detail.commitCoercionPlan state steps).2 row.predicate := by
  rcases commitCoercionPlan_requirement_origin state steps member with old | new
  · exact (fresh old).elim
  · obtain ⟨step, stepMember, primary | method⟩ := new
    · have safe := (stepsSafe step stepMember).2.2.1
      rw [← primary] at safe
      simpa only [PredicateSafe, Safe, State.resolve, InferState.resolve, commit_inference] using safe
    · have safe := (stepsSafe step stepMember).2.2.2 row.predicate method
      simpa only [PredicateSafe, Safe, State.resolve, InferState.resolve, commit_inference] using safe

/-- Successful expected fitting either issues no rows or commits the actual
private path. The declaration catalog is checked at its genuine origin. -/
theorem withExpected_new_requirements_private
    {protectedVars : List TypeVarId} {context : SourceInference.Context}
    {state : State} {actual : InferredExpression} {expected : Option Ty}
    {result : Detail.ExpectationResult}
    (catalog : SignatureCatalogWellFormed context.signatures)
    (ready : state.InferenceReady)
    (actualSafe : Safe protectedVars state actual.type)
    (expectedSafe : ∀ type ∈ expected, Safe protectedVars state type)
    (accepted : Detail.withExpected context state actual expected = .ok result) :
    ∀ row ∈ result.state.requirements, row ∉ state.requirements →
      PredicateSafe protectedVars result.state row.predicate := by
  cases expected with
  | none =>
    simp only [Detail.withExpected, Except.ok.injEq] at accepted
    cases accepted
    exact fun row member fresh => (fresh member).elim
  | some expected =>
    have expectedSafe := expectedSafe expected (by simp)
    cases unified : state.inference.unify actual.type expected with
    | ok inference =>
      simp only [Detail.withExpected, unified, Except.ok.injEq] at accepted
      cases accepted
      exact fun row member fresh => (fresh member).elim
    | error error =>
      cases error with
      | occursCheck _ _ => simp [Detail.withExpected, unified] at accepted
      | exhausted => simp [Detail.withExpected, unified] at accepted
      | mismatch left right =>
        simp only [Detail.withExpected, unified] at accepted
        cases planned : Detail.coercionPlan? context state
            (state.resolve actual.type) (state.resolve expected) with
        | error error => simp [planned, bind, Except.bind] at accepted
        | ok option =>
          cases option with
          | none => simp [planned, bind, Except.bind] at accepted
          | some plan =>
            simp only [planned, bind, Except.bind] at accepted
            change Except.ok _ = Except.ok result at accepted
            cases Except.ok.inj accepted
            exact fun _ member fresh => commitCoercionPlan_new_private
              (coercionPlan_private catalog (safe_resolved ready actualSafe)
                (safe_resolved ready expectedSafe) planned) member fresh

end Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceSelectedPrivacyReferences
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
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceSelectedPrivacyArguments
/-! Privacy follows the exact argument-fitting trace and its real intermediate
states. Each committed expected-type fit contributes its actual new rows. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
open Frontend SourceInference TypeSystem

theorem new_requirements_trans {protectedVars : List TypeVarId} {before middle after : State}
    (first : ∀ row ∈ middle.requirements, row ∉ before.requirements →
      PredicateSafe protectedVars middle row.predicate)
    (second : ∀ row ∈ after.requirements, row ∉ middle.requirements →
      PredicateSafe protectedVars after row.predicate)
    (transport : SafeTransport protectedVars middle after) :
    ∀ row ∈ after.requirements, row ∉ before.requirements →
      PredicateSafe protectedVars after row.predicate := by
  intro row member fresh
  by_cases old : row ∈ middle.requirements
  · intro type typeMember
    exact transport type (first row old fresh type typeMember)
  · exact second row member old

private theorem candidate_fit {context : SourceInference.Context} {state : State}
    {actual : InferredExpression} {expected : Option Ty} {result : Detail.ExpectationResult}
    (accepted : Detail.candidateWithExpected context state actual expected = .ok (some result)) :
    Detail.withExpected context state actual expected = .ok result := by
  unfold Detail.candidateWithExpected at accepted
  cases fitted : Detail.withExpected context state actual expected with
  | ok value =>
    simp only [fitted, Except.ok.injEq, Option.some.injEq] at accepted
    cases accepted
    rfl
  | error error =>
    cases error <;> simp [fitted] at accepted
    all_goals cases ‹Unification.Error› <;> simp_all

private theorem fitTrace_private {protectedVars : List TypeVarId} {context : SourceInference.Context}
    (catalog : SignatureCatalogWellFormed context.signatures)
    {state : State} {arguments : List InferredExpression} {parameters : List Ty}
    {result : Detail.ArgumentFitResult}
    (trace : Detail.ArgumentFitTrace context state arguments parameters result) :
    state.InferenceReady →
    (∀ argument ∈ arguments, argument.type.VariablesBelow state.inference.next) →
    (∀ parameter ∈ parameters, parameter.VariablesBelow state.inference.next) →
    (∀ argument ∈ arguments, Safe protectedVars state argument.type) →
    (∀ parameter ∈ parameters, Safe protectedVars state parameter) →
    LiveBindersSafe protectedVars state →
    SafeTransport protectedVars state result.state ∧
    LiveBindersSafe protectedVars result.state ∧
    ∀ row ∈ result.state.requirements, row ∉ state.requirements →
      PredicateSafe protectedVars result.state row.predicate := by
  induction trace with
  | nil state =>
    intro _ _ _ _ _ live
    exact ⟨.refl _ _, live, fun _ member fresh => (fresh member).elim⟩
  | @cons state argument arguments parameter parameters fitted tail head rest ih =>
    intro ready argumentsBelow parametersBelow argumentsSafe parametersSafe live
    have accepted := candidate_fit head
    have argumentBelow := argumentsBelow argument (by simp)
    have parameterBelow := parametersBelow parameter (by simp)
    have expectedBelow : ∀ type ∈ some parameter, type.VariablesBelow state.inference.next := by
      intro type member
      cases Option.mem_def.mp member
      exact parameterBelow
    have expectedSafe : ∀ type ∈ some parameter, Safe protectedVars state type := by
      intro type member
      cases Option.mem_def.mp member
      exact parametersSafe parameter (by simp)
    have fitProgress := Detail.withExpected_inferenceProperties ready argumentBelow expectedBelow accepted
    have fitting := withExpected_private ready argumentBelow expectedBelow
      (argumentsSafe argument (by simp)) expectedSafe live accepted
    have issued := withExpected_new_requirements_private catalog ready
      (argumentsSafe argument (by simp)) expectedSafe accepted
    have later := ih fitProgress.2.1
      (fun arg member => (argumentsBelow arg (List.mem_cons_of_mem _ member)).weaken fitProgress.1.next_le)
      (fun param member => (parametersBelow param (List.mem_cons_of_mem _ member)).weaken fitProgress.1.next_le)
      (fun arg member => fitting.1 _ (argumentsSafe arg (List.mem_cons_of_mem _ member)))
      (fun param member => fitting.1 _ (parametersSafe param (List.mem_cons_of_mem _ member)))
      fitting.2.2
    exact ⟨fitting.1.trans later.1, later.2.1,
      new_requirements_trans issued later.2.2 later.1⟩

/-- The accepted executable argument pass supplies the entire ordered trace;
no argument-fitting law is assumed by callers. -/
theorem fitArguments_private {protectedVars : List TypeVarId} {context : SourceInference.Context}
    {state : State} {arguments : List InferredExpression} {parameters : List Ty}
    {result : Detail.ArgumentFitResult}
    (catalog : SignatureCatalogWellFormed context.signatures)
    (ready : state.InferenceReady)
    (argumentsBelow : ∀ argument ∈ arguments, argument.type.VariablesBelow state.inference.next)
    (parametersBelow : ∀ parameter ∈ parameters, parameter.VariablesBelow state.inference.next)
    (argumentsSafe : ∀ argument ∈ arguments, Safe protectedVars state argument.type)
    (parametersSafe : ∀ parameter ∈ parameters, Safe protectedVars state parameter)
    (live : LiveBindersSafe protectedVars state)
    (accepted : Detail.fitArguments context state arguments parameters = .ok (some result)) :
    SafeTransport protectedVars state result.state ∧
    LiveBindersSafe protectedVars result.state ∧
    ∀ row ∈ result.state.requirements, row ∉ state.requirements →
      PredicateSafe protectedVars result.state row.predicate :=
  fitTrace_private catalog (Detail.fitArguments_some_trace accepted) ready
    argumentsBelow parametersBelow argumentsSafe parametersSafe live

end Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceSelectedPrivacyApplications
/-! Indirect application follows both executable branches: fitting an exposed
function or allocating a real result variable and unifying a function type. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
open Frontend SourceInference TypeSystem

private theorem functionParts_eq {type parameter result : Ty}
    (found : Detail.functionParts? type = some (parameter,result)) :
    type = .function parameter result := by
  cases type <;> simp [Detail.functionParts?] at found
  case function left right => rcases found with ⟨rfl,rfl⟩; rfl

private theorem unify_requirements {before after : State} {left right : Ty}
    (accepted : Detail.unify before left right = .ok after) :
    after.requirements = before.requirements := by
  unfold Detail.unify at accepted
  cases unified : before.inference.unify left right with
  | error error => simp [unified, Detail.liftUnification, bind, Except.bind] at accepted
  | ok inference =>
    simp only [unified, Detail.liftUnification, bind, Except.bind, pure, Pure.pure, Except.pure,
      Except.ok.injEq] at accepted
    cases accepted
    rfl

/-- The caller supplies privacy of the actual callee, arguments and optional
expectation. The successful application itself supplies every continuation. -/
theorem applyFunctionType_private {protectedVars : List TypeVarId}
    {context : SourceInference.Context} {call : ExpressionId} {callee : Ty}
    {arguments : List InferredExpression} {expected : Option Ty} {state : State}
    {result : Detail.IndirectApplicationResult}
    (catalog : SignatureCatalogWellFormed context.signatures)
    (ready : state.InferenceReady)
    (bound : ∀ metavariable ∈ protectedVars, metavariable.index < state.inference.next)
    (calleeBelow : callee.VariablesBelow state.inference.next)
    (argumentsBelow : ∀ argument ∈ arguments, argument.type.VariablesBelow state.inference.next)
    (expectedBelow : ∀ type ∈ expected, type.VariablesBelow state.inference.next)
    (calleeSafe : Safe protectedVars state callee)
    (argumentsSafe : ∀ argument ∈ arguments, Safe protectedVars state argument.type)
    (expectedSafe : ∀ type ∈ expected, Safe protectedVars state type)
    (live : LiveBindersSafe protectedVars state)
    (accepted : Detail.applyFunctionType context call callee arguments expected state = .ok result) :
    SafeTransport protectedVars state result.state ∧
    Safe protectedVars result.state result.result.type ∧
    LiveBindersSafe protectedVars result.state ∧
    ∀ row ∈ result.state.requirements, row ∉ state.requirements →
      PredicateSafe protectedVars result.state row.predicate := by
  have argumentsBelow : ∀ type ∈ arguments.map InferredExpression.type,
      type.VariablesBelow state.inference.next := by
    intro type member
    obtain ⟨arg, argMember, rfl⟩ := List.mem_map.mp member
    exact argumentsBelow arg argMember
  have argumentsSafe : ∀ type ∈ arguments.map InferredExpression.type,
      Safe protectedVars state type := by
    intro type member
    obtain ⟨arg, argMember, rfl⟩ := List.mem_map.mp member
    exact argumentsSafe arg argMember
  have productBelow := Ty.variablesBelow_productMany argumentsBelow
  have productSafe := safe_productMany protectedVars state _ argumentsSafe
  rcases Detail.applyFunctionType_success_facts accepted with existing | inferred
  · obtain ⟨parameter, returnType, fittedArgument, fittedResult, parts, argumentFit, resultFit, resultEq⟩ := existing
    subst result
    have partsBelow := Detail.functionParts?_success_variablesBelow
      (ready.solved.variablesBelow_apply calleeBelow) parts
    have partsSafe : Safe protectedVars state parameter ∧ Safe protectedVars state returnType := by
      have safe := safe_resolved ready calleeSafe
      rw [functionParts_eq parts] at safe
      exact (safe_function_iff _ _ _ _).mp safe
    have parameterBelow : ∀ type ∈ some parameter, type.VariablesBelow state.inference.next := by
      intro type member
      cases Option.mem_def.mp member
      exact partsBelow.1
    have parameterSafe : ∀ type ∈ some parameter, Safe protectedVars state type := by
      intro type member
      cases Option.mem_def.mp member
      exact partsSafe.1
    have argumentProgress := Detail.withExpected_inferenceProperties ready productBelow parameterBelow argumentFit
    have argumentPrivacy := withExpected_private ready productBelow parameterBelow productSafe parameterSafe live argumentFit
    have argumentRows := withExpected_new_requirements_private catalog ready productSafe parameterSafe argumentFit
    have resultPrivacy := withExpected_private argumentProgress.2.1
      (partsBelow.2.weaken argumentProgress.1.next_le)
      (fun type member => (expectedBelow type member).weaken argumentProgress.1.next_le)
      (argumentPrivacy.1 _ partsSafe.2)
      (fun type member => argumentPrivacy.1 _ (expectedSafe type member))
      argumentPrivacy.2.2 resultFit
    have resultRows := withExpected_new_requirements_private catalog argumentProgress.2.1
      (argumentPrivacy.1 _ partsSafe.2)
      (fun type member => argumentPrivacy.1 _ (expectedSafe type member)) resultFit
    exact ⟨argumentPrivacy.1.trans resultPrivacy.1, resultPrivacy.2.1,
      resultPrivacy.2.2, new_requirements_trans argumentRows resultRows resultPrivacy.1⟩
  · obtain ⟨returnType, freshState, unifiedState, fittedResult, _, allocated, unified, resultFit, resultEq⟩ := inferred
    subst result
    have freshProgress := State.InferenceProgress.fresh state ready.solved
    have freshReady := State.InferenceReady.fresh ready
    have freshSafe := fresh_type ready bound
    have freshTransport : SafeTransport protectedVars state state.fresh.2 := fresh
    have freshBelow : state.fresh.1.VariablesBelow state.fresh.2.inference.next := by
      change Ty.VariablesBelow (state.inference.next + 1) (.variable ⟨state.inference.next⟩)
      exact (Ty.variablesBelow_variable_iff _ _).mpr (Nat.lt_succ_self _)
    have freshBinders : state.fresh.2.localBinders = state.localBinders := rfl
    have freshRequirements : state.fresh.2.requirements = state.requirements := rfl
    rw [allocated] at freshProgress freshReady freshSafe freshTransport freshBelow freshBinders freshRequirements
    change freshState.requirements = state.requirements at freshRequirements
    have functionBelow := (Ty.variablesBelow_function_iff _ _ _).mpr
      ⟨productBelow.weaken freshProgress.next_le, freshBelow⟩
    have functionSafe := (safe_function_iff protectedVars freshState _ _).mpr
      ⟨freshTransport _ productSafe, freshSafe⟩
    have unifyProgress := Detail.unify_inferenceProgress freshReady.solved
      (calleeBelow.weaken freshProgress.next_le) functionBelow unified
    have unifiedReady := Detail.unify_preserves_inferenceReady freshReady
      (calleeBelow.weaken freshProgress.next_le) functionBelow unified
    have unifyPrivacy := ProtectedVariables.unify (freshTransport _ calleeSafe) functionSafe unified
    have beforeFit := freshTransport.trans unifyPrivacy
    have nextLe := (freshProgress.trans unifyProgress).next_le
    have unifiedLive := (live.transport freshBinders freshTransport).transport
      (congrArg LexicalScope.binders (Detail.unify_preserves_lexicalScope unified)) unifyPrivacy
    have resultPrivacy := withExpected_private unifiedReady
      (freshBelow.weaken unifyProgress.next_le)
      (fun type member => (expectedBelow type member).weaken nextLe)
      (unifyPrivacy _ freshSafe)
      (fun type member => beforeFit _ (expectedSafe type member)) unifiedLive resultFit
    have resultRows := withExpected_new_requirements_private catalog unifiedReady
      (unifyPrivacy _ freshSafe)
      (fun type member => beforeFit _ (expectedSafe type member)) resultFit
    refine ⟨beforeFit.trans resultPrivacy.1, resultPrivacy.2.1, resultPrivacy.2.2, ?_⟩
    intro row member newRow
    apply resultRows row member
    simpa only [unify_requirements unified, freshRequirements] using newRow

end Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceSelectedPrivacyLocalLookup
/-! Actual local lookup privacy uses allocator domain coverage. It does not
require uniqueness of the stored scheme quantifier list. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables.UnrestrictedLocalLookup
open Frontend SourceInference TypeSystem

private theorem instantiated_variable_origin {state : State} (ready : state.InferenceReady)
    (scheme : Scheme) (type : Ty)
    (metavariable : TypeVarId)
    (occurs : metavariable ∈ (state.resolve
      ((scheme.instantiateWithSubstitution state.inference.next).substitution.apply type)).freeVariables) :
    (∃ source, source ∈ type.freeVariables ∧ source ∉ scheme.quantified ∧
      metavariable ∈ (state.resolve (.variable source)).freeVariables) ∨
    (state.inference.next ≤ metavariable.index ∧
      metavariable.index < (scheme.instantiateWithSubstitution state.inference.next).next) := by
  let instantiated := scheme.instantiateWithSubstitution state.inference.next
  change metavariable ∈ (state.inference.substitution.apply
    (instantiated.substitution.apply type)).freeVariables at occurs
  rw [← Substitution.compose_apply] at occurs
  obtain ⟨source, sourceMember, image⟩ := apply_variable_origin _ _ _ occurs
  rw [Substitution.compose_apply] at image
  cases found : instantiated.substitution.lookup? source with
  | none =>
    apply Or.inl
    refine ⟨source, sourceMember, ?_, ?_⟩
    · intro quantified
      exact ((Substitution.lookup?_eq_none_iff_not_mem_domain _ _).mp found)
        (Scheme.instantiateWithSubstitution_substitution_domain_covers scheme state.inference.next quantified)
    · simpa only [State.resolve, InferState.resolve, Substitution.apply, found, Option.getD_none] using image
  | some replacement =>
    obtain ⟨fresh, replacementEq, lower, upper⟩ :=
      Scheme.instantiateWithSubstitution_substitution_range_fresh scheme
        state.inference.next (Substitution.lookup?_eq_some_mem found)
    have same : metavariable = fresh := by
      change metavariable ∈ (state.resolve (instantiated.substitution.apply (.variable source))).freeVariables at image
      rw [Substitution.apply, found, Option.getD_some, replacementEq,
        resolve_fresh_variable ready fresh lower] at image
      simpa only [Ty.freeVariables, List.mem_singleton] using image
    subst metavariable
    exact Or.inr ⟨lower, upper⟩

private theorem safe_instantiated_type {protectedVars : List TypeVarId} {state : State}
    (ready : state.InferenceReady)
    (bound : ∀ metavariable ∈ protectedVars, metavariable.index < state.inference.next)
    (scheme : Scheme) (type : Ty)
    (sourceSafe : ∀ metavariable ∈ type.freeVariables,
      metavariable ∉ scheme.quantified → Safe protectedVars state (.variable metavariable)) :
    Safe protectedVars state
      ((scheme.instantiateWithSubstitution state.inference.next).substitution.apply type) := by
  intro metavariable member protectedMember
  rcases instantiated_variable_origin ready scheme type metavariable member with old | fresh
  · obtain ⟨source, sourceMember, outside, image⟩ := old
    exact sourceSafe source sourceMember outside metavariable image protectedMember
  · exact (Nat.not_lt.mpr fresh.1) (bound metavariable protectedMember)

private theorem instantiated_predicate_safe {protectedVars : List TypeVarId} {state : State}
    (ready : state.InferenceReady)
    (bound : ∀ metavariable ∈ protectedVars, metavariable.index < state.inference.next)
    (scheme : Scheme) (predicate : ProgramPredicate)
    (sourceSafe : ∀ type ∈ predicate.subject :: predicate.arguments,
      ∀ metavariable ∈ type.freeVariables,
        metavariable ∉ scheme.quantified → Safe protectedVars state (.variable metavariable)) :
    PredicateSafe protectedVars (instantiatedState state scheme)
      (Detail.applyPredicate (instantiatedState state scheme)
        (TypedTraitResolution.applySubstitution
          (scheme.instantiateWithSubstitution state.inference.next).substitution predicate)) := by
  have each (type : Ty) (member : type ∈ predicate.subject :: predicate.arguments) :
      Safe protectedVars (instantiatedState state scheme)
        (state.resolve ((scheme.instantiateWithSubstitution state.inference.next).substitution.apply type)) :=
    instantiate_transport _ _ _ _ (safe_resolved ready
      (safe_instantiated_type ready bound scheme type (sourceSafe type member)))
  intro type member
  change type ∈ state.resolve ((scheme.instantiateWithSubstitution state.inference.next).substitution.apply predicate.subject) ::
    (predicate.arguments.map (scheme.instantiateWithSubstitution state.inference.next).substitution.apply).map state.resolve at member
  rcases List.mem_cons.mp member with rfl | argument
  · exact each _ (by simp)
  · obtain ⟨instantiated, instMember, rfl⟩ := List.mem_map.mp argument
    obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp instMember
    exact each original (List.mem_cons.mpr (.inr originalMember))

private theorem local_instantiation_safe {protectedVars : List TypeVarId} {state : State}
    {binder : TypedBinder} (ready : state.InferenceReady)
    (bound : ∀ metavariable ∈ protectedVars, metavariable.index < state.inference.next)
    (safe : BinderSafe protectedVars state binder) :
    SafeTransport protectedVars state (instantiatedState state binder.scheme) ∧
    Safe protectedVars (instantiatedState state binder.scheme)
      ((instantiatedState state binder.scheme).resolve
        (binder.scheme.instantiateWithSubstitution state.inference.next).body) ∧
    ∀ predicate ∈ binder.schemeRequirements.map (fun requirement =>
      Detail.applyPredicate (instantiatedState state binder.scheme)
        (TypedTraitResolution.applySubstitution
          (binder.scheme.instantiateWithSubstitution state.inference.next).substitution requirement.predicate)),
      PredicateSafe protectedVars (instantiatedState state binder.scheme) predicate := by
  refine ⟨instantiate_transport _ _ _, ?_, ?_⟩
  · apply instantiate_transport protectedVars state binder.scheme
    apply safe_resolved ready
    apply safe_instantiated_type ready bound binder.scheme binder.scheme.body
    intro v member outside
    exact safe.body v (List.mem_filter.mpr ⟨member, by simp [outside]⟩)
  · intro predicate member
    obtain ⟨requirement, requirementMember, rfl⟩ := List.mem_map.mp member
    exact instantiated_predicate_safe ready bound binder.scheme requirement.predicate
      (safe.requirements requirement requirementMember)

private theorem lookup_instantiation_safe {protectedVars : List TypeVarId} {state : State}
    {name : String} {binder : TypedBinder} (ready : state.InferenceReady)
    (bound : ∀ metavariable ∈ protectedVars, metavariable.index < state.inference.next)
    (safe : LiveBindersSafe protectedVars state)
    (found : state.lookupBinder? name = some binder) :
    SafeTransport protectedVars state (instantiatedState state binder.scheme) ∧
    Safe protectedVars (instantiatedState state binder.scheme)
      ((instantiatedState state binder.scheme).resolve
        (binder.scheme.instantiateWithSubstitution state.inference.next).body) ∧
    ∀ predicate ∈ binder.schemeRequirements.map (fun requirement =>
      Detail.applyPredicate (instantiatedState state binder.scheme)
        (TypedTraitResolution.applySubstitution
          (binder.scheme.instantiateWithSubstitution state.inference.next).substitution requirement.predicate)),
      PredicateSafe protectedVars (instantiatedState state binder.scheme) predicate :=
  local_instantiation_safe ready bound
    (safe binder (State.lookupBinder?_eq_some_facts found).1)

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
  have privacy := lookup_instantiation_safe readyAllocated boundAllocated liveAllocated found
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

end Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables.UnrestrictedLocalLookup
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceSelectedPrivacyOperators
/-! Operator obligations are private because the checked method catalog is
closed and its actual rigid replacement is the already private operand. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
open Frontend SourceInference TypeSystem

private theorem formed_private {protectedVars : List TypeVarId} {state : State}
    {context : SourceSemantics.Context} {type : Ty} (formed : TypeWellFormed context type) :
    Safe protectedVars state type := by
  apply safe_closed
  intro metavariable occurs
  have closed := StructuralSubstitution.TypeWellFormed.freeVariables_eq_nil formed
  simp [closed] at occurs

/-- The executable operator-profile lookup supplies the actual trait and
method membership used to consult the catalog. -/
theorem operatorTraitPredicates_private {protectedVars : List TypeVarId}
    {context : SourceInference.Context} {state : State} {trait : Resolved.DeclarationId}
    {methodName : String} {operand : Ty} {parameters returns : List Ty}
    {predicates : List ProgramPredicate}
    (catalog : SignatureCatalogWellFormed context.signatures)
    (operandSafe : Safe protectedVars state operand)
    (accepted : Detail.operatorTraitPredicates context trait methodName operand parameters returns =
      .ok predicates) :
    ∀ predicate ∈ predicates, PredicateSafe protectedVars state predicate := by
  cases found : context.signatures.trait? trait with
  | none => simp [Detail.operatorTraitPredicates, Detail.exactOperatorTraitMethod, found,
      bind, Except.bind] at accepted
  | some signature =>
    have signatureMember : signature ∈ context.signatures.traits := List.mem_of_find?_eq_some found
    simp only [Detail.operatorTraitPredicates, Detail.exactOperatorTraitMethod, found,
      pure, Pure.pure, Except.pure, bind, Except.bind] at accepted
    cases methods : signature.methods.filter (fun candidate => candidate.name == methodName) with
    | nil => simp [methods] at accepted
    | cons method rest =>
      cases rest with
      | cons second tail => simp [methods] at accepted
      | nil =>
        simp only [methods] at accepted
        have methodMember : method ∈ signature.methods :=
          (List.mem_filter.mp (show method ∈ signature.methods.filter
            (fun candidate => candidate.name == methodName) by rw [methods]; simp)).1
        split at accepted
        · split at accepted
          · simp only [Except.ok.injEq] at accepted
            subst predicates
            intro predicate member
            rcases List.mem_cons.mp member with rfl | member
            · intro type member
              have same : type = operand := by simpa using member
              exact same ▸ operandSafe
            · obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp member
              have formed := ((catalog.traits_semantic signature signatureMember).methods method methodMember).predicates
                original originalMember
              have range : ∀ parameter replacement, (parameter,replacement) ∈ signature.parameters.zip [operand] →
                  Safe protectedVars state replacement := by
                intro parameter replacement member
                have same : replacement = operand := by simpa using (List.of_mem_zip member).2
                exact same ▸ operandSafe
              intro type member
              rcases List.mem_cons.mp member with rfl | member
              · exact safe_parameterApply range (formed_private formed.subject)
              · obtain ⟨originalType, originalTypeMember, rfl⟩ := List.mem_map.mp member
                exact safe_parameterApply range (formed_private (formed.arguments _ originalTypeMember))
          · simp [throw] at accepted
        · simp [throw] at accepted

private abbrev finishOperator (context : SourceInference.Context) (dispatch : Detail.OperatorDispatch)
    (operand builtin builtinResult resultType : Ty) (parameterTypes : List Ty)
    (hasOpenLiteralOperand : Bool) (state : State) : Except Error Detail.OperatorInferenceResult :=
  if operand = builtin then
    pure {type := builtinResult, requirements := [], state}
  else
    match dispatch with
    | .function name =>
      if Detail.isDeferredBuiltinOperatorTarget state hasOpenLiteralOperand builtin operand ||
          Detail.isStagedIntegerOperatorTarget state hasOpenLiteralOperand builtin operand then
        pure {type := resultType, requirements := [], state}
      else throw (.unknownVariable name)
    | .traitMethod traitName methodName => do
      match ← Detail.operatorTrait? context traitName with
      | some trait =>
        let predicates ← Detail.operatorTraitPredicates context trait methodName operand parameterTypes [resultType]
        let (requirements,state) := state.addRequirementsWithIds predicates
        pure {type := resultType, requirements, state}
      | none =>
        if Detail.isDeferredBuiltinOperatorTarget state hasOpenLiteralOperand builtin operand ||
            Detail.isStagedIntegerOperatorTarget state hasOpenLiteralOperand builtin operand then
          pure {type := resultType, requirements := [], state}
        else throw (.operatorNotSupported traitName operand)

private theorem finishOperator_private {protectedVars : List TypeVarId}
    {context : SourceInference.Context} {dispatch : Detail.OperatorDispatch}
    {operand builtin builtinResult resultType : Ty} {parameterTypes : List Ty}
    {hasOpenLiteralOperand : Bool} {state : State} {result : Detail.OperatorInferenceResult}
    (catalog : SignatureCatalogWellFormed context.signatures)
    (operandSafe : Safe protectedVars state operand)
    (builtinSafe : Safe protectedVars state builtinResult)
    (resultSafe : Safe protectedVars state resultType)
    (live : LiveBindersSafe protectedVars state)
    (accepted : finishOperator context dispatch operand builtin builtinResult resultType
      parameterTypes hasOpenLiteralOperand state = .ok result) :
    SafeTransport protectedVars state result.state ∧
    Safe protectedVars result.state result.type ∧
    LiveBindersSafe protectedVars result.state ∧
    ∀ row ∈ result.state.requirements, row ∉ state.requirements →
      PredicateSafe protectedVars result.state row.predicate := by
  unfold finishOperator at accepted
  split at accepted
  · cases Except.ok.inj accepted
    exact ⟨.refl _ _, builtinSafe, live, fun _ member fresh => (fresh member).elim⟩
  · cases dispatch with
    | function name =>
      simp only at accepted
      split at accepted
      · cases Except.ok.inj accepted
        exact ⟨.refl _ _, resultSafe, live, fun _ member fresh => (fresh member).elim⟩
      · cases accepted
    | traitMethod traitName methodName =>
      cases traitResult : Detail.operatorTrait? context traitName with
      | error error => simp [traitResult, bind, Except.bind] at accepted
      | ok option =>
        cases option with
        | none =>
          simp only [traitResult, bind, Except.bind] at accepted
          split at accepted
          · cases Except.ok.inj accepted
            exact ⟨.refl _ _, resultSafe, live, fun _ member fresh => (fresh member).elim⟩
          · cases accepted
        | some trait =>
          simp only [traitResult, bind, Except.bind] at accepted
          cases predicatesResult : Detail.operatorTraitPredicates context trait methodName operand parameterTypes [resultType] with
          | error error => simp [predicatesResult] at accepted
          | ok predicates =>
            simp only [predicatesResult, pure, Pure.pure, Except.pure, Except.ok.injEq] at accepted
            cases accepted
            have transport : SafeTransport protectedVars state (state.addRequirementsWithIds predicates).2 :=
              .of_substitution_eq (congrArg InferState.substitution (requirementBatch_inference _ _))
            refine ⟨transport, transport _ resultSafe,
              live.transport (requirementBatch_binders _ _) transport, ?_⟩
            intro row member fresh
            rcases requirementBatch_row_origin _ _ member with old | issued
            · exact (fresh old).elim
            · intro type typeMember
              exact transport _ (operatorTraitPredicates_private catalog operandSafe predicatesResult
                row.predicate issued type typeMember)


private abbrev finishUnary (context : SourceInference.Context) (operator : Syntax.UnaryOp)
    (operandType : Ty) (hasOpenLiteralOperand : Bool) (state : State) :=
  let operand := state.resolve operandType
  let builtin := match operator with | .logicalNot => Ty.bool | .bitNot => Ty.word
  finishOperator context (Detail.unaryOperatorDispatch operator) operand builtin builtin
    (if operator == Syntax.UnaryOp.logicalNot then .bool else operand) [operand] hasOpenLiteralOperand state

private abbrev finishBinary (context : SourceInference.Context) (operator : Syntax.BinaryOp)
    (operandType : Ty) (hasOpenLiteralOperand : Bool) (state : State) :
    Except SourceInference.Error Detail.OperatorInferenceResult :=
  let operand := state.resolve operandType
  if Detail.fixedWordOperator operator operand then
    pure {
      type := if Detail.binaryResultIsBool operator then .bool else operand
      requirements := []
      state
    }
  else
    let builtin := Detail.binaryBuiltinType operator
    finishOperator context (Detail.binaryOperatorDispatch operator) operand builtin
      (if Detail.binaryResultIsBool operator then .bool else builtin)
      (if Detail.binaryResultIsBool operator then .bool else operand)
      [operand,operand] hasOpenLiteralOperand state

private theorem bool_private (protectedVars : List TypeVarId) (state : State) :
    Safe protectedVars state Ty.bool := safe_closed _ _ (by simp [Ty.VariablesBelow, Ty.bool, Ty.freeVariables])

private theorem finishUnary_private {protectedVars : List TypeVarId}
    {context : SourceInference.Context} {operator : Syntax.UnaryOp} {operandType : Ty}
    {openLiteral : Bool} {state : State} {result : Detail.OperatorInferenceResult}
    (catalog : SignatureCatalogWellFormed context.signatures)
    (ready : state.InferenceReady) (operandSafe : Safe protectedVars state operandType)
    (live : LiveBindersSafe protectedVars state)
    (accepted : finishUnary context operator operandType openLiteral state = .ok result) :
    SafeTransport protectedVars state result.state ∧ Safe protectedVars result.state result.type ∧
    LiveBindersSafe protectedVars result.state ∧
    ∀ row ∈ result.state.requirements, row ∉ state.requirements →
      PredicateSafe protectedVars result.state row.predicate := by
  have resolvedSafe := safe_resolved ready operandSafe
  apply finishOperator_private catalog resolvedSafe _ _ live accepted
  · cases operator <;> exact safe_closed _ _ (by simp [Ty.VariablesBelow, Ty.bool, Ty.word, Ty.freeVariables])
  · split
    · exact bool_private _ _
    · exact resolvedSafe

private theorem finishBinary_private {protectedVars : List TypeVarId}
    {context : SourceInference.Context} {operator : Syntax.BinaryOp} {operandType : Ty}
    {openLiteral : Bool} {state : State} {result : Detail.OperatorInferenceResult}
    (catalog : SignatureCatalogWellFormed context.signatures)
    (ready : state.InferenceReady) (operandSafe : Safe protectedVars state operandType)
    (live : LiveBindersSafe protectedVars state)
    (accepted : finishBinary context operator operandType openLiteral state = .ok result) :
    SafeTransport protectedVars state result.state ∧ Safe protectedVars result.state result.type ∧
    LiveBindersSafe protectedVars result.state ∧
    ∀ row ∈ result.state.requirements, row ∉ state.requirements →
      PredicateSafe protectedVars result.state row.predicate := by
  have resolvedSafe := safe_resolved ready operandSafe
  have resultSafe : Safe protectedVars state
      (if Detail.binaryResultIsBool operator then .bool else state.resolve operandType) := by
    split
    · exact bool_private _ _
    · exact resolvedSafe
  simp only [finishBinary] at accepted
  split at accepted
  · cases Except.ok.inj accepted
    exact ⟨.refl _ _, resultSafe, live, fun _ member fresh => (fresh member).elim⟩
  apply finishOperator_private catalog resolvedSafe _ resultSafe live accepted
  split
  · exact bool_private _ _
  · cases operator <;> exact safe_closed _ _ (by simp [Detail.binaryBuiltinType, Ty.VariablesBelow, Ty.bool, Ty.word, Ty.freeVariables])

/-- Unary inference protects its operand through the optional real expected
unification and the selected builtin or trait method result. -/
theorem inferUnaryOperator_private {protectedVars : List TypeVarId}
    {context : SourceInference.Context} {operator : Syntax.UnaryOp} {operandType : Ty}
    {expected : Option Ty} {integerLiterals : List IntegerLiteralOrigin}
    {state : State} {result : Detail.OperatorInferenceResult}
    (catalog : SignatureCatalogWellFormed context.signatures) (ready : state.InferenceReady)
    (operandBelow : operandType.VariablesBelow state.inference.next)
    (expectedBelow : ∀ type ∈ expected, type.VariablesBelow state.inference.next)
    (operandSafe : Safe protectedVars state operandType)
    (expectedSafe : ∀ type ∈ expected, Safe protectedVars state type)
    (live : LiveBindersSafe protectedVars state)
    (accepted : Detail.inferUnaryOperator context operator operandType expected integerLiterals state = .ok result) :
    SafeTransport protectedVars state result.state ∧ Safe protectedVars result.state result.type ∧
    LiveBindersSafe protectedVars result.state ∧
    ∀ row ∈ result.state.requirements, row ∉ state.requirements →
      PredicateSafe protectedVars result.state row.predicate := by
  let openLiteral := Detail.isOpenIntegerLiteralTarget state integerLiterals operandType
  unfold Detail.inferUnaryOperator at accepted
  cases expected with
  | none =>
    simp only [bind, Except.bind, pure, Pure.pure, Except.pure] at accepted
    exact finishUnary_private catalog ready operandSafe live accepted
  | some expectedType =>
    have expectedBelow := expectedBelow expectedType (by simp)
    have expectedSafe := expectedSafe expectedType (by simp)
    cases skip : (operator == Syntax.UnaryOp.logicalNot ||
        (state.resolve operandType).freeVariables.isEmpty || !openLiteral) with
    | true =>
      simp only [openLiteral, skip, if_true, bind, Except.bind, pure, Pure.pure, Except.pure] at accepted
      exact finishUnary_private catalog ready operandSafe live accepted
    | false =>
      simp only [openLiteral, skip, Bool.false_eq_true, if_false] at accepted
      cases unified : Detail.unify state (state.resolve operandType) expectedType with
      | error error => simp [unified, bind, Except.bind] at accepted
      | ok fitted =>
        simp only [unified, bind, Except.bind] at accepted
        have fitReady := Detail.unify_preserves_inferenceReady ready
          (ready.solved.variablesBelow_apply operandBelow) expectedBelow unified
        have fitPrivacy := ProtectedVariables.unify (safe_resolved ready operandSafe) expectedSafe unified
        have fitLive := live.unify (safe_resolved ready operandSafe) expectedSafe unified
        have tail := finishUnary_private catalog fitReady (fitPrivacy _ operandSafe) fitLive accepted
        refine ⟨fitPrivacy.trans tail.1, tail.2.1, tail.2.2.1, ?_⟩
        intro row member fresh
        apply tail.2.2.2 row member
        simpa only [unify_requirements unified] using fresh


private theorem prepend_unify {protectedVars : List TypeVarId} {before after : State}
    {left right : Ty} {result : Detail.OperatorInferenceResult}
    (leftSafe : Safe protectedVars before left) (rightSafe : Safe protectedVars before right)
    (unified : Detail.unify before left right = .ok after)
    (tail : SafeTransport protectedVars after result.state ∧ Safe protectedVars result.state result.type ∧
      LiveBindersSafe protectedVars result.state ∧
      ∀ row ∈ result.state.requirements, row ∉ after.requirements →
        PredicateSafe protectedVars result.state row.predicate) :
    SafeTransport protectedVars before result.state ∧ Safe protectedVars result.state result.type ∧
    LiveBindersSafe protectedVars result.state ∧
    ∀ row ∈ result.state.requirements, row ∉ before.requirements →
      PredicateSafe protectedVars result.state row.predicate := by
  refine ⟨(ProtectedVariables.unify leftSafe rightSafe unified).trans tail.1,
    tail.2.1, tail.2.2.1, ?_⟩
  intro row member fresh
  apply tail.2.2.2 row member
  simpa only [unify_requirements unified] using fresh

/-- Binary inference follows both actual unifications before selecting its
builtin result or cataloged method obligations. -/
theorem inferBinaryOperator_private {protectedVars : List TypeVarId}
    {context : SourceInference.Context} {operator : Syntax.BinaryOp} {left right : Ty}
    {expected : Option Ty} {integerLiterals : List IntegerLiteralOrigin}
    {state : State} {result : Detail.OperatorInferenceResult}
    (catalog : SignatureCatalogWellFormed context.signatures) (ready : state.InferenceReady)
    (leftBelow : left.VariablesBelow state.inference.next)
    (rightBelow : right.VariablesBelow state.inference.next)
    (expectedBelow : ∀ type ∈ expected, type.VariablesBelow state.inference.next)
    (leftSafe : Safe protectedVars state left) (rightSafe : Safe protectedVars state right)
    (expectedSafe : ∀ type ∈ expected, Safe protectedVars state type)
    (live : LiveBindersSafe protectedVars state)
    (accepted : Detail.inferBinaryOperator context operator left right expected integerLiterals state = .ok result) :
    SafeTransport protectedVars state result.state ∧ Safe protectedVars result.state result.type ∧
    LiveBindersSafe protectedVars result.state ∧
    ∀ row ∈ result.state.requirements, row ∉ state.requirements →
      PredicateSafe protectedVars result.state row.predicate := by
  let openLiteral := Detail.isOpenIntegerLiteralTarget state integerLiterals left ||
    Detail.isOpenIntegerLiteralTarget state integerLiterals right
  by_cases shift : Detail.isShiftOperator operator = true
  · obtain ⟨_, typeEq, valued, valueResult, amountResult⟩ :=
      Detail.inferBinaryOperator_shift_result shift accepted
    have wordSafe : ∀ any : State, Safe protectedVars any .word := by
      intro any metavariable member
      simp [Frontend.SourceInference.State.resolve, TypeSystem.InferState.resolve, TypeSystem.Ty.word,
        TypeSystem.Ty.freeVariables] at member
    have valuedLive := live.unify leftSafe (wordSafe state) valueResult
    have valuePrivacy := ProtectedVariables.unify leftSafe (wordSafe state) valueResult
    apply prepend_unify leftSafe (wordSafe state) valueResult
    have rightSafeValued := valuePrivacy _ rightSafe
    apply prepend_unify rightSafeValued (wordSafe valued) amountResult
    refine ⟨SafeTransport.refl _ _, by rw [typeEq]; exact wordSafe _,
      valuedLive.unify rightSafeValued (wordSafe valued) amountResult, ?_⟩
    intro row member fresh
    exact absurd member fresh
  by_cases unchecked : Detail.isUncheckedOperator operator = true
  · obtain ⟨unifiedState, prepared, unified, prepare, tailSuccess⟩ :=
      Detail.inferBinaryOperator_unchecked_result unchecked accepted
    have unifiedReady := Detail.unify_preserves_inferenceReady ready leftBelow rightBelow unified
    have unifiedProgress := Detail.unify_inferenceProgress ready.solved leftBelow rightBelow unified
    have unifiedPrivacy := ProtectedVariables.unify leftSafe rightSafe unified
    have operandSafe := unifiedPrivacy _ leftSafe
    have unifiedLive := live.unify leftSafe rightSafe unified
    apply prepend_unify leftSafe rightSafe unified
    rcases prepare with preparedEq | wordResult
    · rw [preparedEq] at tailSuccess
      exact finishBinary_private catalog unifiedReady operandSafe unifiedLive
        (show finishBinary context operator left false unifiedState = .ok result from tailSuccess)
    · have wordSafe : Safe protectedVars unifiedState .word := by
        intro metavariable member
        simp [Frontend.SourceInference.State.resolve, TypeSystem.InferState.resolve, TypeSystem.Ty.word,
          TypeSystem.Ty.freeVariables] at member
      have operandBelow := unifiedReady.solved.variablesBelow_apply
        (leftBelow.weaken unifiedProgress.next_le)
      have preparedReady := Detail.unify_preserves_inferenceReady unifiedReady operandBelow
        (TypeSystem.Ty.variablesBelow_constructor _ _) wordResult
      have resolvedSafe := safe_resolved unifiedReady operandSafe
      have preparedPrivacy := ProtectedVariables.unify resolvedSafe wordSafe wordResult
      have preparedLive := unifiedLive.unify resolvedSafe wordSafe wordResult
      exact prepend_unify resolvedSafe wordSafe wordResult
        (finishBinary_private catalog preparedReady (preparedPrivacy _ operandSafe) preparedLive
          (show finishBinary context operator left false prepared = .ok result from tailSuccess))
  unfold Detail.inferBinaryOperator Detail.binaryOperatorTail at accepted
  rw [if_neg shift, if_neg unchecked] at accepted
  cases unified : Detail.unify state left right with
  | error error => simp [unified, bind, Except.bind] at accepted
  | ok unifiedState =>
    simp only [unified, bind, Except.bind] at accepted
    have unifiedReady := Detail.unify_preserves_inferenceReady ready leftBelow rightBelow unified
    have unifiedProgress := Detail.unify_inferenceProgress ready.solved leftBelow rightBelow unified
    have unifiedPrivacy := ProtectedVariables.unify leftSafe rightSafe unified
    have operandSafe := unifiedPrivacy _ leftSafe
    have unifiedLive := live.unify leftSafe rightSafe unified
    apply prepend_unify leftSafe rightSafe unified
    cases expected with
    | none =>
      simp only [pure, Pure.pure, Except.pure] at accepted
      exact finishBinary_private catalog unifiedReady operandSafe unifiedLive accepted
    | some expectedType =>
      have expectedBelow := (expectedBelow expectedType (by simp)).weaken unifiedProgress.next_le
      have expectedSafe := unifiedPrivacy _ (expectedSafe expectedType (by simp))
      cases skip : (Detail.binaryResultIsBool operator ||
          (unifiedState.resolve left).freeVariables.isEmpty || !openLiteral) with
      | true =>
        simp only [openLiteral, skip, if_true, pure, Pure.pure, Except.pure] at accepted
        exact finishBinary_private catalog unifiedReady operandSafe unifiedLive accepted
      | false =>
        simp only [openLiteral, skip, Bool.false_eq_true, if_false] at accepted
        cases fitted : Detail.unify unifiedState (unifiedState.resolve left) expectedType with
        | error error => simp [fitted] at accepted
        | ok fittedState =>
          simp only [fitted] at accepted
          have operandBelow := unifiedReady.solved.variablesBelow_apply
            (leftBelow.weaken unifiedProgress.next_le)
          have fittedReady := Detail.unify_preserves_inferenceReady unifiedReady operandBelow expectedBelow fitted
          have resolvedSafe := safe_resolved unifiedReady operandSafe
          have fittedPrivacy := ProtectedVariables.unify resolvedSafe expectedSafe fitted
          have fittedLive := unifiedLive.unify resolvedSafe expectedSafe fitted
          exact prepend_unify resolvedSafe expectedSafe fitted
            (finishBinary_private catalog fittedReady (fittedPrivacy _ operandSafe) fittedLive accepted)

end Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
end
