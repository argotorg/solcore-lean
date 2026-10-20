import Solcore.SourceSemantics.SourceInferenceSelectedPrivacyLambdaParameters

/-! Privacy of the actual recursive pattern checker, including fresh numeric
requirements, constructor payloads, and entered pattern binders. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
open Frontend SourceInference TypeSystem

private theorem unify_requirements {state result : State} {left right : Ty}
    (accepted : Detail.unify state left right = .ok result) : result.requirements = state.requirements := by
  unfold Detail.unify at accepted
  cases unified : state.inference.unify left right with
  | error error => simp [unified, Detail.liftUnification, bind, Except.bind] at accepted
  | ok inference =>
    simp only [unified, Detail.liftUnification, bind, Except.bind, pure, Pure.pure, Except.pure] at accepted
    cases accepted
    rfl

private theorem freshTypes_fields (count : Nat) (state : State) :
    (Detail.freshTypes count state).2.localBinders = state.localBinders ∧
      (Detail.freshTypes count state).2.requirements = state.requirements := by
  induction count generalizing state with
  | zero => exact ⟨rfl, rfl⟩
  | succ count ih => exact ih state.fresh.2

private theorem freshConstructor_requirements (dataType : ProgramDataSignature)
    (constructor : ProgramDataConstructorSignature) (state : State) :
    (Detail.freshDataConstructorInstantiation dataType constructor state).2.requirements = state.requirements := by
  have fold (parameters : List TypeParameterId) (accumulator : List Ty × State) :
      (parameters.foldl (fun result _ =>
        (result.1 ++ [result.2.fresh.1], result.2.fresh.2)) accumulator).2.requirements =
        accumulator.2.requirements := by
    induction parameters generalizing accumulator with
    | nil => rfl
    | cons parameter rest ih => exact ih (accumulator.1 ++ [accumulator.2.fresh.1], accumulator.2.fresh.2)
  exact fold dataType.parameters ([],state)

private def PatternPrivacy (protectedVars : List TypeVarId) (initial final : State) : Prop :=
  SafeTransport protectedVars initial final ∧ LiveBindersSafe protectedVars final ∧
    ∀ row ∈ final.requirements, row ∉ initial.requirements → PredicateSafe protectedVars final row.predicate

private theorem PatternPrivacy.trans {protectedVars : List TypeVarId} {first second third : State}
    (left : PatternPrivacy protectedVars first second) (right : PatternPrivacy protectedVars second third) :
    PatternPrivacy protectedVars first third :=
  ⟨left.1.trans right.1, right.2.1, new_requirements_trans left.2.2 right.2.2 right.1⟩

private theorem PatternPrivacy.of_unchanged {protectedVars : List TypeVarId} {initial final : State}
    (transport : SafeTransport protectedVars initial final) (live : LiveBindersSafe protectedVars final)
    (requirements : final.requirements = initial.requirements) : PatternPrivacy protectedVars initial final := by
  refine ⟨transport, live, ?_⟩
  intro row member fresh
  exact False.elim (fresh (requirements ▸ member))

private theorem integer_prefix_private {protectedVars : List TypeVarId} {state recorded final : State}
    {expected : Ty} {metavariable : TypeVarId} {normalized : Ty} {requirement : RequirementId}
    (ready : state.InferenceReady)
    (bound : ∀ protectedVariable ∈ protectedVars, protectedVariable.index < state.inference.next)
    (expectedSafe : Safe protectedVars state expected) (live : LiveBindersSafe protectedVars state)
    (freshType : state.fresh.1 = .variable metavariable)
    (unified : Detail.unify recorded (.variable metavariable) normalized = .ok final)
    (normalization : recorded.resolve expected = normalized)
    (inference : recorded.inference = state.fresh.2.inference)
    (binders : recorded.localBinders = state.localBinders)
    (requirements : recorded.requirements = state.requirements ++
      [{id := requirement, predicate := ProgramSignatures.builtinIntPredicate (.variable metavariable)}]) :
    PatternPrivacy protectedVars state final := by
  have stage : SafeTransport protectedVars state.fresh.2 recorded :=
    .of_substitution_eq (congrArg InferState.substitution inference)
  have initialStage : SafeTransport protectedVars state recorded := fresh.trans stage
  have targetSafe : Safe protectedVars recorded (.variable metavariable) :=
    freshType ▸ stage _ (fresh_type ready bound)
  have recordedReady : recorded.InferenceReady := by
    apply State.InferenceReady.of_progress_of_binderEnvironment_eq ready.fresh
      (State.InferenceProgress.of_inference_eq ready.fresh.solved inference)
    simp only [State.binderEnvironment, binders]
    rfl
  have normalizedSafe : Safe protectedVars recorded normalized :=
    normalization ▸ safe_resolved recordedReady (initialStage _ expectedSafe)
  have transport := ProtectedVariables.unify targetSafe normalizedSafe unified
  refine ⟨initialStage.trans transport,
    (live.transport binders initialStage).unify targetSafe normalizedSafe unified, ?_⟩
  intro row member fresh
  rw [unify_requirements unified, requirements] at member
  rcases List.mem_append.mp member with old | issued
  · exact False.elim (fresh old)
  · have same := List.mem_singleton.mp issued
    subst row
    intro type member
    have typeEq : type = .variable metavariable := by
      simpa [ProgramSignatures.builtinIntPredicate] using member
    subst type
    exact transport _ targetSafe

private theorem contextual_prefix_private {protectedVars : List TypeVarId}
    {context : SourceInference.Context} {state final : State} {expected : Ty} {name : String}
    {dataType : ProgramDataSignature} {constructor : ProgramDataConstructorSignature} {arguments : List Ty}
    (ready : state.InferenceReady) (expectedBelow : expected.VariablesBelow state.inference.next)
    (formation : ProgramSignatureFormationValidated context.signatures)
    (safe : Safe protectedVars state expected) (live : LiveBindersSafe protectedVars state)
    (selected : Detail.contextualConstructorCandidate context state (some expected) name = .ok (dataType,constructor,arguments))
    (unified : Detail.unify state (Detail.instantiateDataConstructor dataType constructor arguments).resultType expected = .ok final) :
    PatternPrivacy protectedVars state final ∧ state.InferenceProgress final ∧ final.InferenceReady ∧
      (∀ type ∈ (Detail.instantiateDataConstructor dataType constructor arguments).payloadTypes,
        type.VariablesBelow final.inference.next ∧ Safe protectedVars final type) := by
  have privacy := contextual_constructor ready formation safe selected
  obtain ⟨dataMember, constructorMember, actual, expectedEq, nominalEq⟩ :=
    Detail.contextualConstructorCandidate_success_facts selected
  cases Option.some.inj expectedEq
  have resolvedBelow : (state.resolve expected).VariablesBelow state.inference.next :=
    ready.solved.variablesBelow_apply expectedBelow
  rw [nominalEq] at resolvedBelow
  have argumentsBelow := ((Ty.variablesBelow_applyMany_iff state.inference.next
    (.constructor (.declaration dataType.id)) arguments).mp
      (by simpa only [Ty.nominal] using resolvedBelow)).2
  have bounds := Detail.instantiateDataConstructor_types_variablesBelow (dataType := dataType) argumentsBelow
    (formation.data_constructor_payloadTypes_variablesBelow dataMember constructorMember state.inference.next)
  have progress := Detail.unify_inferenceProgress ready.solved bounds.2 expectedBelow unified
  have finalReady := Detail.unify_preserves_inferenceReady ready bounds.2 expectedBelow unified
  have transport := ProtectedVariables.unify privacy.2 safe unified
  exact ⟨PatternPrivacy.of_unchanged transport (live.unify privacy.2 safe unified) (unify_requirements unified),
    progress, finalReady, fun type member => ⟨(bounds.1 type member).weaken progress.next_le, transport _ (privacy.1 type member)⟩⟩

private theorem explicit_prefix_private {protectedVars : List TypeVarId}
    {context : SourceInference.Context} {state allocated final : State} {expected : Ty}
    {qualifiers : List String} {name : String} {dataType : ProgramDataSignature}
    {constructor : ProgramDataConstructorSignature} {instantiation : DataConstructorInstantiation}
    (ready : state.InferenceReady) (expectedBelow : expected.VariablesBelow state.inference.next)
    (formation : ProgramSignatureFormationValidated context.signatures)
    (bound : ∀ protectedVariable ∈ protectedVars, protectedVariable.index < state.inference.next)
    (safe : Safe protectedVars state expected) (live : LiveBindersSafe protectedVars state)
    (selected : Detail.explicitConstructorCandidate context qualifiers name = .ok (dataType,constructor))
    (allocation : Detail.freshDataConstructorInstantiation dataType constructor state = (instantiation,allocated))
    (unified : Detail.unify allocated instantiation.resultType expected = .ok final) :
    PatternPrivacy protectedVars state final ∧ state.InferenceProgress final ∧ final.InferenceReady ∧
      (∀ type ∈ instantiation.payloadTypes, type.VariablesBelow final.inference.next ∧ Safe protectedVars final type) := by
  obtain ⟨dataMember, constructorMember, _⟩ := Detail.explicitConstructorCandidate_success_facts selected
  have payloadClosed := formation.data_constructor_payloadTypes_variablesBelow dataMember constructorMember 0
  have privacy := fresh_constructor (dataType := dataType) ready bound payloadClosed
  have properties := Detail.freshDataConstructorInstantiation_inferenceProperties dataType constructor state ready
    (fun type member => (payloadClosed type member).weaken (Nat.zero_le _))
  have lexical := Detail.freshDataConstructorInstantiation_preserves_lexicalScope dataType constructor state
  have requirements := freshConstructor_requirements dataType constructor state
  rw [allocation] at privacy properties lexical requirements
  have allocatedBinders := congrArg LexicalScope.binders lexical
  have expectedBound := expectedBelow.weaken properties.1.next_le
  have expectedSafe := privacy.1 _ safe
  have transport := ProtectedVariables.unify privacy.2.2 expectedSafe unified
  have progress := Detail.unify_inferenceProgress properties.2.1.solved properties.2.2.2.2 expectedBound unified
  have finalReady := Detail.unify_preserves_inferenceReady properties.2.1 properties.2.2.2.2 expectedBound unified
  have finalLive := (live.transport allocatedBinders privacy.1).unify privacy.2.2 expectedSafe unified
  exact ⟨PatternPrivacy.of_unchanged (privacy.1.trans transport) finalLive ((unify_requirements unified).trans requirements),
    properties.1.trans progress, finalReady, fun type member => ⟨(properties.2.2.2.1 type member).weaken progress.next_le,
      transport _ (privacy.2.1 type member)⟩⟩

private theorem tuple_prefix_private {protectedVars : List TypeVarId} {state allocated final : State}
    {expected : Ty} {types : List Ty} {count : Nat}
    (ready : state.InferenceReady) (expectedBelow : expected.VariablesBelow state.inference.next)
    (bound : ∀ protectedVariable ∈ protectedVars, protectedVariable.index < state.inference.next)
    (safe : Safe protectedVars state expected) (live : LiveBindersSafe protectedVars state)
    (allocation : Detail.freshTypes count state = (types,allocated))
    (unified : Detail.unify allocated expected (Ty.productMany types) = .ok final) :
    PatternPrivacy protectedVars state final ∧ state.InferenceProgress final ∧ final.InferenceReady ∧
      (∀ type ∈ types, type.VariablesBelow final.inference.next ∧ Safe protectedVars final type) := by
  have privacy := freshTypes count ready bound
  have properties := Detail.freshTypes_inferenceProperties count state ready
  have fields := freshTypes_fields count state
  rw [allocation] at privacy properties fields
  have expectedSafe := privacy.1 _ safe
  have argumentsSafe := safe_productMany protectedVars allocated types privacy.2
  have expectedBound := expectedBelow.weaken properties.1.next_le
  have productBound := Ty.variablesBelow_productMany properties.2.2
  have progress := Detail.unify_inferenceProgress properties.2.1.solved expectedBound productBound unified
  have finalReady := Detail.unify_preserves_inferenceReady properties.2.1 expectedBound productBound unified
  have transport := ProtectedVariables.unify expectedSafe argumentsSafe unified
  have finalLive := (live.transport fields.1 privacy.1).unify expectedSafe argumentsSafe unified
  exact ⟨PatternPrivacy.of_unchanged (privacy.1.trans transport) finalLive ((unify_requirements unified).trans fields.2),
    properties.1.trans progress, finalReady, fun type member => ⟨(properties.2.2 type member).weaken progress.next_le, transport _ (privacy.2 type member)⟩⟩


private def PatternCallPrivacy (protectedVars : List TypeVarId) (fuel : Nat)
    (context : SourceInference.Context) (pattern : Syntax.Pattern) (expected : Ty)
    (seen : List String) (state : State) : Prop :=
  ∀ result, state.InferenceReady → expected.VariablesBelow state.inference.next →
    ProgramSignatureFormationValidated context.signatures →
    (∀ metavariable ∈ protectedVars, metavariable.index < state.inference.next) →
    Safe protectedVars state expected → LiveBindersSafe protectedVars state →
    Detail.inferMatchPatternFlatFuel fuel context pattern expected seen state = .ok result →
    PatternPrivacy protectedVars state result.state

private def PatternsCallPrivacy (protectedVars : List TypeVarId) (fuel : Nat)
    (context : SourceInference.Context) (patterns : List Syntax.Pattern) (expected : List Ty)
    (seen : List String) (state : State) : Prop :=
  ∀ result, state.InferenceReady →
    (∀ type ∈ expected, type.VariablesBelow state.inference.next) →
    ProgramSignatureFormationValidated context.signatures →
    (∀ metavariable ∈ protectedVars, metavariable.index < state.inference.next) →
    (∀ type ∈ expected, Safe protectedVars state type) → LiveBindersSafe protectedVars state →
    Detail.inferMatchPatternsFlatFuel fuel context patterns expected seen state = .ok result →
    PatternPrivacy protectedVars state result.state

set_option maxHeartbeats 2000000 in
private theorem pattern_call_private (protectedVars : List TypeVarId) (fuel : Nat)
    (context : SourceInference.Context) (pattern : Syntax.Pattern) (expected : Ty)
    (seen : List String) (state : State) :
    PatternCallPrivacy protectedVars fuel context pattern expected seen state := by
  apply Detail.inferMatchPatternFlatFuel.induct context
    (motive1 := fun fuel pattern expected seen state =>
      PatternCallPrivacy protectedVars fuel context pattern expected seen state)
    (motive2 := fun fuel patterns expected seen state =>
      PatternsCallPrivacy protectedVars fuel context patterns expected seen state)
  case case3 =>
    intros
    unfold PatternCallPrivacy at *
    intro result ready expectedBelow formation bound expectedSafe live success
    unfold Detail.inferMatchPatternFlatFuel at success
    simp_all [bind, Except.bind]
    repeat' first | split at success
    all_goals try cases success
    all_goals simp_all [pure, Pure.pure, Except.pure]
    all_goals
      rename_i unified
      exact integer_prefix_private ready bound expectedSafe live (by assumption) unified
        (by assumption) rfl rfl rfl
  case case5 =>
    intros
    unfold PatternCallPrivacy at *
    intro result ready expectedBelow formation bound expectedSafe live success
    unfold Detail.inferMatchPatternFlatFuel at success
    simp_all [bind, Except.bind]
    repeat' first | split at success
    all_goals try cases success
    all_goals simp_all [pure, Pure.pure, Except.pure]
    all_goals
      rename_i unified
      exact integer_prefix_private ready bound expectedSafe live (by assumption) unified
        (by assumption) rfl rfl rfl
  case case10 =>
    intros sourcePattern sourceExpected sourceSeen inputState sourceFuel
      leadingDot qualifiers constructorName sourceArguments patternEq branchEq
      flatArguments contextualBranch childrenIH
    unfold PatternCallPrivacy at *
    intro result ready expectedBelow formation bound expectedSafe live success
    unfold Detail.inferMatchPatternFlatFuel at success
    simp_all [bind, Except.bind]
    repeat' first | split at success
    all_goals try cases success
    all_goals simp_all [pure, Pure.pure, Except.pure]
    all_goals try subst_vars
    all_goals first
      | have beforeChildren := contextual_prefix_private ready expectedBelow formation expectedSafe live
          (by assumption) (by assumption)
        have child := childrenIH _ _ _ beforeChildren.2.2.1
          (fun type member => (beforeChildren.2.2.2 type member).1) formation
          (fun metavariable member => Nat.lt_of_lt_of_le (bound metavariable member) beforeChildren.2.1.next_le)
          (fun type member => (beforeChildren.2.2.2 type member).2) beforeChildren.1.2.1 (by assumption)
        exact beforeChildren.1.trans child
      | have beforeChildren := explicit_prefix_private ready expectedBelow formation bound expectedSafe live
          (by assumption) rfl (by assumption)
        have child := childrenIH _ _ _ beforeChildren.2.2.1
          (fun type member => (beforeChildren.2.2.2 type member).1) formation
          (fun metavariable member => Nat.lt_of_lt_of_le (bound metavariable member) beforeChildren.2.1.next_le)
          (fun type member => (beforeChildren.2.2.2 type member).2) beforeChildren.1.2.1 (by assumption)
        exact beforeChildren.1.trans child
  case case11 =>
    intros sourcePattern sourceExpected sourceSeen inputState sourceFuel
      leadingDot qualifiers constructorName sourceArguments patternEq branchEq
      flatArguments explicitBranch childrenIH
    unfold PatternCallPrivacy at *
    intro result ready expectedBelow formation bound expectedSafe live success
    unfold Detail.inferMatchPatternFlatFuel at success
    simp_all [bind, Except.bind]
    repeat' first | split at success
    all_goals try cases success
    all_goals simp_all [pure, Pure.pure, Except.pure]
    all_goals try subst_vars
    all_goals first
      | have beforeChildren := contextual_prefix_private ready expectedBelow formation expectedSafe live
          (by assumption) (by assumption)
        have child := childrenIH _ _ _ beforeChildren.2.2.1
          (fun type member => (beforeChildren.2.2.2 type member).1) formation
          (fun metavariable member => Nat.lt_of_lt_of_le (bound metavariable member) beforeChildren.2.1.next_le)
          (fun type member => (beforeChildren.2.2.2 type member).2) beforeChildren.1.2.1 (by assumption)
        exact beforeChildren.1.trans child
      | have beforeChildren := explicit_prefix_private ready expectedBelow formation bound expectedSafe live
          (by assumption) rfl (by assumption)
        have child := childrenIH _ _ _ beforeChildren.2.2.1
          (fun type member => (beforeChildren.2.2.2 type member).1) formation
          (fun metavariable member => Nat.lt_of_lt_of_le (bound metavariable member) beforeChildren.2.1.next_le)
          (fun type member => (beforeChildren.2.2.2 type member).2) beforeChildren.1.2.1 (by assumption)
        exact beforeChildren.1.trans child
  case case13 =>
    intros sourcePattern sourceExpected sourceSeen inputState sourceFuel
      elements patternEq sources argumentTypes allocatedState freshEq childrenIH
    unfold PatternCallPrivacy at *
    intro result ready expectedBelow formation bound expectedSafe live success
    unfold Detail.inferMatchPatternFlatFuel at success
    simp_all [bind, Except.bind]
    repeat' first | split at success
    all_goals try cases success
    all_goals simp_all
    have argumentTypesEq : (Detail.freshTypes sources.length inputState).1 = argumentTypes :=
      congrArg Prod.fst freshEq
    have allocatedStateEq : (Detail.freshTypes sources.length inputState).2 = allocatedState :=
      congrArg Prod.snd freshEq
    have beforeChildren := tuple_prefix_private (count := sources.length) (types := argumentTypes)
      (allocated := allocatedState) ready expectedBelow bound expectedSafe live freshEq (by
        rw [← allocatedStateEq, ← argumentTypesEq]
        simpa only [sources] using (by assumption))
    have child := childrenIH _ _ beforeChildren.2.2.1
      (fun type member => (beforeChildren.2.2.2 type member).1) formation
      (fun metavariable member => Nat.lt_of_lt_of_le (bound metavariable member) beforeChildren.2.1.next_le)
      (fun type member => (beforeChildren.2.2.2 type member).2) beforeChildren.1.2.1 (by
        rw [← argumentTypesEq]
        simpa only [sources] using (by assumption))
    exact beforeChildren.1.trans child
  case case17 =>
    intros fuel head rest expectedHead expectedTail seen state ihHead ihTail
    unfold PatternsCallPrivacy
    unfold PatternCallPrivacy at ihHead
    unfold PatternsCallPrivacy at ihTail
    intro result ready expectedBelow formation bound expectedSafe live success
    simp only [Detail.inferMatchPatternsFlatFuel] at success
    cases headRun : Detail.inferMatchPatternFlatFuel fuel context head expectedHead seen state with
    | error error => simp [headRun, bind, Except.bind] at success
    | ok inferredHead =>
      simp only [headRun, bind, Except.bind] at success
      cases tailRun : Detail.inferMatchPatternsFlatFuel fuel context rest expectedTail inferredHead.names inferredHead.state with
      | error error => simp [tailRun] at success
      | ok inferredTail =>
        simp only [tailRun] at success
        injection success with resultEq
        subst result
        have headPrivacy := ihHead inferredHead ready (expectedBelow _ List.mem_cons_self) formation
          bound (expectedSafe _ List.mem_cons_self) live headRun
        have headProperties := Detail.inferMatchPatternFlatFuel_inferenceProperties ready
          (expectedBelow _ List.mem_cons_self) formation headRun
        have tailPrivacy := ihTail inferredHead inferredTail headProperties.2
          (fun type member => (expectedBelow type (List.mem_cons_of_mem _ member)).weaken headProperties.1.next_le)
          formation (fun metavariable member => Nat.lt_of_lt_of_le (bound metavariable member) headProperties.1.next_le)
          (fun type member => headPrivacy.1 _ (expectedSafe type (List.mem_cons_of_mem _ member)))
          headPrivacy.2.1 tailRun
        exact headPrivacy.trans tailPrivacy
  all_goals
    intros
    first | unfold PatternCallPrivacy at * | unfold PatternsCallPrivacy at *
    intro result ready expectedBelow formation bound expectedSafe live success
    first | unfold Detail.inferMatchPatternFlatFuel at success | unfold Detail.inferMatchPatternsFlatFuel at success
    simp_all [bind, Except.bind]
    repeat' first | split at success
    all_goals try cases success
    all_goals try simp_all
    all_goals try exact PatternPrivacy.of_unchanged (.refl _ _) live rfl
    all_goals try exact (by simpa only using ih1 _ ready expectedBelow formation bound expectedSafe live (by assumption))
    all_goals
      try
        exact PatternPrivacy.of_unchanged (.of_substitution_eq rfl)
          (allocate_mono_private _ _ _ (safe_resolved ready expectedSafe) live) rfl

/-- The actual recursive flat pattern computation transports private live
variables, including every requirement row newly issued by nested children. -/
theorem inferMatchPatternFlatFuel_private
    {protectedVars : List TypeVarId} {fuel : Nat} {context : SourceInference.Context}
    {pattern : Syntax.Pattern} {expected : Ty} {seen : List String} {state : State}
    {result : Detail.InferredPattern}
    (ready : state.InferenceReady) (expectedBelow : expected.VariablesBelow state.inference.next)
    (formation : ProgramSignatureFormationValidated context.signatures)
    (bound : ∀ metavariable ∈ protectedVars, metavariable.index < state.inference.next)
    (expectedSafe : Safe protectedVars state expected) (live : LiveBindersSafe protectedVars state)
    (accepted : Detail.inferMatchPatternFlatFuel fuel context pattern expected seen state = .ok result) :
    SafeTransport protectedVars state result.state ∧ LiveBindersSafe protectedVars result.state ∧
      ∀ row ∈ result.state.requirements, row ∉ state.requirements → PredicateSafe protectedVars result.state row.predicate :=
  pattern_call_private protectedVars fuel context pattern expected seen state result
    ready expectedBelow formation bound expectedSafe live accepted

/-- Public pattern checking keeps the exact continuation state returned by
its recursive pattern computation. -/
theorem inferMatchPatternFuel_private
    {protectedVars : List TypeVarId} {fuel : Nat} {context : SourceInference.Context}
    {pattern : Syntax.Pattern} {expected : Ty} {state : State}
    {result : TypedMatchPattern × State}
    (ready : state.InferenceReady) (expectedBelow : expected.VariablesBelow state.inference.next)
    (formation : ProgramSignatureFormationValidated context.signatures)
    (bound : ∀ metavariable ∈ protectedVars, metavariable.index < state.inference.next)
    (expectedSafe : Safe protectedVars state expected) (live : LiveBindersSafe protectedVars state)
    (accepted : Detail.inferMatchPatternFuel fuel context pattern expected state = .ok result) :
    SafeTransport protectedVars state result.2 ∧ LiveBindersSafe protectedVars result.2 ∧
      ∀ row ∈ result.2.requirements, row ∉ state.requirements → PredicateSafe protectedVars result.2 row.predicate := by
  unfold Detail.inferMatchPatternFuel at accepted
  cases actual : Detail.inferMatchPatternFlatFuel fuel context pattern expected [] state with
  | error error => simp [actual, bind, Except.bind] at accepted
  | ok inferred =>
    simp only [actual, bind, Except.bind, pure, Pure.pure, Except.pure, Except.ok.injEq] at accepted
    cases accepted
    exact inferMatchPatternFlatFuel_private ready expectedBelow formation bound expectedSafe live actual

end Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
