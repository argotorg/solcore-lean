import Solcore.SourceSemantics.Internal.Formation.NormalizedDeclarations

/-!
# Normalized patterns and matches

Formation through nested patterns, match arms and index expressions.
-/

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceNormalizedPatternPrefixes
/-! Actual pattern prefixes retain structural formation and expose the real
child types. Constructor payloads follow the accepted result unification. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceNormalizedCoercionFormation
open Frontend SourceInference TypeSystem SourceInferenceRequirementFormation SourceInferenceSoundness

private theorem unify_fields {state result : State} {left right : Ty}
    (accepted : Detail.unify state left right = .ok result) :
    result.localBinders = state.localBinders ∧ result.requirements = state.requirements := by
  unfold Detail.unify at accepted
  cases unified : state.inference.unify left right with
  | error error => simp [unified, Detail.liftUnification, bind, Except.bind] at accepted
  | ok inference =>
    simp only [unified, Detail.liftUnification, bind, Except.bind, pure, Pure.pure, Except.pure] at accepted
    cases accepted
    exact ⟨rfl,rfl⟩

private theorem freshTypes_fields (count : Nat) (state : State) :
    (Detail.freshTypes count state).2.localBinders = state.localBinders ∧
      (Detail.freshTypes count state).2.requirements = state.requirements := by
  induction count generalizing state with
  | zero => exact ⟨rfl,rfl⟩
  | succ count ih => exact ih state.fresh.2

private theorem freshTypes_variables (count : Nat) (state : State) :
    ∀ type ∈ (Detail.freshTypes count state).1, ∃ metavariable, type = .variable metavariable := by
  induction count generalizing state with
  | zero => simp [Detail.freshTypes]
  | succ count ih =>
    intro type member
    change type ∈ state.fresh.1 :: (Detail.freshTypes count state.fresh.2).1 at member
    rcases List.mem_cons.mp member with rfl | tail
    · exact ⟨⟨state.inference.next⟩,rfl⟩
    · exact ih state.fresh.2 type tail

private theorem freshConstructor_requirements (dataType : ProgramDataSignature)
    (constructor : ProgramDataConstructorSignature) (state : State) :
    (Detail.freshDataConstructorInstantiation dataType constructor state).2.requirements = state.requirements := by
  have fold (parameters : List TypeParameterId) (accumulator : List Ty × State) :
      (parameters.foldl (fun result _ =>
        (result.1 ++ [result.2.fresh.1],result.2.fresh.2)) accumulator).2.requirements =
        accumulator.2.requirements := by
    induction parameters generalizing accumulator with
    | nil => rfl
    | cons parameter rest ih => exact ih (accumulator.1 ++ [accumulator.2.fresh.1],accumulator.2.fresh.2)
  exact fold dataType.parameters ([],state)

private theorem matched_formation
    {semantic : SourceSemantics.Context} {outer : Substitution}
    {before after : State} {left right : Ty}
    (formed : TypeAdmissible semantic (outer.apply right))
    (continuation : outer.SemanticallyExtends after.inference.substitution)
    (unified : Detail.unify before left right = .ok after) :
    TypeAdmissible semantic (outer.apply left) := by
  have eq := congrArg outer.apply (Detail.unify_resolve_eq unified)
  change outer.apply (after.inference.substitution.apply left) =
    outer.apply (after.inference.substitution.apply right) at eq
  rw [continuation left,continuation right] at eq
  exact eq.symm ▸ formed

private theorem contextual_payload_formation
    {semantic : SourceSemantics.Context} {outer : Substitution}
    {context : SourceInference.Context} {dataType : ProgramDataSignature}
    {constructor : ProgramDataConstructorSignature} {arguments : List Ty}
    (formation : InferenceFormationContext semantic context outer)
    (dataMember : dataType ∈ context.signatures.dataTypes)
    (constructorMember : constructor ∈ dataType.constructors)
    (resultFormed : TypeAdmissible semantic
      (outer.apply (Detail.instantiateDataConstructor dataType constructor arguments).resultType)) :
    ∀ type ∈ (Detail.instantiateDataConstructor dataType constructor arguments).payloadTypes,
      TypeAdmissible semantic (outer.apply type) := by
  have valid := SourceSemantics.DataConstructorInstantiation.Admissible.instantiateDataConstructor_applySubstitution
    formation.catalog (formation.signatures.symm ▸ dataMember) constructorMember outer resultFormed
  intro type member
  apply SourceSemantics.DataConstructorInstantiation.Admissible.payload_type_admissible
    formation.catalog formation.scope.binders valid
  exact List.mem_map.mpr ⟨type,member,rfl⟩

structure PatternPrefixFormation (semantic : SourceSemantics.Context) (outer : Substitution)
    (initial final : State) (types : List Ty) : Prop where
  progress : initial.InferenceProgress final
  ready : final.InferenceReady
  below : ∀ type ∈ types, type.VariablesBelow final.inference.next
  formed : outer.SemanticallyExtends final.inference.substitution →
    NormalizedStateFormation semantic outer final ∧
      ∀ type ∈ types, TypeAdmissible semantic (outer.apply type)

theorem contextual_pattern_prefix_formation
    {semantic : SourceSemantics.Context} {outer : Substitution}
    {context : SourceInference.Context} {state final : State} {expected : Ty} {name : String}
    {dataType : ProgramDataSignature} {constructor : ProgramDataConstructorSignature} {arguments : List Ty}
    (ready : state.InferenceReady) (expectedBelow : expected.VariablesBelow state.inference.next)
    (formation : InferenceFormationContext semantic context outer)
    (stateFormed : NormalizedStateFormation semantic outer state)
    (expectedFormed : TypeAdmissible semantic (outer.apply expected))
    (selected : Detail.contextualConstructorCandidate context state (some expected) name = .ok (dataType,constructor,arguments))
    (unified : Detail.unify state (Detail.instantiateDataConstructor dataType constructor arguments).resultType expected = .ok final) :
    PatternPrefixFormation semantic outer state final
      (Detail.instantiateDataConstructor dataType constructor arguments).payloadTypes := by
  obtain ⟨dataMember,constructorMember,actual,expectedEq,nominalEq⟩ :=
    Detail.contextualConstructorCandidate_success_facts selected
  cases Option.some.inj expectedEq
  have resolvedBelow := ready.solved.variablesBelow_apply expectedBelow
  change (state.resolve expected).VariablesBelow state.inference.next at resolvedBelow
  rw [nominalEq] at resolvedBelow
  have argumentsBelow := ((Ty.variablesBelow_applyMany_iff state.inference.next
    (.constructor (.declaration dataType.id)) arguments).mp
      (by simpa only [Ty.nominal] using resolvedBelow)).2
  have bounds := Detail.instantiateDataConstructor_types_variablesBelow (dataType := dataType) argumentsBelow
    (formation.validated.data_constructor_payloadTypes_variablesBelow dataMember constructorMember state.inference.next)
  have progress := Detail.unify_inferenceProgress ready.solved bounds.2 expectedBelow unified
  have finalReady := Detail.unify_preserves_inferenceReady ready bounds.2 expectedBelow unified
  refine ⟨progress,finalReady,fun type member => (bounds.1 type member).weaken progress.next_le,?_⟩
  intro continuation
  have fields := unify_fields unified
  exact ⟨stateFormed.congr fields.1 fields.2,
    contextual_payload_formation formation dataMember constructorMember
      (matched_formation expectedFormed continuation unified)⟩

theorem explicit_pattern_prefix_formation
    {semantic : SourceSemantics.Context} {outer : Substitution}
    {context : SourceInference.Context} {state allocated final : State} {expected : Ty}
    {qualifiers : List String} {name : String} {dataType : ProgramDataSignature}
    {constructor : ProgramDataConstructorSignature} {instantiation : DataConstructorInstantiation}
    (ready : state.InferenceReady) (expectedBelow : expected.VariablesBelow state.inference.next)
    (formation : InferenceFormationContext semantic context outer)
    (stateFormed : NormalizedStateFormation semantic outer state)
    (expectedFormed : TypeAdmissible semantic (outer.apply expected))
    (selected : Detail.explicitConstructorCandidate context qualifiers name = .ok (dataType,constructor))
    (allocation : Detail.freshDataConstructorInstantiation dataType constructor state = (instantiation,allocated))
    (unified : Detail.unify allocated instantiation.resultType expected = .ok final) :
    PatternPrefixFormation semantic outer state final instantiation.payloadTypes := by
  obtain ⟨dataMember,constructorMember,_⟩ := Detail.explicitConstructorCandidate_success_facts selected
  have payloadClosed := formation.validated.data_constructor_payloadTypes_variablesBelow dataMember constructorMember 0
  have properties := Detail.freshDataConstructorInstantiation_inferenceProperties dataType constructor state ready
    (fun type member => (payloadClosed type member).weaken (Nat.zero_le _))
  have lexical := Detail.freshDataConstructorInstantiation_preserves_lexicalScope dataType constructor state
  have requirements := freshConstructor_requirements dataType constructor state
  rw [allocation] at properties lexical requirements
  have expectedBound := expectedBelow.weaken properties.1.next_le
  have progress := Detail.unify_inferenceProgress properties.2.1.solved properties.2.2.2.2 expectedBound unified
  have finalReady := Detail.unify_preserves_inferenceReady properties.2.1 properties.2.2.2.2 expectedBound unified
  refine ⟨properties.1.trans progress,finalReady,
    fun type member => (properties.2.2.2.1 type member).weaken progress.next_le,?_⟩
  intro continuation
  have fields := unify_fields unified
  have allocatedFormed := stateFormed.congr (congrArg LexicalScope.binders lexical) requirements
  refine ⟨allocatedFormed.congr fields.1 fields.2,?_⟩
  have resultFormed := matched_formation expectedFormed continuation unified
  obtain ⟨arguments,_,_,instantiationEq⟩ := Detail.freshDataConstructorInstantiation_success_shape allocation
  rw [instantiationEq] at resultFormed ⊢
  exact contextual_payload_formation formation dataMember constructorMember resultFormed

theorem tuple_pattern_prefix_formation
    {semantic : SourceSemantics.Context} {outer : Substitution}
    {context : SourceInference.Context} {state allocated final : State}
    {expected : Ty} {types : List Ty} {count : Nat}
    (ready : state.InferenceReady) (expectedBelow : expected.VariablesBelow state.inference.next)
    (formation : InferenceFormationContext semantic context outer)
    (stateFormed : NormalizedStateFormation semantic outer state)
    (allocation : Detail.freshTypes count state = (types,allocated))
    (unified : Detail.unify allocated expected (Ty.productMany types) = .ok final) :
    PatternPrefixFormation semantic outer state final types := by
  have properties := Detail.freshTypes_inferenceProperties count state ready
  have fields := freshTypes_fields count state
  have variables := freshTypes_variables count state
  rw [allocation] at properties fields variables
  have expectedBound := expectedBelow.weaken properties.1.next_le
  have productBound := Ty.variablesBelow_productMany properties.2.2
  have progress := Detail.unify_inferenceProgress properties.2.1.solved expectedBound productBound unified
  have finalReady := Detail.unify_preserves_inferenceReady properties.2.1 expectedBound productBound unified
  refine ⟨properties.1.trans progress,finalReady,
    fun type member => (properties.2.2 type member).weaken progress.next_le,?_⟩
  intro _
  have finalFields := unify_fields unified
  refine ⟨(stateFormed.congr fields.1 fields.2).congr finalFields.1 finalFields.2,?_⟩
  intro type member
  obtain ⟨metavariable,rfl⟩ := variables type member
  exact type_applySubstitution_residual formation.residual formation.range
    (.variableOfResidual formation.scope.binders formation.residual _)

theorem integer_pattern_prefix_formation
    {semantic : SourceSemantics.Context} {outer : Substitution}
    {context : SourceInference.Context} {state recorded final : State}
    {metavariable : TypeVarId} {normalized : Ty} {requirement : RequirementId}
    (formation : InferenceFormationContext semantic context outer)
    (stateFormed : NormalizedStateFormation semantic outer state)
    (unified : Detail.unify recorded (.variable metavariable) normalized = .ok final)
    (binders : recorded.localBinders = state.localBinders)
    (requirements : recorded.requirements = state.requirements ++
      [{id := requirement,predicate := ProgramSignatures.builtinIntPredicate (.variable metavariable)}]) :
    NormalizedStateFormation semantic outer final := by
  have recordedFormed : NormalizedStateFormation semantic outer recorded := by
    refine ⟨?_,fun binder member => stateFormed.binders binder (binders ▸ member)⟩
    intro row member
    rw [requirements] at member
    rcases List.mem_append.mp member with old | issued
    · exact stateFormed.requirements row old
    · cases List.mem_singleton.mp issued
      apply builtin_integer_predicate
      exact type_applySubstitution_residual formation.residual formation.range
        (.variableOfResidual formation.scope.binders formation.residual _)
  have fields := unify_fields unified
  exact recordedFormed.congr fields.1 fields.2

end Solcore.SourceSemantics.SourceInferenceNormalizedCoercionFormation
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceNormalizedPatternFormation
/-! Normalized formation follows all actual nested pattern calls. The final
substitution is threaded backwards through their accepted continuations. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceNormalizedCoercionFormation
open Frontend SourceInference TypeSystem Detail SourceInferenceSoundness

private def PatternCallFormation (semantic : SourceSemantics.Context) (outer : Substitution)
    (fuel : Nat) (context : SourceInference.Context) (pattern : Syntax.Pattern) (expected : Ty)
    (seen : List String) (state : State) : Prop :=
  ∀ result, state.InferenceReady → expected.VariablesBelow state.inference.next →
    InferenceFormationContext semantic context outer →
    NormalizedStateFormation semantic outer state →
    TypeAdmissible semantic (outer.apply expected) →
    inferMatchPatternFlatFuel fuel context pattern expected seen state = .ok result →
    outer.SemanticallyExtends result.state.inference.substitution →
    NormalizedStateFormation semantic outer result.state

private def PatternsCallFormation (semantic : SourceSemantics.Context) (outer : Substitution)
    (fuel : Nat) (context : SourceInference.Context) (patterns : List Syntax.Pattern) (expected : List Ty)
    (seen : List String) (state : State) : Prop :=
  ∀ result, state.InferenceReady →
    (∀ type ∈ expected, type.VariablesBelow state.inference.next) →
    InferenceFormationContext semantic context outer →
    NormalizedStateFormation semantic outer state →
    (∀ type ∈ expected, TypeAdmissible semantic (outer.apply type)) →
    inferMatchPatternsFlatFuel fuel context patterns expected seen state = .ok result →
    outer.SemanticallyExtends result.state.inference.substitution →
    NormalizedStateFormation semantic outer result.state

set_option maxHeartbeats 2000000 in
private theorem pattern_call_formation (semantic : SourceSemantics.Context) (outer : Substitution)
    (fuel : Nat) (context : SourceInference.Context) (pattern : Syntax.Pattern) (expected : Ty)
    (seen : List String) (state : State) :
    PatternCallFormation semantic outer fuel context pattern expected seen state := by
  apply inferMatchPatternFlatFuel.induct context
    (motive1 := fun fuel pattern expected seen state =>
      PatternCallFormation semantic outer fuel context pattern expected seen state)
    (motive2 := fun fuel patterns expected seen state =>
      PatternsCallFormation semantic outer fuel context patterns expected seen state)
  case case3 =>
    intros
    unfold PatternCallFormation at *
    intro result ready expectedBelow formation formed expectedFormed success continuation
    unfold inferMatchPatternFlatFuel at success
    simp_all [bind,Except.bind]
    repeat' first | split at success
    all_goals try cases success
    all_goals simp_all [pure,Pure.pure,Except.pure]
    all_goals
      rename_i unified
      exact integer_pattern_prefix_formation formation formed unified rfl rfl
  case case5 =>
    intros
    unfold PatternCallFormation at *
    intro result ready expectedBelow formation formed expectedFormed success continuation
    unfold inferMatchPatternFlatFuel at success
    simp_all [bind,Except.bind]
    repeat' first | split at success
    all_goals try cases success
    all_goals simp_all [pure,Pure.pure,Except.pure]
    all_goals
      rename_i unified
      exact integer_pattern_prefix_formation formation formed unified rfl rfl
  case case10 =>
    intros sourcePattern sourceExpected sourceSeen inputState sourceFuel
      leadingDot qualifiers constructorName sourceArguments patternEq branchEq
      flatArguments contextualBranch childrenIH
    unfold PatternCallFormation at *
    intro result ready expectedBelow formation formed expectedFormed success continuation
    unfold inferMatchPatternFlatFuel at success
    simp_all [bind,Except.bind]
    repeat' first | split at success
    all_goals try cases success
    all_goals simp_all [pure,Pure.pure,Except.pure]
    all_goals try subst_vars
    all_goals first
      | have beforeChildren := contextual_pattern_prefix_formation ready expectedBelow formation formed expectedFormed
          (by assumption) (by assumption)
        have childProperties := inferMatchPatternsFlatFuel_inferenceProperties beforeChildren.ready beforeChildren.below
          formation.validated (by assumption)
        have prefixFormed := beforeChildren.formed (continuation.trans childProperties.1.substitution_extends)
        exact childrenIH _ _ _ beforeChildren.ready beforeChildren.below formation prefixFormed.1 prefixFormed.2
          (by assumption) continuation
      | have beforeChildren := explicit_pattern_prefix_formation ready expectedBelow formation formed expectedFormed
          (by assumption) rfl (by assumption)
        have childProperties := inferMatchPatternsFlatFuel_inferenceProperties beforeChildren.ready beforeChildren.below
          formation.validated (by assumption)
        have prefixFormed := beforeChildren.formed (continuation.trans childProperties.1.substitution_extends)
        exact childrenIH _ _ _ beforeChildren.ready beforeChildren.below formation prefixFormed.1 prefixFormed.2
          (by assumption) continuation
  case case11 =>
    intros sourcePattern sourceExpected sourceSeen inputState sourceFuel
      leadingDot qualifiers constructorName sourceArguments patternEq branchEq
      flatArguments explicitBranch childrenIH
    unfold PatternCallFormation at *
    intro result ready expectedBelow formation formed expectedFormed success continuation
    unfold inferMatchPatternFlatFuel at success
    simp_all [bind,Except.bind]
    repeat' first | split at success
    all_goals try cases success
    all_goals simp_all [pure,Pure.pure,Except.pure]
    all_goals try subst_vars
    all_goals first
      | have beforeChildren := contextual_pattern_prefix_formation ready expectedBelow formation formed expectedFormed
          (by assumption) (by assumption)
        have childProperties := inferMatchPatternsFlatFuel_inferenceProperties beforeChildren.ready beforeChildren.below
          formation.validated (by assumption)
        have prefixFormed := beforeChildren.formed (continuation.trans childProperties.1.substitution_extends)
        exact childrenIH _ _ _ beforeChildren.ready beforeChildren.below formation prefixFormed.1 prefixFormed.2
          (by assumption) continuation
      | have beforeChildren := explicit_pattern_prefix_formation ready expectedBelow formation formed expectedFormed
          (by assumption) rfl (by assumption)
        have childProperties := inferMatchPatternsFlatFuel_inferenceProperties beforeChildren.ready beforeChildren.below
          formation.validated (by assumption)
        have prefixFormed := beforeChildren.formed (continuation.trans childProperties.1.substitution_extends)
        exact childrenIH _ _ _ beforeChildren.ready beforeChildren.below formation prefixFormed.1 prefixFormed.2
          (by assumption) continuation
  case case13 =>
    intros sourcePattern sourceExpected sourceSeen inputState sourceFuel
      elements patternEq sources argumentTypes allocatedState freshEq childrenIH
    unfold PatternCallFormation at *
    intro result ready expectedBelow formation formed expectedFormed success continuation
    unfold inferMatchPatternFlatFuel at success
    simp_all [bind,Except.bind]
    repeat' first | split at success
    all_goals try cases success
    all_goals simp_all
    have argumentTypesEq : (freshTypes sources.length inputState).1 = argumentTypes := congrArg Prod.fst freshEq
    have allocatedStateEq : (freshTypes sources.length inputState).2 = allocatedState := congrArg Prod.snd freshEq
    have beforeChildren := tuple_pattern_prefix_formation (count := sources.length) (types := argumentTypes)
      (allocated := allocatedState) ready expectedBelow formation formed freshEq (by
        rw [← allocatedStateEq,← argumentTypesEq]
        simpa only [sources] using (by assumption))
    rename_i rawChildren
    have childRun := rawChildren
    change inferMatchPatternsFlatFuel sourceFuel context sources
      (freshTypes sources.length inputState).1 sourceSeen _ = _ at childRun
    rw [argumentTypesEq] at childRun
    have childProperties := inferMatchPatternsFlatFuel_inferenceProperties beforeChildren.ready beforeChildren.below
      formation.validated childRun
    have prefixFormed := beforeChildren.formed (continuation.trans childProperties.1.substitution_extends)
    exact childrenIH _ _ beforeChildren.ready beforeChildren.below formation prefixFormed.1 prefixFormed.2
      childRun continuation
  case case17 =>
    intros fuel head rest expectedHead expectedTail seen state ihHead ihTail
    unfold PatternsCallFormation
    unfold PatternCallFormation at ihHead
    unfold PatternsCallFormation at ihTail
    intro result ready expectedBelow formation formed expectedFormed success continuation
    simp only [inferMatchPatternsFlatFuel] at success
    cases headRun : inferMatchPatternFlatFuel fuel context head expectedHead seen state with
    | error error => simp [headRun,bind,Except.bind] at success
    | ok inferredHead =>
      simp only [headRun,bind,Except.bind] at success
      cases tailRun : inferMatchPatternsFlatFuel fuel context rest expectedTail inferredHead.names inferredHead.state with
      | error error => simp [tailRun] at success
      | ok inferredTail =>
        simp only [tailRun] at success
        injection success with resultEq
        subst result
        have headProperties := inferMatchPatternFlatFuel_inferenceProperties ready
          (expectedBelow _ List.mem_cons_self) formation.validated headRun
        have tailBelow : ∀ type ∈ expectedTail, type.VariablesBelow inferredHead.state.inference.next :=
          fun type member => (expectedBelow type (List.mem_cons_of_mem _ member)).weaken headProperties.1.next_le
        have tailProperties := inferMatchPatternsFlatFuel_inferenceProperties headProperties.2 tailBelow formation.validated tailRun
        have headFormation := ihHead inferredHead ready (expectedBelow _ List.mem_cons_self) formation formed
          (expectedFormed _ List.mem_cons_self) headRun (continuation.trans tailProperties.1.substitution_extends)
        exact ihTail inferredHead inferredTail headProperties.2 tailBelow formation headFormation
          (fun type member => expectedFormed type (List.mem_cons_of_mem _ member)) tailRun continuation
  all_goals
    intros
    first | unfold PatternCallFormation at * | unfold PatternsCallFormation at *
    intro result ready expectedBelow formation formed expectedFormed success continuation
    first | unfold inferMatchPatternFlatFuel at success | unfold inferMatchPatternsFlatFuel at success
    simp_all [bind,Except.bind]
    repeat' first | split at success
    all_goals try cases success
    all_goals try simp_all
    all_goals try exact formed
    all_goals try exact (by simpa only using ih1 _ ready expectedBelow formation formed expectedFormed (by assumption) continuation)
    all_goals
      apply NormalizedStateFormation.allocate formed
      apply NormalizedBinderFormation.mono
      exact (continuation _).symm ▸ expectedFormed

/-- All actual nested pattern constructors preserve normalized formation. -/
theorem inferMatchPatternFlatFuel_normalized_formation
    {semantic : SourceSemantics.Context} {outer : Substitution} {fuel : Nat}
    {context : SourceInference.Context} {pattern : Syntax.Pattern} {expected : Ty}
    {seen : List String} {state : State} {result : InferredPattern}
    (ready : state.InferenceReady) (expectedBelow : expected.VariablesBelow state.inference.next)
    (formation : InferenceFormationContext semantic context outer)
    (formed : NormalizedStateFormation semantic outer state)
    (expectedFormed : TypeAdmissible semantic (outer.apply expected))
    (accepted : inferMatchPatternFlatFuel fuel context pattern expected seen state = .ok result)
    (continuation : outer.SemanticallyExtends result.state.inference.substitution) :
    NormalizedStateFormation semantic outer result.state :=
  pattern_call_formation semantic outer fuel context pattern expected seen state result ready expectedBelow formation
    formed expectedFormed accepted continuation

/-- The public pattern wrapper retains the actual recursive pattern state. -/
theorem inferMatchPatternFuel_normalized_formation
    {semantic : SourceSemantics.Context} {outer : Substitution} {fuel : Nat}
    {context : SourceInference.Context} {pattern : Syntax.Pattern} {expected : Ty}
    {state : State} {result : TypedMatchPattern × State}
    (ready : state.InferenceReady) (expectedBelow : expected.VariablesBelow state.inference.next)
    (formation : InferenceFormationContext semantic context outer)
    (formed : NormalizedStateFormation semantic outer state)
    (expectedFormed : TypeAdmissible semantic (outer.apply expected))
    (accepted : inferMatchPatternFuel fuel context pattern expected state = .ok result)
    (continuation : outer.SemanticallyExtends result.2.inference.substitution) :
    NormalizedStateFormation semantic outer result.2 := by
  unfold inferMatchPatternFuel at accepted
  cases actual : inferMatchPatternFlatFuel fuel context pattern expected [] state with
  | error error => simp [actual,bind,Except.bind] at accepted
  | ok inferred =>
    simp only [actual,bind,Except.bind,pure,Pure.pure,Except.pure,Except.ok.injEq] at accepted
    cases accepted
    exact inferMatchPatternFlatFuel_normalized_formation ready expectedBelow formation formed expectedFormed actual continuation

end Solcore.SourceSemantics.SourceInferenceNormalizedCoercionFormation
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceNormalizedMatchContinuation
/-! Actual match inference retains normalized formation through patterns,
arm bodies, saved lexical scopes and the optional default continuation. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000
namespace Solcore.SourceSemantics.SourceInferenceNormalizedCoercionFormation
open Frontend SourceInference TypeSystem Detail SourceInferenceSoundness

theorem inferMatchCasesFuel_cons_formation
    {semantic : SourceSemantics.Context} {outer : Substitution}
    {fuel : Nat} {context : SourceInference.Context}
    {scrutineeType expectedReturn : Ty} {outerScope : LexicalScope}
    {arm : Syntax.MatchCase} {rest : List Syntax.MatchCase} {initial : State}
    (bodyIH : ∀ state, InferStatementsFuelFormation semantic outer fuel context
      arm.value.body.value expectedReturn state)
    (tailIH : ∀ body : BlockResult, InferMatchCasesFuelFormation semantic outer fuel
      context scrutineeType expectedReturn outerScope rest
      (body.state.restoreLexicalScope outerScope)) :
    InferMatchCasesFuelFormation semantic outer (fuel + 1) context scrutineeType
      expectedReturn outerScope (arm :: rest) initial := by
  intro ready nodes formed formation scrutineeBelow scrutineeFormed returnBelow returnFormed
    scopeEq result accepted continuation noCapture
  subst outerScope
  unfold inferMatchCasesFuel at accepted
  simp only [bind, Except.bind] at accepted
  cases patternRun : inferMatchPatternFuel fuel context arm.value.pattern scrutineeType initial with
  | error error => simp [patternRun] at accepted
  | ok patternPair =>
    rcases patternPair with ⟨pattern, patternState⟩
    simp only [patternRun] at accepted
    cases bodyRun : inferStatementsFuel fuel context arm.value.body.value expectedReturn patternState with
    | error error => simp [bodyRun] at accepted
    | ok body =>
      simp only [bodyRun] at accepted
      cases tailRun : inferMatchCasesFuel fuel context scrutineeType expectedReturn initial.lexicalScope
          rest (body.state.restoreLexicalScope initial.lexicalScope) with
      | error error => simp [tailRun] at accepted
      | ok tail =>
        simp only [tailRun, pure, Pure.pure, Except.pure, Except.ok.injEq] at accepted
        subst result
        have patternProperties := inferMatchPatternFuel_inferenceProperties ready
          scrutineeBelow formation.validated patternRun
        have patternNodes := (inferMatchPatternFuel_occurrenceBoundExtends patternRun).nodesBelowNextOccurrence nodes
        have returnAtPattern := returnBelow.weaken patternProperties.1.next_le
        have bodyProperties := inferStatementsFuel_inferenceProperties patternProperties.2.1
          formation.validated formation.functionShapes returnAtPattern bodyRun
        have bodyNodes := (inferStatementsFuel_occurrenceBoundExtends bodyRun).nodesBelowNextOccurrence patternNodes
        have throughBody := patternProperties.1.trans bodyProperties.1
        have restoredProperties := State.restoreLexicalScope_inferenceProperties ready throughBody
        have restoredNodes := State.restoreLexicalScope_preserves_nodesBelowNextOccurrence
          body.state initial.lexicalScope bodyNodes
        have tailProperties := inferMatchCasesFuel_inferenceProperties restoredProperties.2
          formation.validated formation.functionShapes
          (scrutineeBelow.weaken restoredProperties.1.next_le)
          (returnBelow.weaken restoredProperties.1.next_le) (by simp) tailRun
        have bodyContinuation : outer.SemanticallyExtends body.state.inference.substitution :=
          continuation.trans tailProperties.1.substitution_extends
        have patternFormed := inferMatchPatternFuel_normalized_formation ready scrutineeBelow formation formed
          scrutineeFormed patternRun (bodyContinuation.trans bodyProperties.1.substitution_extends)
        have bodyNoCapture : NoCaptureNodes outer body.state.nodes :=
          noCapture.of_prefix (inferMatchCasesFuel_preserves_nodesPrefix
            (state := body.state.restoreLexicalScope initial.lexicalScope) (result := tail)
            tailRun List.prefix_rfl restoredNodes (Nat.le_refl _))
        have bodyFormed := bodyIH patternState patternProperties.2.1 patternNodes patternFormed formation
          returnAtPattern returnFormed body bodyRun bodyContinuation bodyNoCapture
        exact tailIH body restoredProperties.2 restoredNodes
          (formed.restore bodyFormed.2 initial.lexicalScope (by intro _ member; exact member)) formation
          (scrutineeBelow.weaken restoredProperties.1.next_le) scrutineeFormed
          (returnBelow.weaken restoredProperties.1.next_le) returnFormed (by simp)
          tail tailRun continuation noCapture

private def finishMatch (fuel : Nat) (context : SourceInference.Context)
    (statement : Syntax.Statement) (id : StatementId) (hidden : Resolved.LocalId)
    (scrutinee : InferredExpression) (arms : Syntax.Located Syntax.MatchArmsValue)
    (expectedReturn : Ty) (state : State) : Except Error StatementResult := do
  let outerScope := state.lexicalScope
  let checked ← inferMatchCasesFuel fuel context scrutinee.type expectedReturn outerScope arms.value.cases state
  let (defaultBody,state) ← match arms.value.defaultBody with
    | none => pure (none,checked.state)
    | some body => do
      let inferred ← inferStatementsFuel fuel context body.value expectedReturn checked.state
      pure (some (inferred.statements,inferred.sawReturn),inferred.state.restoreLexicalScope outerScope)
  let exhaustive := checked.hasWildcard || defaultBody.isSome ||
    exhaustsNominalConstructors context state scrutinee.type checked.cases
  if !exhaustive then throw (.nonExhaustiveMatch statement.span) else
    let requirements := checked.cases.flatMap fun arm => arm.pattern.requirements
    let defaultStatements := defaultBody.map (·.1)
    let defaultReturns := defaultBody.map (·.2) |>.getD true
    let sawReturn := checked.allReturn && defaultReturns
    let type := if sawReturn then state.resolve expectedReturn else .unit
    let state := state.recordNode (.statement {
      id := id
      span := statement.span
      type := type
      form := .matchWith {
        scrutinee := scrutinee.id
        hiddenScrutinee := hidden
        cases := checked.cases
        defaultBody := defaultStatements
        requirements := requirements
      }
    })
    pure {
      id := id
      type := type
      hasValue := sawReturn
      sawReturn := sawReturn
      state := state
    }


private theorem finishMatch_progress
    {semantic : SourceSemantics.Context} {outer : Substitution}
    {fuel : Nat} {context : SourceInference.Context}
    {statement : Syntax.Statement} {id : StatementId} {hidden : Resolved.LocalId}
    {scrutinee : InferredExpression} {arms : Syntax.Located Syntax.MatchArmsValue}
    {expectedReturn : Ty} {state : State} {result : StatementResult}
    (ready : state.InferenceReady) (nodes : state.NodesBelowNextOccurrence)
    (formation : InferenceFormationContext semantic context outer)
    (scrutineeBelow : scrutinee.type.VariablesBelow state.inference.next)
    (returnBelow : expectedReturn.VariablesBelow state.inference.next)
    (success : finishMatch fuel context statement id hidden scrutinee arms expectedReturn state = .ok result) :
    state.InferenceProgress result.state ∧ state.nodes <+: result.state.nodes := by
  unfold finishMatch at success
  simp only [bind,Except.bind] at success
  cases casesRun : inferMatchCasesFuel fuel context scrutinee.type expectedReturn state.lexicalScope arms.value.cases state with
  | error error => simp [casesRun] at success
  | ok checked =>
    simp only [casesRun] at success
    have casesProperties := inferMatchCasesFuel_inferenceProperties ready formation.validated formation.functionShapes scrutineeBelow returnBelow rfl casesRun
    have casesNodes := (inferMatchCasesFuel_occurrenceBoundExtends casesRun).nodesBelowNextOccurrence nodes
    have casesPrefix := inferMatchCasesFuel_preserves_nodesPrefix casesRun List.prefix_rfl nodes (Nat.le_refl _)
    cases defaultEq : arms.value.defaultBody with
    | none =>
      simp only [defaultEq,pure,Pure.pure,Except.pure] at success
      split at success
      · cases success
      · injection success with resultEq
        subst result
        exact ⟨⟨casesProperties.1.next_le, casesProperties.1.solved, casesProperties.1.substitution_extends⟩, casesPrefix.trans (State.recordNode_nodesPrefix _ _)⟩
    | some body =>
      cases bodyRun : inferStatementsFuel fuel context body.value expectedReturn checked.state with
      | error error => simp [defaultEq,bodyRun] at success
      | ok checkedBody =>
        simp only [defaultEq,bodyRun,pure,Pure.pure,Except.pure] at success
        have bodyProperties := inferStatementsFuel_inferenceProperties casesProperties.2.1
          formation.validated formation.functionShapes (returnBelow.weaken casesProperties.1.next_le) bodyRun
        have bodyPrefix := inferStatementsFuel_preserves_nodesPrefix bodyRun List.prefix_rfl casesNodes (Nat.le_refl _)
        split at success
        · cases success
        · injection success with resultEq
          subst result
          have progress := casesProperties.1.trans bodyProperties.1
          exact ⟨⟨progress.next_le, progress.solved, progress.substitution_extends⟩,
            (casesPrefix.trans bodyPrefix).trans (State.recordNode_nodesPrefix _ _)⟩

private theorem finishMatch_formation
    {semantic : SourceSemantics.Context} {outer : Substitution}
    {fuel : Nat} {context : SourceInference.Context}
    {statement : Syntax.Statement} {id : StatementId} {hidden : Resolved.LocalId}
    {scrutinee : InferredExpression} {arms : Syntax.Located Syntax.MatchArmsValue}
    {expectedReturn : Ty} {state : State}
    (ready : state.InferenceReady) (nodes : state.NodesBelowNextOccurrence)
    (formed : NormalizedStateFormation semantic outer state)
    (formation : InferenceFormationContext semantic context outer)
    (scrutineeBelow : scrutinee.type.VariablesBelow state.inference.next)
    (scrutineeFormed : TypeAdmissible semantic (outer.apply scrutinee.type))
    (returnBelow : expectedReturn.VariablesBelow state.inference.next)
    (returnFormed : TypeAdmissible semantic (outer.apply expectedReturn))
    (casesIH : InferMatchCasesFuelFormation semantic outer fuel context scrutinee.type expectedReturn state.lexicalScope arms.value.cases state)
    (bodyIH : ∀ (checked : MatchCasesResult) (body : Syntax.Located (List Syntax.Statement)),
      InferStatementsFuelFormation semantic outer fuel context body.value expectedReturn checked.state)
    {result : StatementResult}
    (success : finishMatch fuel context statement id hidden scrutinee arms expectedReturn state = .ok result)
    (continuation : outer.SemanticallyExtends result.state.inference.substitution)
    (noCapture : NoCaptureNodes outer result.state.nodes) :
    TypeAdmissible semantic (outer.apply result.type) ∧ NormalizedStateFormation semantic outer result.state := by
  unfold finishMatch at success
  simp only [bind,Except.bind] at success
  cases casesRun : inferMatchCasesFuel fuel context scrutinee.type expectedReturn state.lexicalScope arms.value.cases state with
  | error error => simp [casesRun] at success
  | ok checked =>
    simp only [casesRun] at success
    have casesProperties := inferMatchCasesFuel_inferenceProperties ready formation.validated formation.functionShapes scrutineeBelow returnBelow rfl casesRun
    have casesNodes := (inferMatchCasesFuel_occurrenceBoundExtends casesRun).nodesBelowNextOccurrence nodes
    cases defaultEq : arms.value.defaultBody with
    | none =>
      simp only [defaultEq,pure,Pure.pure,Except.pure] at success
      split at success
      · cases success
      · injection success with resultEq
        subst result
        have casesFormed := casesIH ready nodes formed formation scrutineeBelow scrutineeFormed
          returnBelow returnFormed rfl checked casesRun continuation
          (noCapture.of_prefix (State.recordNode_nodesPrefix _ _))
        refine ⟨?_, casesFormed.congr rfl rfl⟩
        split
        · exact (continuation expectedReturn).symm ▸ returnFormed
        · exact .unit formation.scope.binders
    | some body =>
      cases bodyRun : inferStatementsFuel fuel context body.value expectedReturn checked.state with
      | error error => simp [defaultEq,bodyRun] at success
      | ok checkedBody =>
        simp only [defaultEq,bodyRun,pure,Pure.pure,Except.pure] at success
        have bodyProperties := inferStatementsFuel_inferenceProperties casesProperties.2.1
          formation.validated formation.functionShapes (returnBelow.weaken casesProperties.1.next_le) bodyRun
        have bodyPrefix := inferStatementsFuel_preserves_nodesPrefix bodyRun List.prefix_rfl casesNodes (Nat.le_refl _)
        split at success
        · cases success
        · injection success with resultEq
          subst result
          have bodyNoCapture : NoCaptureNodes outer checkedBody.state.nodes :=
            noCapture.of_prefix (State.recordNode_nodesPrefix _ _)
          have casesFormed := casesIH ready nodes formed formation scrutineeBelow scrutineeFormed
            returnBelow returnFormed rfl checked casesRun
            (continuation.trans bodyProperties.1.substitution_extends) (bodyNoCapture.of_prefix bodyPrefix)
          have bodyFormed := bodyIH checked body casesProperties.2.1 casesNodes casesFormed formation
            (returnBelow.weaken casesProperties.1.next_le) returnFormed checkedBody bodyRun continuation bodyNoCapture
          have restored := formed.restore bodyFormed.2 state.lexicalScope (by intro _ member; exact member)
          refine ⟨?_, restored.congr rfl rfl⟩
          split
          · exact (continuation expectedReturn).symm ▸ returnFormed
          · exact .unit formation.scope.binders

theorem inferStatementFuel_match_single_formation
    {semantic : SourceSemantics.Context} {outer : Substitution}
    {fuel : Nat} {context : SourceInference.Context}
    {statement : Syntax.Statement} {scrutinees : Syntax.NonemptyDelimitedList Syntax.Expr}
    {arms : Syntax.Located Syntax.MatchArmsValue} {source : Syntax.Expr} {expectedReturn : Ty} {initial : State}
    (form : statement.value = .matchWith scrutinees arms)
    (single : scrutinees.elements.toList = [source])
    (casesIH : ∀ (scrutinee : InferredExpression) (state : State),
      InferMatchCasesFuelFormation semantic outer fuel context scrutinee.type expectedReturn state.lexicalScope arms.value.cases state)
    (bodyIH : ∀ (checked : MatchCasesResult) (body : Syntax.Located (List Syntax.Statement)),
      InferStatementsFuelFormation semantic outer fuel context body.value expectedReturn checked.state)
    (sourceIH : InferExprFuelFormation semantic outer fuel context source none initial.allocateStatementId.2) :
    InferStatementFuelFormation semantic outer (fuel+1) context statement expectedReturn initial := by
  intro ready nodes formed formation returnBelow returnFormed result success continuation noCapture
  let allocated := initial.allocateStatementId.2
  have allocatedReady : allocated.InferenceReady := State.InferenceReady.allocateStatementId ready
  have allocatedNodes := (State.OccurrenceBoundExtends.allocateStatementId initial).nodesBelowNextOccurrence nodes
  unfold inferStatementFuel at success
  simp only [form,single,bind,Except.bind] at success
  cases sourceRun : inferExprFuel fuel context source none allocated with
  | error error => simp [allocated,sourceRun] at success
  | ok pair =>
    rcases pair with ⟨scrutinee,sourceState⟩
    simp only [allocated,sourceRun] at success
    have sourceProperties := inferExprFuel_inferenceProperties allocatedReady formation.validated formation.functionShapes (by simp) sourceRun
    have sourceNodes := (inferExprFuel_occurrenceBoundExtends sourceRun).nodesBelowNextOccurrence allocatedNodes
    let hiddenState := sourceState.allocateHiddenLocal.2
    have hiddenReady : hiddenState.InferenceReady := State.InferenceReady.allocateHiddenLocal sourceProperties.2.1
    have hiddenNodes := (State.OccurrenceBoundExtends.allocateHiddenLocal sourceState).nodesBelowNextOccurrence sourceNodes
    have finishRun : finishMatch fuel context statement initial.allocateStatementId.1 sourceState.allocateHiddenLocal.1
        scrutinee arms expectedReturn hiddenState = .ok result := success
    have finished := finishMatch_progress hiddenReady hiddenNodes formation sourceProperties.2.2
      (returnBelow.weaken sourceProperties.1.next_le) finishRun
    have sourceFormed := sourceIH allocatedReady allocatedNodes (formed.congr rfl rfl) formation
      (by simp) (by simp) (scrutinee,sourceState) sourceRun
      (continuation.trans finished.1.substitution_extends) (noCapture.of_prefix finished.2)
    exact finishMatch_formation hiddenReady hiddenNodes (sourceFormed.2.congr rfl rfl) formation
      sourceProperties.2.2 sourceFormed.1 (returnBelow.weaken sourceProperties.1.next_le) returnFormed
      (casesIH scrutinee hiddenState) bodyIH finishRun continuation noCapture

theorem inferStatementFuel_match_many_formation
    {semantic : SourceSemantics.Context} {outer : Substitution}
    {fuel : Nat} {context : SourceInference.Context}
    {statement : Syntax.Statement} {scrutinees : Syntax.NonemptyDelimitedList Syntax.Expr}
    {arms : Syntax.Located Syntax.MatchArmsValue} {expectedReturn : Ty} {initial : State}
    (form : statement.value = .matchWith scrutinees arms)
    (notSingleton : ∀ source, scrutinees.elements.toList = [source] → False)
    (casesIH : ∀ (scrutinee : InferredExpression) (state : State),
      InferMatchCasesFuelFormation semantic outer fuel context scrutinee.type expectedReturn state.lexicalScope arms.value.cases state)
    (bodyIH : ∀ (checked : MatchCasesResult) (body : Syntax.Located (List Syntax.Statement)),
      InferStatementsFuelFormation semantic outer fuel context body.value expectedReturn checked.state)
    (sourcesIH : InferExprsFuelFormation semantic outer fuel context scrutinees.elements.toList initial.allocateStatementId.2) :
    InferStatementFuelFormation semantic outer (fuel+1) context statement expectedReturn initial := by
  intro ready nodes formed formation returnBelow returnFormed result success continuation noCapture
  let allocated := initial.allocateStatementId.2
  have allocatedReady : allocated.InferenceReady := State.InferenceReady.allocateStatementId ready
  have allocatedNodes := (State.OccurrenceBoundExtends.allocateStatementId initial).nodesBelowNextOccurrence nodes
  unfold inferStatementFuel at success
  simp only [form] at success
  simp only [bind,Except.bind] at success
  cases sourcesRun : inferExprsFuel fuel context scrutinees.elements.toList initial.allocateStatementId.2 with
  | error error => simp [sourcesRun] at success
  | ok pair =>
    rcases pair with ⟨elements,elementState⟩
    simp only [sourcesRun,pure,Pure.pure,Except.pure] at success
    have properties := inferExprsFuel_inferenceProperties allocatedReady formation.validated formation.functionShapes sourcesRun
    have elementNodes := (inferExprsFuel_occurrenceBoundExtends sourcesRun).nodesBelowNextOccurrence allocatedNodes
    let tuple : InferredExpression := {id := elementState.allocateExpressionId.1,type := Ty.productMany (elements.map (·.type))}
    let tupleNode : Node := .expression {
      id := tuple.id
      span := statement.span
      type := tuple.type
      form := .tuple (elements.map (·.id)) }
    let tupleState := elementState.allocateExpressionId.2.recordNode tupleNode
    have tupleReady : tupleState.InferenceReady := State.InferenceReady.recordNode _
      (State.InferenceReady.allocateExpressionId properties.2.1)
    have tupleNodes : tupleState.NodesBelowNextOccurrence :=
      (State.OccurrenceBoundExtends.recordNode _ tupleNode
        (State.allocateExpressionId_index_lt_nextOccurrence elementState)).nodesBelowNextOccurrence
          ((State.OccurrenceBoundExtends.allocateExpressionId elementState).nodesBelowNextOccurrence elementNodes)
    have tupleBelow : tuple.type.VariablesBelow tupleState.inference.next := by
      apply Ty.variablesBelow_productMany
      intro type member
      obtain ⟨element,elementMember,rfl⟩ := List.mem_map.mp member
      exact properties.2.2 element elementMember
    let hiddenState := tupleState.allocateHiddenLocal.2
    have hiddenReady : hiddenState.InferenceReady := State.InferenceReady.allocateHiddenLocal tupleReady
    have hiddenNodes := (State.OccurrenceBoundExtends.allocateHiddenLocal tupleState).nodesBelowNextOccurrence tupleNodes
    have finishRun : finishMatch fuel context statement initial.allocateStatementId.1 tupleState.allocateHiddenLocal.1
        tuple arms expectedReturn hiddenState = .ok result := success
    have finished := finishMatch_progress hiddenReady hiddenNodes formation tupleBelow
      (returnBelow.weaken properties.1.next_le) finishRun
    have elementNoCapture : NoCaptureNodes outer elementState.nodes :=
      noCapture.of_prefix ((State.recordNode_nodesPrefix elementState.allocateExpressionId.2 tupleNode).trans finished.2)
    have elementsFormed := sourcesIH allocatedReady allocatedNodes (formed.congr rfl rfl) formation
      (elements,elementState) sourcesRun (continuation.trans finished.1.substitution_extends) elementNoCapture
    have tupleFormed : TypeAdmissible semantic (outer.apply tuple.type) := by
      change TypeAdmissible semantic (outer.apply (Ty.productMany (elements.map (·.type))))
      rw [Substitution.apply_productMany]
      apply TypeAdmissible.productMany formation.scope.binders
      intro type member
      obtain ⟨raw,rawMember,rfl⟩ := List.mem_map.mp member
      obtain ⟨element,elementMember,rfl⟩ := List.mem_map.mp rawMember
      exact elementsFormed.1 element elementMember
    exact finishMatch_formation hiddenReady hiddenNodes (elementsFormed.2.congr rfl rfl) formation
      tupleBelow tupleFormed (returnBelow.weaken properties.1.next_le) returnFormed
      (casesIH tuple hiddenState) bodyIH finishRun continuation noCapture

end Solcore.SourceSemantics.SourceInferenceNormalizedCoercionFormation
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceNormalizedIndexContinuation
/-! Index expressions and places retain normalized formation through their
actual base inference, fresh mapping variables, unification and key inference. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000
namespace Solcore.SourceSemantics.SourceInferenceNormalizedCoercionFormation
open Frontend SourceInference TypeSystem Detail SourceInferenceSoundness SourceInferenceRequirementFormation

private theorem recording_fields
    {context : SourceInference.Context} {source : Syntax.Expr} {id : ExpressionId}
    {type : Ty} {form : ExpressionForm} {expected : Option Ty} {state : State}
    {result : InferredExpression × State}
    (accepted : recordExpressionWithExpected context source id type form [] expected state = .ok result) :
    result.2.localBinders = state.localBinders ∧ state.nodes <+: result.2.nodes := by
  obtain ⟨fitted, run, _, resultEq⟩ := recordExpressionWithExpected_success_record accepted
  rw [resultEq]
  refine ⟨?_, ?_⟩
  · exact congrArg LexicalScope.binders (localReadScope_withExpected_lexicalScope run)
  · rw [State.recordNode_nodes, (withExpected_occurrenceState_eq run).1]
    exact List.prefix_append _ _

private structure MappingPrefix (base final : State) : Prop where
  progress : base.InferenceProgress final
  ready : final.InferenceReady
  keyBelow : (final.resolve base.fresh.1).VariablesBelow final.inference.next
  valueBelow : base.fresh.2.fresh.1.VariablesBelow final.inference.next
  nodes : final.nodes = base.nodes
  occurrence : final.nextOccurrence = base.nextOccurrence
  binders : final.localBinders = base.localBinders
  requirements : final.requirements = base.requirements

private theorem mapping_prefix {base final : State} {type : Ty}
    (ready : base.InferenceReady) (below : type.VariablesBelow base.inference.next)
    (accepted : unify base.fresh.2.fresh.2 type
      (.mapping base.fresh.1 base.fresh.2.fresh.1) = .ok final) :
    MappingPrefix base final := by
  have key := fresh_eq_inferenceProperties ready (type := base.fresh.1)
    (next := base.fresh.2) rfl
  have value := fresh_eq_inferenceProperties key.2.1 (type := base.fresh.2.fresh.1)
    (next := base.fresh.2.fresh.2) rfl
  have baseBelow := below.weaken (key.1.trans value.1).next_le
  have keyBelow := key.2.2.weaken value.1.next_le
  have mappingBelow := (Ty.variablesBelow_mapping_iff _ _ _).2 ⟨keyBelow,value.2.2⟩
  have unified := unify_inferenceProgress value.2.1.solved baseBelow mappingBelow accepted
  have finalReady := unify_preserves_inferenceReady value.2.1 baseBelow mappingBelow accepted
  have fields := unify_fields accepted
  have occurrences := unify_occurrenceState_eq accepted
  exact ⟨key.1.trans (value.1.trans unified),finalReady,
    finalReady.solved.variablesBelow_apply (keyBelow.weaken unified.next_le),
    value.2.2.weaken unified.next_le,occurrences.1,occurrences.2,fields.1,fields.2⟩

private theorem fresh_formed {semantic : SourceSemantics.Context}
    {context : SourceInference.Context} {outer : Substitution}
    (formation : InferenceFormationContext semantic context outer) (state : State) :
    TypeAdmissible semantic (outer.apply state.fresh.1) :=
  type_applySubstitution_residual formation.residual formation.range
    (.variableOfResidual formation.scope.binders formation.residual ⟨state.inference.next⟩)

theorem inferPlaceFuel_index_formation
    {semantic : SourceSemantics.Context} {outer : Substitution}
    {fuel : Nat} {context : SourceInference.Context} {target base key : Syntax.Expr}
    {brackets : Syntax.SourceSpan} {initial : State}
    (form : target.value = .index base brackets key)
    (baseIH : InferPlaceFuelFormation semantic outer fuel context base initial)
    (keyIH : ∀ keyType state, InferExprFuelFormation semantic outer fuel context key
      (some (state.resolve keyType)) state) :
    InferPlaceFuelFormation semantic outer (fuel + 1) context target initial := by
  intro ready nodes formed formation result accepted continuation noCapture
  unfold inferPlaceFuel at accepted
  simp only [form, bind, Except.bind] at accepted
  cases baseRun : inferPlaceFuel fuel context base initial with
  | error error => simp [baseRun] at accepted
  | ok basePair =>
    rcases basePair with ⟨basePlace,baseState⟩
    simp only [baseRun] at accepted
    cases unified : unify baseState.fresh.2.fresh.2 basePlace.type
        (.mapping baseState.fresh.1 baseState.fresh.2.fresh.1) with
    | error error => simp [unified] at accepted
    | ok unifiedState =>
      simp only [unified] at accepted
      cases keyRun : inferExprFuel fuel context key (some (unifiedState.resolve baseState.fresh.1))
          unifiedState with
      | error error => simp [keyRun] at accepted
      | ok keyPair =>
        rcases keyPair with ⟨keyValue,keyState⟩
        simp only [keyRun, pure, Pure.pure, Except.pure, Except.ok.injEq] at accepted
        subst result
        have baseProperties := inferPlaceFuel_inferenceProperties ready
          formation.validated formation.functionShapes baseRun
        have mappingPrefix := mapping_prefix baseProperties.2.1 baseProperties.2.2 unified
        have baseNodes := (inferPlaceFuel_occurrenceBoundExtends baseRun).nodesBelowNextOccurrence nodes
        have unifiedNodes : unifiedState.NodesBelowNextOccurrence := by
          simpa only [State.NodesBelowNextOccurrence, mappingPrefix.nodes, mappingPrefix.occurrence] using baseNodes
        have expectedBelow : ∀ type ∈ some (unifiedState.resolve baseState.fresh.1),
            type.VariablesBelow unifiedState.inference.next := by
          intro type member
          cases Option.mem_def.mp member
          exact mappingPrefix.keyBelow
        have keyProperties := inferExprFuel_inferenceProperties mappingPrefix.ready
          formation.validated formation.functionShapes expectedBelow keyRun
        have unifiedContinuation := continuation.trans keyProperties.1.substitution_extends
        have basePrefix : baseState.nodes <+: keyState.nodes := by
          rw [← mappingPrefix.nodes]
          exact inferExprFuel_preserves_nodesPrefix keyRun List.prefix_rfl unifiedNodes (Nat.le_refl _)
        have baseFormed := baseIH ready nodes formed formation _ baseRun
          (unifiedContinuation.trans mappingPrefix.progress.substitution_extends)
          (noCapture.of_prefix basePrefix)
        have keyFormed := keyIH baseState.fresh.1 unifiedState mappingPrefix.ready unifiedNodes
          (baseFormed.2.congr mappingPrefix.binders mappingPrefix.requirements) formation expectedBelow
          (by
            intro type member
            cases Option.mem_def.mp member
            exact (unifiedContinuation _).symm ▸ fresh_formed formation baseState)
          _ keyRun continuation noCapture
        exact ⟨(continuation _).symm ▸ fresh_formed formation baseState.fresh.2,keyFormed.2⟩

theorem inferExprFuel_index_formation
    {semantic : SourceSemantics.Context} {outer : Substitution}
    {fuel : Nat} {context : SourceInference.Context} {expression base key : Syntax.Expr}
    {brackets : Syntax.SourceSpan} {expected : Option Ty} {initial : State}
    (form : expression.value = .index base brackets key)
    (baseIH : InferExprFuelFormation semantic outer fuel context base none initial.allocateExpressionId.2)
    (keyIH : ∀ keyType state, InferExprFuelFormation semantic outer fuel context key
      (some (state.resolve keyType)) state) :
    InferExprFuelFormation semantic outer (fuel + 1) context expression expected initial := by
  intro ready nodes formed formation expectedBelow expectedFormed result accepted continuation noCapture
  unfold inferExprFuel at accepted
  simp only [form, bind, Except.bind] at accepted
  cases baseRun : inferExprFuel fuel context base none initial.allocateExpressionId.2 with
  | error error => simp [baseRun] at accepted
  | ok basePair =>
    rcases basePair with ⟨baseValue,baseState⟩
    simp only [baseRun] at accepted
    cases unified : unify baseState.fresh.2.fresh.2 baseValue.type
        (.mapping baseState.fresh.1 baseState.fresh.2.fresh.1) with
    | error error => simp [unified] at accepted
    | ok unifiedState =>
      simp only [unified] at accepted
      cases keyRun : inferExprFuel fuel context key (some (unifiedState.resolve baseState.fresh.1))
          unifiedState with
      | error error => simp [keyRun] at accepted
      | ok keyPair =>
        rcases keyPair with ⟨keyValue,keyState⟩
        simp only [keyRun] at accepted
        have allocation : initial.InferenceProgress initial.allocateExpressionId.2 ∧
            initial.allocateExpressionId.2.InferenceReady :=
          ⟨State.InferenceProgress.allocateExpressionId initial ready.solved, ready.allocateExpressionId⟩
        have allocatedNodes := (State.OccurrenceBoundExtends.allocateExpressionId initial).nodesBelowNextOccurrence nodes
        have baseProperties := inferExprFuel_inferenceProperties allocation.2
          formation.validated formation.functionShapes (by simp) baseRun
        have mappingPrefix := mapping_prefix baseProperties.2.1 baseProperties.2.2 unified
        have baseNodes := (inferExprFuel_occurrenceBoundExtends baseRun).nodesBelowNextOccurrence allocatedNodes
        have unifiedNodes : unifiedState.NodesBelowNextOccurrence := by
          simpa only [State.NodesBelowNextOccurrence, mappingPrefix.nodes, mappingPrefix.occurrence] using baseNodes
        have keyExpectedBelow : ∀ type ∈ some (unifiedState.resolve baseState.fresh.1),
            type.VariablesBelow unifiedState.inference.next := by
          intro type member
          cases Option.mem_def.mp member
          exact mappingPrefix.keyBelow
        have keyProperties := inferExprFuel_inferenceProperties mappingPrefix.ready
          formation.validated formation.functionShapes keyExpectedBelow keyRun
        have throughKey := allocation.1.trans
          (baseProperties.1.trans (mappingPrefix.progress.trans keyProperties.1))
        have valueBelow := keyProperties.1.resolve_variablesBelow mappingPrefix.valueBelow
        have expectedAtKey : ∀ type ∈ expected, type.VariablesBelow keyState.inference.next :=
          fun type member => (expectedBelow type member).weaken throughKey.next_le
        have recorded := recordExpressionWithExpected_inferenceProperties keyProperties.2.1
          valueBelow expectedAtKey accepted
        have recordFields := recording_fields accepted
        have keyContinuation := continuation.trans recorded.1.substitution_extends
        have unifiedContinuation := keyContinuation.trans keyProperties.1.substitution_extends
        have keyNoCapture := noCapture.of_prefix recordFields.2
        have basePrefix : baseState.nodes <+: keyState.nodes := by
          rw [← mappingPrefix.nodes]
          exact inferExprFuel_preserves_nodesPrefix keyRun List.prefix_rfl unifiedNodes (Nat.le_refl _)
        have baseFormed := baseIH allocation.2 allocatedNodes (formed.congr rfl rfl) formation
          (by simp) (by simp) _ baseRun (unifiedContinuation.trans mappingPrefix.progress.substitution_extends)
          (keyNoCapture.of_prefix basePrefix)
        have keyFormed := keyIH baseState.fresh.1 unifiedState mappingPrefix.ready unifiedNodes
          (baseFormed.2.congr mappingPrefix.binders mappingPrefix.requirements) formation keyExpectedBelow
          (by
            intro type member
            cases Option.mem_def.mp member
            exact (unifiedContinuation _).symm ▸ fresh_formed formation baseState)
          _ keyRun keyContinuation keyNoCapture
        have fitted := recordExpressionWithExpected_normalized_formation formation.toFormationContext continuation
          ((keyContinuation _).symm ▸ fresh_formed formation baseState.fresh.2) expectedFormed accepted
        exact ⟨fitted.1,keyFormed.2.of_new_rows recordFields.1 fitted.2⟩

end Solcore.SourceSemantics.SourceInferenceNormalizedCoercionFormation
end
