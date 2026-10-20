import Solcore.SourceSemantics.SourceInferenceNormalizedContracts

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
