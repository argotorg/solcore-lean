import Solcore.SourceSemantics.SourceInferenceSelectedExpressionList
import Solcore.SourceSemantics.SourceInferenceSelectedOrdinaryRecorder

set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceSoundness
open Frontend Frontend.SourceInference TypeSystem

private theorem fresh_eq_typingSourceExtends
    {initial final : Frontend.SourceInference.State}
    {type : TypeSystem.Ty}
    (success : initial.fresh = (type, final))
    (roots : List NodeId := []) :
    TypingSourceExtends (initial.toTypedSource roots)
      (final.toTypedSource roots) := by
  have finalEq : initial.fresh.2 = final := congrArg Prod.snd success
  rw [← finalEq]
  exact .refl _

private theorem fresh_eq_integerLiterals_eq
    {initial final : Frontend.SourceInference.State}
    {type : TypeSystem.Ty}
    (success : initial.fresh = (type, final)) :
    final.integerLiterals = initial.integerLiterals := by
  have finalEq : initial.fresh.2 = final := congrArg Prod.snd success
  rw [← finalEq]
  rfl

private theorem fresh_eq_integerPatterns_eq
    {initial final : Frontend.SourceInference.State}
    {type : TypeSystem.Ty}
    (success : initial.fresh = (type, final)) :
    final.integerPatterns = initial.integerPatterns := by
  have finalEq : initial.fresh.2 = final := congrArg Prod.snd success
  rw [← finalEq]
  rfl

private theorem fresh_eq_requirements_eq
    {initial final : Frontend.SourceInference.State}
    {type : TypeSystem.Ty}
    (success : initial.fresh = (type, final)) :
    final.requirements = initial.requirements := by
  have finalEq : initial.fresh.2 = final := congrArg Prod.snd success
  rw [← finalEq]
  rfl

private theorem unify_success_typingSourceExtends
    {initial final : Frontend.SourceInference.State}
    {left right : TypeSystem.Ty}
    (success : Detail.unify initial left right = .ok final)
    (roots : List NodeId := []) :
    TypingSourceExtends (initial.toTypedSource roots)
      (final.toTypedSource roots) := by
  constructor
  · change final.owner = initial.owner
    have headerEq := Detail.unify_state_header success
    simpa [Frontend.SourceInference.State.header] using
      congrArg Frontend.SourceInference.State.Header.owner headerEq
  · change initial.nodes <+: final.nodes
    rw [(Detail.unify_occurrenceState_eq success).1]
    exact List.prefix_rfl

theorem actualInferExprFuelRetainedSoundness_index {fuel : Nat}
    (recursive : ActualInferExprFuelRetainedSoundness fuel) :
  ∀ {wholeContext inferenceContext : Frontend.SourceInference.Context}
    {wholeReturn : Ty} {expression baseExpression indexExpression : Syntax.Expr}
    {brackets : Syntax.SourceSpan} {expected : Option Ty}
    {initial resultState evidenceState : State}
    {inferred : InferredExpression} {roots : List NodeId}
    {finalized : Frontend.SourceInference.Result}
    {semanticSource : TypedSource}
    {frames : List InitializedLetBinding}
    {semanticContext : SourceSemantics.Context},
    expression.value = .index baseExpression brackets indexExpression →
    Detail.inferExprFuel (fuel + 1) inferenceContext expression expected initial =
        .ok (inferred, resultState) →
    FinalInferenceResources wholeContext wholeReturn evidenceState roots
      finalized →
    ExecutableCoercionInterfaces.SourceInterfaces wholeContext.signatures
      finalized.solvedRequirements finalized.typedSource →
    finalized.substitution.SemanticallyExtends
      resultState.inference.substitution →
    inferenceContext.signatures = wholeContext.signatures →
    inferenceContext.scope.genericOwner = wholeContext.scope.genericOwner →
    inferenceContext.typeParameters = wholeContext.typeParameters →
    inferenceContext.assumptions = wholeContext.assumptions →
    ProgramSignatureFormationValidated inferenceContext.signatures →
    (∀ candidate ∈ inferenceContext.signatures.functions,
      candidate.scheme.body = .function
        (Ty.productMany candidate.parameterTypes)
        (Ty.productMany candidate.returnTypes)) →
    SignatureCatalogWellFormed inferenceContext.signatures →
    SignatureParametersWellFormed inferenceContext.scope.genericOwner
      inferenceContext.typeParameters →
    RecursiveExpressionInvariant wholeContext finalized initial
      semanticContext →
    ActualContext wholeContext finalized frames semanticContext →
    ActualStateInvariant initial (evidenceState.toTypedSource roots) →
    (∀ expectedType ∈ expected,
      expectedType.VariablesBelow initial.inference.next) →
    (∀ expectedType ∈ expected,
      TypeAdmissible semanticContext (finalized.substitution.apply expectedType)) →
    ProperDescendantsPreserved finalized.substitution
      (resultState.toTypedSource roots) finalized.typedSource
      (.expression inferred.id) →
    RawProperDescendantsPreserved (resultState.toTypedSource roots)
      (evidenceState.toTypedSource roots) (.expression inferred.id) →
    resultState.integerPatterns ⊆ evidenceState.integerPatterns →
    resultState.integerLiterals ⊆ evidenceState.integerLiterals →
    resultState.requirements ⊆ evidenceState.requirements →
    ExpressionRequirementsRetainedAt
      (resultState.toTypedSource roots) finalized.typedSource inferred.id →
    ExpressionCoercionPrimariesRetainedAt
      (resultState.toTypedSource roots) finalized.typedSource inferred.id →
    ExpressionOperatorSiteRetainedAt
      (resultState.toTypedSource roots) finalized.typedSource inferred.id →
    ExpressionDirectChildrenRetainedAt
      (resultState.toTypedSource roots) finalized.typedSource inferred.id →
    TemplateScopeCovered finalized.typedSource semanticContext
      (.expression inferred.id) →
    ProperDescendantsPreserved finalized.substitution (resultState.toTypedSource roots)
      semanticSource (.expression inferred.id) →
    ActualContext.Covers finalized frames (.expression inferred.id) →
    ExpressionTypingBase (resultState.toTypedSource roots) semanticSource
      semanticContext finalized.substitution inferred := by
  intro wholeContext inferenceContext wholeReturn expression baseExpression indexExpression brackets expected initial
    resultState evidenceState inferred roots finalized semanticSource
    frames semanticContext expressionEq success resources interfaces resultSubstitutionExtension signaturesEq
    ownerEq typeParametersEq assumptionsEq signatureFormation
    functionsCanonical catalog canonical invariant actual operational expectedBelow expectedAdmissible
    finalPreserved rawProper integerPatternsSubset integerLiteralsSubset requirementsSubset
    retained coercionsRetained _operatorsRetained childrenRetained covered semanticPreserved actualCovered
  generalize allocationEq : initial.allocateExpressionId = allocatedPair
  rcases allocatedPair with ⟨id, allocated⟩
  have allocatedInvariant := invariant.allocateExpressionId allocationEq
  have allocatedOperational : ActualStateInvariant allocated (evidenceState.toTypedSource roots) := by
    obtain ⟨pending, ledger⟩ := operational.ledger
    have stateEq : initial.allocateExpressionId.2 = allocated := congrArg Prod.snd allocationEq
    refine ⟨⟨pending, ?_⟩, ?_, ?_⟩
    · rw [← stateEq]
      exact ledger.allocateExpressionId
    · apply operational.origins.congr_localBinders
      rw [← stateEq]
      rfl
    · apply activeQuantifiersBelowNext_transport operational.quantifiersBelow
      · rw [← stateEq]; rfl
      · rw [← stateEq]; exact Nat.le_refl _
  have allocatedExpected : ∀ type ∈ expected, type.VariablesBelow allocated.inference.next := by
    rw [allocateExpressionId_inferenceNext_eq allocationEq]
    exact expectedBelow
  obtain ⟨baseResult, baseState, keyType, keyState, valueType, valueState,
      mappingState, indexResult, indexState, baseSuccess, keyFresh, valueFresh,
      mappingSuccess, indexSuccess, recorded⟩ :=
    Detail.inferExprFuel_success_index_facts expressionEq allocationEq success
  have baseProperties := Detail.inferExprFuel_inferenceProperties
    allocatedInvariant.ready signatureFormation functionsCanonical (by
      intro expectedType member
      simp at member) baseSuccess
  have keyProperties := Detail.fresh_eq_inferenceProperties
    baseProperties.2.1 keyFresh
  have valueProperties := Detail.fresh_eq_inferenceProperties
    keyProperties.2.1 valueFresh
  have baseAtValue : baseResult.type.VariablesBelow
      valueState.inference.next :=
    baseProperties.2.2.weaken
      (keyProperties.1.trans valueProperties.1).next_le
  have keyAtValue : keyType.VariablesBelow valueState.inference.next :=
    keyProperties.2.2.weaken valueProperties.1.next_le
  have mappingBelow : (TypeSystem.Ty.mapping keyType valueType).VariablesBelow
      valueState.inference.next :=
    (TypeSystem.Ty.variablesBelow_mapping_iff _ _ _).2
      ⟨keyAtValue, valueProperties.2.2⟩
  have unifyProgress := Detail.unify_inferenceProgress
    valueProperties.2.1.solved baseAtValue mappingBelow mappingSuccess
  have mappingReady := Detail.unify_preserves_inferenceReady
    valueProperties.2.1 baseAtValue mappingBelow mappingSuccess
  have keyAtMapping : keyType.VariablesBelow mappingState.inference.next :=
    keyAtValue.weaken unifyProgress.next_le
  have resolvedKeyBelow :
      (mappingState.resolve keyType).VariablesBelow
        mappingState.inference.next :=
    mappingReady.solved.variablesBelow_apply keyAtMapping
  have indexProperties := Detail.inferExprFuel_inferenceProperties
    mappingReady signatureFormation functionsCanonical (by
      intro expectedType member
      simp only [Option.mem_def] at member
      have expectedTypeEq : expectedType = mappingState.resolve keyType :=
        (Option.some.inj member).symm
      rw [expectedTypeEq]
      exact resolvedKeyBelow) indexSuccess
  have allocatedToIndex : allocated.InferenceProgress indexState :=
    baseProperties.1.trans
      (keyProperties.1.trans
        (valueProperties.1.trans
          (unifyProgress.trans indexProperties.1)))
  have expectedAtIndex : ∀ expectedType ∈ expected,
      expectedType.VariablesBelow indexState.inference.next := by
    intro expectedType member
    exact (allocatedExpected expectedType member).weaken allocatedToIndex.next_le
  have valueAtIndex : valueType.VariablesBelow indexState.inference.next :=
    valueProperties.2.2.weaken
      (unifyProgress.trans indexProperties.1).next_le
  have resolvedValueBelow :
      (indexState.resolve valueType).VariablesBelow
        indexState.inference.next :=
    indexProperties.2.1.solved.variablesBelow_apply valueAtIndex
  have recordedProperties :=
    Detail.recordExpressionWithExpected_inferenceProperties
      indexProperties.2.1 resolvedValueBelow expectedAtIndex recorded
  have laterIndex : finalized.substitution.SemanticallyExtends
      indexState.inference.substitution :=
    TypeSystem.Substitution.SemanticallyExtends.trans resultSubstitutionExtension
      recordedProperties.1.substitution_extends
  have laterMapping : finalized.substitution.SemanticallyExtends
      mappingState.inference.substitution :=
    TypeSystem.Substitution.SemanticallyExtends.trans laterIndex
      indexProperties.1.substitution_extends
  have allocatedBelow := allocatedInvariant.nodesBelow
  have baseBelow : baseState.NodesBelowNextOccurrence :=
    (Detail.inferExprFuel_occurrenceBoundExtends baseSuccess
      ).nodesBelowNextOccurrence allocatedBelow
  have keyBelow : keyState.NodesBelowNextOccurrence := by
    have below :=
      Frontend.SourceInference.State.fresh_preserves_nodesBelowNextOccurrence
        baseState baseBelow
    have stateEq : baseState.fresh.2 = keyState := congrArg Prod.snd keyFresh
    simpa [stateEq] using below
  have valueBelow : valueState.NodesBelowNextOccurrence := by
    have below :=
      Frontend.SourceInference.State.fresh_preserves_nodesBelowNextOccurrence
        keyState keyBelow
    have stateEq : keyState.fresh.2 = valueState :=
      congrArg Prod.snd valueFresh
    simpa [stateEq] using below
  have mappingNodesBelow : mappingState.NodesBelowNextOccurrence :=
    (Detail.unify_occurrenceBoundExtends mappingSuccess
      ).nodesBelowNextOccurrence valueBelow
  have indexBelow : indexState.NodesBelowNextOccurrence :=
    (Detail.inferExprFuel_occurrenceBoundExtends indexSuccess
      ).nodesBelowNextOccurrence mappingNodesBelow
  have baseToKey := fresh_eq_typingSourceExtends keyFresh roots
  have keyToValue := fresh_eq_typingSourceExtends valueFresh roots
  have valueToMapping := unify_success_typingSourceExtends mappingSuccess roots
  have mappingToIndex :=
    inferExprFuel_success_typingSourceExtends indexSuccess mappingNodesBelow roots
  have allocatedOwner : allocated.owner = initial.owner := by
    have stateEq : initial.allocateExpressionId.2 = allocated :=
      congrArg Prod.snd allocationEq
    rw [← stateEq]
    rfl
  have baseOwner : baseState.owner = allocated.owner :=
    Detail.inferExprFuel_preserves_owner baseSuccess
  have parentOwner : resultState.owner = initial.owner :=
    Detail.inferExprFuel_preserves_owner success
  have indexToParent : TypingSourceExtends
      (indexState.toTypedSource roots) (resultState.toTypedSource roots) := by
    constructor
    · exact parentOwner.trans
        (allocatedOwner.symm.trans
          (baseOwner.symm.trans
            (baseToKey.owner_eq.symm.trans
              (keyToValue.owner_eq.symm.trans
                (valueToMapping.owner_eq.symm.trans
                  mappingToIndex.owner_eq.symm)))))
    · exact recordExpressionWithExpected_success_nodesPrefix recorded
  have baseToParent :=
    TypingSourceExtends.trans baseToKey
      (TypingSourceExtends.trans keyToValue
        (TypingSourceExtends.trans valueToMapping
          (TypingSourceExtends.trans mappingToIndex indexToParent)))
  have indexIntegerLiteralsSubset :
      indexState.integerLiterals ⊆ resultState.integerLiterals := by
    intro origin member
    rw [Detail.recordExpressionWithExpected_integerLiterals_eq recorded]
    exact member
  have mappingIntegerLiteralsSubset :
      mappingState.integerLiterals ⊆ resultState.integerLiterals :=
    List.Subset.trans
      (Detail.inferExprFuel_integerLiterals_subset indexSuccess)
      indexIntegerLiteralsSubset
  have valueIntegerLiteralsSubset :
      valueState.integerLiterals ⊆ resultState.integerLiterals := by
    intro origin member
    apply mappingIntegerLiteralsSubset
    rw [Detail.unify_integerLiterals mappingSuccess]
    exact member
  have keyIntegerLiteralsSubset :
      keyState.integerLiterals ⊆ resultState.integerLiterals := by
    intro origin member
    apply valueIntegerLiteralsSubset
    rw [fresh_eq_integerLiterals_eq valueFresh]
    exact member
  have baseIntegerLiteralsSubset :
      baseState.integerLiterals ⊆ resultState.integerLiterals := by
    intro origin member
    apply keyIntegerLiteralsSubset
    rw [fresh_eq_integerLiterals_eq keyFresh]
    exact member
  have indexIntegerPatternsSubset :
      indexState.integerPatterns ⊆ resultState.integerPatterns := by
    intro origin member
    rw [recordExpressionWithExpected_integerPatterns_eq recorded]
    exact member
  have mappingIntegerPatternsSubset :
      mappingState.integerPatterns ⊆ resultState.integerPatterns :=
    List.Subset.trans
      (Detail.inferExprFuel_integerPatterns_subset indexSuccess)
      indexIntegerPatternsSubset
  have valueIntegerPatternsSubset :
      valueState.integerPatterns ⊆ resultState.integerPatterns := by
    intro origin member
    apply mappingIntegerPatternsSubset
    rw [(Detail.unify_integerPatternMetadata_eq mappingSuccess).1]
    exact member
  have keyIntegerPatternsSubset :
      keyState.integerPatterns ⊆ resultState.integerPatterns := by
    intro origin member
    apply valueIntegerPatternsSubset
    rw [fresh_eq_integerPatterns_eq valueFresh]
    exact member
  have baseIntegerPatternsSubset :
      baseState.integerPatterns ⊆ resultState.integerPatterns := by
    intro origin member
    apply keyIntegerPatternsSubset
    rw [fresh_eq_integerPatterns_eq keyFresh]
    exact member
  have indexRequirementsSubset :
      indexState.requirements ⊆ resultState.requirements :=
    Detail.recordExpressionWithExpected_requirements_subset recorded
  have mappingRequirementsSubset :
      mappingState.requirements ⊆ resultState.requirements :=
    List.Subset.trans
      (Detail.inferExprFuel_requirements_subset indexSuccess)
      indexRequirementsSubset
  have valueRequirementsSubset :
      valueState.requirements ⊆ resultState.requirements := by
    intro requirement member
    apply mappingRequirementsSubset
    rw [Detail.unify_requirements_eq mappingSuccess]
    exact member
  have keyRequirementsSubset :
      keyState.requirements ⊆ resultState.requirements := by
    intro requirement member
    apply valueRequirementsSubset
    rw [fresh_eq_requirements_eq valueFresh]
    exact member
  have baseRequirementsSubset :
      baseState.requirements ⊆ resultState.requirements := by
    intro requirement member
    apply keyRequirementsSubset
    rw [fresh_eq_requirements_eq keyFresh]
    exact member
  have laterValue := laterMapping.trans unifyProgress.substitution_extends
  have laterKey := laterValue.trans valueProperties.1.substitution_extends
  have laterBase := laterKey.trans keyProperties.1.substitution_extends
  have baseInvariant := allocatedInvariant.ofExpression signatureFormation functionsCanonical
    (by simp) laterBase baseSuccess
  have keyEq : baseState.fresh.2 = keyState := congrArg Prod.snd keyFresh
  have valueEq : keyState.fresh.2 = valueState := congrArg Prod.snd valueFresh
  have keyInvariant : RecursiveExpressionInvariant wholeContext finalized keyState semanticContext := by
    simpa only [keyEq] using baseInvariant.fresh (by simpa only [keyEq] using laterKey)
  have valueInvariant : RecursiveExpressionInvariant wholeContext finalized valueState semanticContext := by
    simpa only [valueEq] using keyInvariant.fresh (by simpa only [valueEq] using laterValue)
  have mappingInvariant := valueInvariant.unify baseAtValue mappingBelow laterMapping mappingSuccess
  have baseOperational := allocatedOperational.ofExpression baseSuccess baseProperties.1.next_le
  have keyOperational : ActualStateInvariant keyState (evidenceState.toTypedSource roots) := by
    simpa only [keyEq] using baseOperational.fresh
  have valueOperational : ActualStateInvariant valueState (evidenceState.toTypedSource roots) := by
    simpa only [valueEq] using keyOperational.fresh
  have mappingOperational := valueOperational.unify mappingSuccess
  have indexExpected : ∀ type ∈ (some (mappingState.resolve keyType) : Option Ty),
      type.VariablesBelow mappingState.inference.next := by
    intro type member
    have same : type = mappingState.resolve keyType := (Option.some.inj member).symm
    subst type
    exact resolvedKeyBelow
  obtain ⟨coercions, contains⟩ := recordExpressionWithExpected_success_containsExpression recorded roots
  have edge : ∀ child ∈ [baseResult.id, indexResult.id],
      DirectChild (resultState.toTypedSource roots) (.expression inferred.id) (.expression child) := by
    intro child member
    refine ⟨.expression _, ⟨contains.1, rfl⟩, ?_⟩
    simpa [nodeChildIds, Node.references, ExpressionForm.references] using
      (List.mem_map.mpr ⟨child, member, rfl⟩ : NodeId.expression child ∈
        [baseResult.id, indexResult.id].map NodeId.expression)
  have baseEdge := edge baseResult.id (by simp)
  have baseTypeRaw := actualInferExprFuelFinalSubtreeSoundness_of_retainedSoundness recursive
    baseSuccess resources interfaces laterBase signaturesEq ownerEq typeParametersEq assumptionsEq
    signatureFormation functionsCanonical catalog canonical allocatedInvariant actual allocatedOperational (by simp) (by simp)
    ((semanticPreserved.childSubtree baseEdge).monoBefore baseToParent)
    ((finalPreserved.childSubtree baseEdge).monoBefore baseToParent)
    ((rawProper.childSubtree baseEdge).monoBefore baseToParent).proper
    (List.Subset.trans baseIntegerPatternsSubset integerPatternsSubset)
    (List.Subset.trans baseIntegerLiteralsSubset integerLiteralsSubset)
    (List.Subset.trans baseRequirementsSubset requirementsSubset)
    (covered.expressionChild resources.graph_closed (childrenRetained baseEdge))
    (actualCovered.directChild (childrenRetained baseEdge))
  have unifiedEq : mappingState.resolve baseResult.type =
      mappingState.resolve (.mapping keyType valueType) := by
    simpa [Frontend.SourceInference.State.resolve] using
      Detail.unify_resolve_eq mappingSuccess
  have resolvedBaseEq :
      finalized.substitution.apply
          (mappingState.resolve baseResult.type) =
        finalized.substitution.apply baseResult.type := by
    simpa [Frontend.SourceInference.State.resolve,
      TypeSystem.InferState.resolve] using laterMapping baseResult.type
  have resolvedMappingEq :
      finalized.substitution.apply
          (mappingState.resolve (.mapping keyType valueType)) =
        finalized.substitution.apply (.mapping keyType valueType) := by
    simpa [Frontend.SourceInference.State.resolve,
      TypeSystem.InferState.resolve] using
        laterMapping (.mapping keyType valueType)
  have baseEq : finalized.substitution.apply baseResult.type =
      .mapping (finalized.substitution.apply keyType)
        (finalized.substitution.apply valueType) := by
    calc
      finalized.substitution.apply baseResult.type =
          finalized.substitution.apply
            (mappingState.resolve baseResult.type) := resolvedBaseEq.symm
      _ = finalized.substitution.apply
          (mappingState.resolve (.mapping keyType valueType)) :=
        congrArg finalized.substitution.apply unifiedEq
      _ = finalized.substitution.apply
          (.mapping keyType valueType) := resolvedMappingEq
      _ = .mapping (finalized.substitution.apply keyType)
          (finalized.substitution.apply valueType) := rfl
  have resolvedKeyEq :
      finalized.substitution.apply (mappingState.resolve keyType) =
        finalized.substitution.apply keyType := by
    simpa [Frontend.SourceInference.State.resolve,
      TypeSystem.InferState.resolve] using laterMapping keyType
  have indexEdge := edge indexResult.id (by simp)
  have indexTypeRaw := actualInferExprFuelFinalSubtreeSoundness_of_retainedSoundness recursive
    indexSuccess resources interfaces laterIndex signaturesEq ownerEq typeParametersEq assumptionsEq
    signatureFormation functionsCanonical catalog canonical mappingInvariant actual mappingOperational indexExpected
    (by
      intro type member
      have same : type = mappingState.resolve keyType := (Option.some.inj member).symm
      subst type
      rw [resolvedKeyEq]
      have baseAdmissible := baseTypeRaw.type_admissible
      rw [baseEq] at baseAdmissible
      exact TypeAdmissible.mapping_key baseAdmissible)
    ((semanticPreserved.childSubtree indexEdge).monoBefore indexToParent)
    ((finalPreserved.childSubtree indexEdge).monoBefore indexToParent)
    ((rawProper.childSubtree indexEdge).monoBefore indexToParent).proper
    (List.Subset.trans indexIntegerPatternsSubset integerPatternsSubset)
    (List.Subset.trans indexIntegerLiteralsSubset integerLiteralsSubset)
    (List.Subset.trans indexRequirementsSubset requirementsSubset)
    (covered.expressionChild resources.graph_closed (childrenRetained indexEdge))
    (actualCovered.directChild (childrenRetained indexEdge))
  have indexExpectedEq :
      finalized.substitution.apply indexResult.type =
        finalized.substitution.apply
          (mappingState.resolve keyType) :=
    Detail.inferExprFuel_expected_type_apply_eq indexSuccess laterIndex
  have resolvedValueEq :
      finalized.substitution.apply (indexState.resolve valueType) =
        finalized.substitution.apply valueType := by
    simpa [Frontend.SourceInference.State.resolve,
      TypeSystem.InferState.resolve] using laterIndex valueType
  have baseType : ExpressionHasType semanticSource semanticContext baseResult.id
      (.mapping (finalized.substitution.apply keyType)
        (finalized.substitution.apply valueType)) := by
    rw [← baseEq]
    exact baseTypeRaw
  have indexType : ExpressionHasType semanticSource semanticContext indexResult.id
      (finalized.substitution.apply keyType) := by
    rw [← resolvedKeyEq, ← indexExpectedEq]
    exact indexTypeRaw
  have formType : ExpressionFormHasRawType semanticSource semanticContext
      ((ExpressionForm.index baseResult.id indexResult.id).applySubstitution
        finalized.substitution)
      (finalized.substitution.apply (indexState.resolve valueType))
      (.ordinary []) := by
    rw [resolvedValueEq]
    simpa [ExpressionForm.applySubstitution] using
      ExpressionFormHasRawType.index baseType indexType
  have rawAdmissible : TypeAdmissible semanticContext
      (finalized.substitution.apply (indexState.resolve valueType)) := by
    rw [resolvedValueEq]
    exact TypeAdmissible.mapping_value baseType.type_admissible
  exact recordExpressionWithExpected_success_expressionTypingBase_actual resources interfaces
    recorded resultSubstitutionExtension requirementsSubset retained coercionsRetained
    catalog signaturesEq invariant formType rawAdmissible covered

end Solcore.SourceSemantics.SourceInferenceSoundness
