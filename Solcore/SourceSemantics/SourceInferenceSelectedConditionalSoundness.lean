import Solcore.SourceSemantics.SourceInferenceSelectedExpressionList
import Solcore.SourceSemantics.SourceInferenceSelectedOrdinaryRecorder

set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceSoundness
open Frontend Frontend.SourceInference TypeSystem

theorem actualInferExprFuelRetainedSoundness_conditional {fuel : Nat}
    (recursive : ActualInferExprFuelRetainedSoundness fuel) :
  ∀ {wholeContext inferenceContext : Frontend.SourceInference.Context}
    {wholeReturn : Ty} {expression condition thenBranch elseBranch : Syntax.Expr}
    {question colon : Syntax.SourceSpan} {expected : Option Ty}
    {initial resultState evidenceState : State}
    {inferred : InferredExpression} {roots : List NodeId}
    {finalized : Frontend.SourceInference.Result}
    {semanticSource : TypedSource}
    {frames : List InitializedLetBinding}
    {semanticContext : SourceSemantics.Context},
    expression.value = .conditional condition question thenBranch colon elseBranch →
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
  intro wholeContext inferenceContext wholeReturn expression condition thenBranch elseBranch question colon expected initial
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
  obtain ⟨conditionResult, conditionState, thenResult, thenState, elseResult,
      elseState, unifiedState, conditionSuccess, thenSuccess, elseSuccess,
      unifySuccess, recorded⟩ :=
    Detail.inferExprFuel_success_conditional_facts expressionEq allocationEq
      success
  have conditionProperties := Detail.inferExprFuel_inferenceProperties
    allocatedInvariant.ready signatureFormation functionsCanonical (by
      intro expectedType member
      simp only [Option.mem_def] at member
      have expectedTypeEq : expectedType = .bool :=
        (Option.some.inj member).symm
      rw [expectedTypeEq]
      change TypeSystem.Ty.VariablesBelow allocated.inference.next
        (.constructor (.builtin .bool))
      exact TypeSystem.Ty.variablesBelow_constructor _ _) conditionSuccess
  have expectedAtCondition : ∀ expectedType ∈ expected,
      expectedType.VariablesBelow conditionState.inference.next := by
    intro expectedType member
    exact (allocatedExpected expectedType member).weaken
      conditionProperties.1.next_le
  have thenProperties := Detail.inferExprFuel_inferenceProperties
    conditionProperties.2.1 signatureFormation functionsCanonical
      expectedAtCondition thenSuccess
  have expectedAtThen : ∀ expectedType ∈ expected,
      expectedType.VariablesBelow thenState.inference.next := by
    intro expectedType member
    exact (expectedAtCondition expectedType member).weaken
      thenProperties.1.next_le
  have elseProperties := Detail.inferExprFuel_inferenceProperties
    thenProperties.2.1 signatureFormation functionsCanonical expectedAtThen
      elseSuccess
  have thenAtElse : thenResult.type.VariablesBelow
      elseState.inference.next :=
    thenProperties.2.2.weaken elseProperties.1.next_le
  have unifyProgress := Detail.unify_inferenceProgress
    elseProperties.2.1.solved thenAtElse elseProperties.2.2 unifySuccess
  have unifiedReady := Detail.unify_preserves_inferenceReady
    elseProperties.2.1 thenAtElse elseProperties.2.2 unifySuccess
  have allocatedToUnified : allocated.InferenceProgress unifiedState :=
    conditionProperties.1.trans
      (thenProperties.1.trans (elseProperties.1.trans unifyProgress))
  have expectedAtUnified : ∀ expectedType ∈ expected,
      expectedType.VariablesBelow unifiedState.inference.next := by
    intro expectedType member
    exact (allocatedExpected expectedType member).weaken
      allocatedToUnified.next_le
  have thenAtUnified : thenResult.type.VariablesBelow
      unifiedState.inference.next :=
    thenAtElse.weaken unifyProgress.next_le
  have resolvedThenBelow :
      (unifiedState.resolve thenResult.type).VariablesBelow
        unifiedState.inference.next :=
    unifiedReady.solved.variablesBelow_apply thenAtUnified
  have recordedProperties :=
    Detail.recordExpressionWithExpected_inferenceProperties unifiedReady
      resolvedThenBelow expectedAtUnified recorded
  have laterUnified : finalized.substitution.SemanticallyExtends
      unifiedState.inference.substitution :=
    TypeSystem.Substitution.SemanticallyExtends.trans resultSubstitutionExtension
      recordedProperties.1.substitution_extends
  have laterElse : finalized.substitution.SemanticallyExtends
      elseState.inference.substitution :=
    TypeSystem.Substitution.SemanticallyExtends.trans laterUnified
      unifyProgress.substitution_extends
  have laterThen : finalized.substitution.SemanticallyExtends
      thenState.inference.substitution :=
    TypeSystem.Substitution.SemanticallyExtends.trans laterElse
      elseProperties.1.substitution_extends
  have laterCondition : finalized.substitution.SemanticallyExtends
      conditionState.inference.substitution :=
    TypeSystem.Substitution.SemanticallyExtends.trans laterThen
      thenProperties.1.substitution_extends
  have allocatedBelow := allocatedInvariant.nodesBelow
  have conditionBelow : conditionState.NodesBelowNextOccurrence :=
    (Detail.inferExprFuel_occurrenceBoundExtends conditionSuccess
      ).nodesBelowNextOccurrence allocatedBelow
  have thenBelow : thenState.NodesBelowNextOccurrence :=
    (Detail.inferExprFuel_occurrenceBoundExtends thenSuccess
      ).nodesBelowNextOccurrence conditionBelow
  have elseBelow : elseState.NodesBelowNextOccurrence :=
    (Detail.inferExprFuel_occurrenceBoundExtends elseSuccess
      ).nodesBelowNextOccurrence thenBelow
  have unifiedBelow : unifiedState.NodesBelowNextOccurrence :=
    (Detail.unify_occurrenceBoundExtends unifySuccess
      ).nodesBelowNextOccurrence elseBelow
  have conditionToThen :=
    inferExprFuel_success_typingSourceExtends thenSuccess conditionBelow roots
  have thenToElse :=
    inferExprFuel_success_typingSourceExtends elseSuccess thenBelow roots
  have elseToUnified : TypingSourceExtends
      (elseState.toTypedSource roots) (unifiedState.toTypedSource roots) := by
    constructor
    · change unifiedState.owner = elseState.owner
      have headerEq := Detail.unify_state_header unifySuccess
      simpa [Frontend.SourceInference.State.header] using
        congrArg Frontend.SourceInference.State.Header.owner headerEq
    · change elseState.nodes <+: unifiedState.nodes
      rw [(Detail.unify_occurrenceState_eq unifySuccess).1]
      exact List.prefix_rfl
  have allocatedOwner : allocated.owner = initial.owner := by
    have stateEq : initial.allocateExpressionId.2 = allocated :=
      congrArg Prod.snd allocationEq
    rw [← stateEq]
    rfl
  have conditionOwner : conditionState.owner = allocated.owner :=
    Detail.inferExprFuel_preserves_owner conditionSuccess
  have thenOwner : thenState.owner = conditionState.owner :=
    Detail.inferExprFuel_preserves_owner thenSuccess
  have elseOwner : elseState.owner = thenState.owner :=
    Detail.inferExprFuel_preserves_owner elseSuccess
  have unifiedOwner : unifiedState.owner = elseState.owner := by
    have headerEq := Detail.unify_state_header unifySuccess
    simpa [Frontend.SourceInference.State.header] using
      congrArg Frontend.SourceInference.State.Header.owner headerEq
  have parentOwner : resultState.owner = initial.owner :=
    Detail.inferExprFuel_preserves_owner success
  have unifiedToParent : TypingSourceExtends
      (unifiedState.toTypedSource roots) (resultState.toTypedSource roots) := by
    constructor
    · exact parentOwner.trans
        (allocatedOwner.symm.trans
          (conditionOwner.symm.trans
            (thenOwner.symm.trans
              (elseOwner.symm.trans unifiedOwner.symm))))
    · exact recordExpressionWithExpected_success_nodesPrefix recorded
  have conditionToParent :=
    TypingSourceExtends.trans conditionToThen
      (TypingSourceExtends.trans thenToElse
        (TypingSourceExtends.trans elseToUnified unifiedToParent))
  have thenToParent :=
    TypingSourceExtends.trans thenToElse
      (TypingSourceExtends.trans elseToUnified unifiedToParent)
  have elseToParent :=
    TypingSourceExtends.trans elseToUnified unifiedToParent
  have unifiedIntegerLiteralsSubset :
      unifiedState.integerLiterals ⊆ resultState.integerLiterals := by
    intro origin member
    rw [Detail.recordExpressionWithExpected_integerLiterals_eq recorded]
    exact member
  have elseIntegerLiteralsSubset :
      elseState.integerLiterals ⊆ resultState.integerLiterals := by
    intro origin member
    apply unifiedIntegerLiteralsSubset
    rw [Detail.unify_integerLiterals unifySuccess]
    exact member
  have thenIntegerLiteralsSubset :
      thenState.integerLiterals ⊆ resultState.integerLiterals :=
    List.Subset.trans
      (Detail.inferExprFuel_integerLiterals_subset elseSuccess)
      elseIntegerLiteralsSubset
  have conditionIntegerLiteralsSubset :
      conditionState.integerLiterals ⊆ resultState.integerLiterals :=
    List.Subset.trans
      (Detail.inferExprFuel_integerLiterals_subset thenSuccess)
      thenIntegerLiteralsSubset
  have unifiedIntegerPatternsSubset :
      unifiedState.integerPatterns ⊆ resultState.integerPatterns := by
    intro origin member
    rw [recordExpressionWithExpected_integerPatterns_eq recorded]
    exact member
  have elseIntegerPatternsSubset :
      elseState.integerPatterns ⊆ resultState.integerPatterns := by
    intro origin member
    apply unifiedIntegerPatternsSubset
    rw [(Detail.unify_integerPatternMetadata_eq unifySuccess).1]
    exact member
  have thenIntegerPatternsSubset :
      thenState.integerPatterns ⊆ resultState.integerPatterns :=
    List.Subset.trans
      (Detail.inferExprFuel_integerPatterns_subset elseSuccess)
      elseIntegerPatternsSubset
  have conditionIntegerPatternsSubset :
      conditionState.integerPatterns ⊆ resultState.integerPatterns :=
    List.Subset.trans
      (Detail.inferExprFuel_integerPatterns_subset thenSuccess)
      thenIntegerPatternsSubset
  have unifiedRequirementsSubset :
      unifiedState.requirements ⊆ resultState.requirements :=
    Detail.recordExpressionWithExpected_requirements_subset recorded
  have elseRequirementsSubset :
      elseState.requirements ⊆ resultState.requirements := by
    intro requirement member
    apply unifiedRequirementsSubset
    rw [Detail.unify_requirements_eq unifySuccess]
    exact member
  have thenRequirementsSubset :
      thenState.requirements ⊆ resultState.requirements :=
    List.Subset.trans
      (Detail.inferExprFuel_requirements_subset elseSuccess)
      elseRequirementsSubset
  have conditionRequirementsSubset :
      conditionState.requirements ⊆ resultState.requirements :=
    List.Subset.trans
      (Detail.inferExprFuel_requirements_subset thenSuccess)
      thenRequirementsSubset
  have conditionExpected : ∀ type ∈ (some Ty.bool : Option Ty), type.VariablesBelow allocated.inference.next := by
    intro type member
    have same : type = Ty.bool := (Option.some.inj member).symm
    subst type
    exact Ty.variablesBelow_constructor _ _
  have conditionInvariant := allocatedInvariant.ofExpression signatureFormation functionsCanonical
    conditionExpected laterCondition conditionSuccess
  have thenInvariant := conditionInvariant.ofExpression signatureFormation functionsCanonical
    expectedAtCondition laterThen thenSuccess
  have conditionOperational := allocatedOperational.ofExpression conditionSuccess conditionProperties.1.next_le
  have thenOperational := conditionOperational.ofExpression thenSuccess thenProperties.1.next_le
  obtain ⟨coercions, contains⟩ := recordExpressionWithExpected_success_containsExpression recorded roots
  have edge : ∀ child ∈ [conditionResult.id, thenResult.id, elseResult.id],
      DirectChild (resultState.toTypedSource roots) (.expression inferred.id) (.expression child) := by
    intro child member
    refine ⟨.expression _, ⟨contains.1, rfl⟩, ?_⟩
    simpa [nodeChildIds, Node.references, ExpressionForm.references] using
      (List.mem_map.mpr ⟨child, member, rfl⟩ : NodeId.expression child ∈
        [conditionResult.id, thenResult.id, elseResult.id].map NodeId.expression)
  have conditionEdge := edge conditionResult.id (by simp)
  have conditionTypeRaw := actualInferExprFuelFinalSubtreeSoundness_of_retainedSoundness recursive
    conditionSuccess resources interfaces laterCondition signaturesEq ownerEq typeParametersEq assumptionsEq
    signatureFormation functionsCanonical catalog canonical allocatedInvariant actual allocatedOperational conditionExpected
    (by
      intro type member
      have same : type = .bool := (Option.some.inj member).symm
      subst type
      exact TypeAdmissible.bool (invariant.typeParameterBinders (by simpa [ownerEq, typeParametersEq] using canonical)))
    ((semanticPreserved.childSubtree conditionEdge).monoBefore conditionToParent)
    ((finalPreserved.childSubtree conditionEdge).monoBefore conditionToParent)
    ((rawProper.childSubtree conditionEdge).monoBefore conditionToParent).proper
    (List.Subset.trans conditionIntegerPatternsSubset integerPatternsSubset)
    (List.Subset.trans conditionIntegerLiteralsSubset integerLiteralsSubset)
    (List.Subset.trans conditionRequirementsSubset requirementsSubset)
    (covered.expressionChild resources.graph_closed (childrenRetained conditionEdge))
    (actualCovered.directChild (childrenRetained conditionEdge))
  have thenEdge := edge thenResult.id (by simp)
  have thenTypeRaw := actualInferExprFuelFinalSubtreeSoundness_of_retainedSoundness recursive
    thenSuccess resources interfaces laterThen signaturesEq ownerEq typeParametersEq assumptionsEq
    signatureFormation functionsCanonical catalog canonical conditionInvariant actual conditionOperational expectedAtCondition expectedAdmissible
    ((semanticPreserved.childSubtree thenEdge).monoBefore thenToParent)
    ((finalPreserved.childSubtree thenEdge).monoBefore thenToParent)
    ((rawProper.childSubtree thenEdge).monoBefore thenToParent).proper
    (List.Subset.trans thenIntegerPatternsSubset integerPatternsSubset)
    (List.Subset.trans thenIntegerLiteralsSubset integerLiteralsSubset)
    (List.Subset.trans thenRequirementsSubset requirementsSubset)
    (covered.expressionChild resources.graph_closed (childrenRetained thenEdge))
    (actualCovered.directChild (childrenRetained thenEdge))
  have elseEdge := edge elseResult.id (by simp)
  have elseTypeRaw := actualInferExprFuelFinalSubtreeSoundness_of_retainedSoundness recursive
    elseSuccess resources interfaces laterElse signaturesEq ownerEq typeParametersEq assumptionsEq
    signatureFormation functionsCanonical catalog canonical thenInvariant actual thenOperational expectedAtThen expectedAdmissible
    ((semanticPreserved.childSubtree elseEdge).monoBefore elseToParent)
    ((finalPreserved.childSubtree elseEdge).monoBefore elseToParent)
    ((rawProper.childSubtree elseEdge).monoBefore elseToParent).proper
    (List.Subset.trans elseIntegerPatternsSubset integerPatternsSubset)
    (List.Subset.trans elseIntegerLiteralsSubset integerLiteralsSubset)
    (List.Subset.trans elseRequirementsSubset requirementsSubset)
    (covered.expressionChild resources.graph_closed (childrenRetained elseEdge))
    (actualCovered.directChild (childrenRetained elseEdge))
  have conditionEq : finalized.substitution.apply conditionResult.type =
      .bool := by
    simpa using Detail.inferExprFuel_expected_type_apply_eq conditionSuccess
      laterCondition
  have conditionType : ExpressionHasType semanticSource semanticContext
      conditionResult.id .bool := by
    rw [← conditionEq]
    exact conditionTypeRaw
  have resolvedThenEq :
      finalized.substitution.apply
          (unifiedState.resolve thenResult.type) =
        finalized.substitution.apply thenResult.type := by
    simpa [Frontend.SourceInference.State.resolve,
      TypeSystem.InferState.resolve] using laterUnified thenResult.type
  have resolvedElseEq :
      finalized.substitution.apply
          (unifiedState.resolve elseResult.type) =
        finalized.substitution.apply elseResult.type := by
    simpa [Frontend.SourceInference.State.resolve,
      TypeSystem.InferState.resolve] using laterUnified elseResult.type
  have unifiedEq : unifiedState.resolve thenResult.type =
      unifiedState.resolve elseResult.type := by
    simpa [Frontend.SourceInference.State.resolve] using
      Detail.unify_resolve_eq unifySuccess
  have branchEq : finalized.substitution.apply thenResult.type =
      finalized.substitution.apply elseResult.type := by
    calc
      finalized.substitution.apply thenResult.type =
          finalized.substitution.apply
            (unifiedState.resolve thenResult.type) := resolvedThenEq.symm
      _ = finalized.substitution.apply
          (unifiedState.resolve elseResult.type) :=
        congrArg finalized.substitution.apply unifiedEq
      _ = finalized.substitution.apply elseResult.type := resolvedElseEq
  have thenType : ExpressionHasType semanticSource semanticContext thenResult.id
      (finalized.substitution.apply
        (unifiedState.resolve thenResult.type)) := by
    rw [resolvedThenEq]
    exact thenTypeRaw
  have elseType : ExpressionHasType semanticSource semanticContext elseResult.id
      (finalized.substitution.apply
        (unifiedState.resolve thenResult.type)) := by
    rw [resolvedThenEq, branchEq]
    exact elseTypeRaw
  have formType : ExpressionFormHasRawType semanticSource semanticContext
      ((ExpressionForm.conditional conditionResult.id thenResult.id
        elseResult.id).applySubstitution finalized.substitution)
      (finalized.substitution.apply
        (unifiedState.resolve thenResult.type)) (.ordinary []) := by
    simpa [ExpressionForm.applySubstitution] using
      ExpressionFormHasRawType.conditional conditionType thenType elseType
  exact recordExpressionWithExpected_success_expressionTypingBase_actual resources interfaces
    recorded resultSubstitutionExtension requirementsSubset retained coercionsRetained
    catalog signaturesEq invariant formType thenType.type_admissible covered

end Solcore.SourceSemantics.SourceInferenceSoundness
