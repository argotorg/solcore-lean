import Solcore.SourceSemantics.SourceCompiledProvenanceStatementContracts
import Solcore.SourceSemantics.SourceCompiledBodySelectionFormation
import Solcore.SourceSemantics.SourceCompiledGeneralizedExpressionRooted
import Solcore.SourceSemantics.SourceInferenceSelectedOrdinaryRecorder
import Solcore.SourceSemantics.SourceInferenceSelectedExpressionState

set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledGeneralizedSoundness
open Frontend SourceInference TypeSystem SourceInferenceSoundness
open SourceCompiledLocalFinalization SourceInferenceExecution

private theorem safe_after_expression
    {childFuel : Nat} {context : SourceInference.Context} {expression : Syntax.Expr}
    {expected laterExpected : Option Ty} {initial final : State} {value : InferredExpression}
    {source : TypedSource}
    (operational : GeneralizedActualStateInvariant initial source)
    (ready : initial.InferenceReady)
    (catalog : SignatureCatalogWellFormed context.signatures)
    (formation : ProgramSignatureFormationValidated context.signatures)
    (canonical : ∀ signature ∈ context.signatures.functions,
      signature.scheme.body = .function (Ty.productMany signature.parameterTypes)
        (Ty.productMany signature.returnTypes))
    (expectedBelow : ∀ type ∈ expected, type.VariablesBelow initial.inference.next)
    (expectedSafe : ∀ binder ∈ initial.localBinders, ∀ type ∈ expected,
      ProtectedVariables.Safe binder.scheme.quantified initial type)
    (laterSafe : ∀ binder ∈ initial.localBinders, ∀ type ∈ laterExpected,
      ProtectedVariables.Safe binder.scheme.quantified initial type)
    (accepted : Detail.inferExprFuel childFuel context expression expected initial = .ok (value, final)) :
    ∀ binder ∈ final.localBinders, ∀ type ∈ laterExpected,
      ProtectedVariables.Safe binder.scheme.quantified final type := by
  intro binder member type typeMember
  have binders := congrArg LexicalScope.binders (Detail.inferExprFuel_success_lexicalScope_eq accepted)
  change final.localBinders = initial.localBinders at binders
  have entering : binder ∈ initial.localBinders := binders ▸ member
  exact (ProtectedVariables.inferExprFuel_private binder.scheme.quantified childFuel context expression
    expected initial ready operational.requirements (operational.quantifiersBelow binder entering)
    (operational.privacy binder entering) catalog formation canonical expectedBelow
    (expectedSafe binder entering) _ accepted).1 type (laterSafe binder entering type typeMember)

/-- Conditional inference threads privacy through the condition and both branches before assembling their common final-source typing. -/
theorem expressionRetained_conditional_for {callProvenance : CallIndex → Prop}
    {raw : Workspace.RawWorkspace} {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel childFuel : Nat}
    {selected : BodySelection compiled row fuel}
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    (descend : ChildClosed callProvenance)
    (recursive : ExpressionRetainedSoundnessFor callProvenance selected childFuel)
    {inferenceContext : SourceInference.Context} {expression condition thenBranch elseBranch : Syntax.Expr}
    {question colon : Syntax.SourceSpan}
    {expected : Option Ty} {initial resultState : State} {inferred : InferredExpression}
    {frames : List InitializedLetBinding} {target : SourceSemantics.Context}
    (here : callProvenance (.expression (childFuel + 1) inferenceContext expression expected initial inferred resultState))
    (expressionEq : expression.value = .conditional condition question thenBranch colon elseBranch)
    (boundary : RetainedExpressionBoundary selected (childFuel + 1) inferenceContext
      expression expected initial inferred resultState frames target) :
    ExpressionTypingBase (resultState.toTypedSource (bodyRoots selected))
      selected.body.finalized.typedSource target selected.body.finalized.substitution inferred := by
  have resources := selected.body.resources
  have signatureFormation := boundary.scope.formation checked
  have functionsCanonical := boundary.scope.functionsCanonical checked
  have catalog := boundary.scope.catalog checked
  have canonical := boundary.scope.canonical checked
  generalize allocationEq : initial.allocateExpressionId = allocatedPair
  rcases allocatedPair with ⟨id, allocated⟩
  have allocatedInvariant := boundary.invariant.allocateExpressionId allocationEq
  have allocatedOperational : GeneralizedActualStateInvariant allocated (evidenceSource selected) := by
    rw [← show initial.allocateExpressionId.2 = allocated from congrArg Prod.snd allocationEq]
    exact boundary.operational.allocateExpressionId
  have allocatedSafe : ∀ binder ∈ allocated.localBinders, ∀ type ∈ expected,
      ProtectedVariables.Safe binder.scheme.quantified allocated type := by
    rw [← show initial.allocateExpressionId.2 = allocated from congrArg Prod.snd allocationEq]
    exact boundary.expectedSafe
  have allocatedExpected : ∀ type ∈ expected, type.VariablesBelow allocated.inference.next := by
    rw [allocateExpressionId_inferenceNext_eq allocationEq]
    exact boundary.expectedBelow
  obtain ⟨conditionResult, conditionState, thenResult, thenState, elseResult,
      elseState, unifiedState, conditionSuccess, thenSuccess, elseSuccess,
      unifySuccess, recorded⟩ :=
    Detail.inferExprFuel_success_conditional_facts expressionEq allocationEq
      boundary.accepted
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
  have laterUnified : selected.body.finalized.substitution.SemanticallyExtends
      unifiedState.inference.substitution :=
    TypeSystem.Substitution.SemanticallyExtends.trans boundary.extension
      recordedProperties.1.substitution_extends
  have laterElse : selected.body.finalized.substitution.SemanticallyExtends
      elseState.inference.substitution :=
    TypeSystem.Substitution.SemanticallyExtends.trans laterUnified
      unifyProgress.substitution_extends
  have laterThen : selected.body.finalized.substitution.SemanticallyExtends
      thenState.inference.substitution :=
    TypeSystem.Substitution.SemanticallyExtends.trans laterElse
      elseProperties.1.substitution_extends
  have laterCondition : selected.body.finalized.substitution.SemanticallyExtends
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
    inferExprFuel_success_typingSourceExtends thenSuccess conditionBelow (bodyRoots selected)
  have thenToElse :=
    inferExprFuel_success_typingSourceExtends elseSuccess thenBelow (bodyRoots selected)
  have elseToUnified : TypingSourceExtends
      (elseState.toTypedSource (bodyRoots selected)) (unifiedState.toTypedSource (bodyRoots selected)) := by
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
    Detail.inferExprFuel_preserves_owner boundary.accepted
  have unifiedToParent : TypingSourceExtends
      (unifiedState.toTypedSource (bodyRoots selected)) (resultState.toTypedSource (bodyRoots selected)) := by
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
  have conditionSafe : ∀ binder ∈ allocated.localBinders, ∀ type ∈ (some Ty.bool : Option Ty),
      ProtectedVariables.Safe binder.scheme.quantified allocated type := by
    intro binder _ type member
    have same : type = Ty.bool := (Option.some.inj member).symm
    subst type
    exact ProtectedVariables.safe_closed _ _ (Ty.variablesBelow_constructor _ _)
  have expectedSafeAtCondition := safe_after_expression allocatedOperational allocatedInvariant.ready
    catalog signatureFormation functionsCanonical conditionExpected conditionSafe allocatedSafe conditionSuccess
  have conditionOperational := allocatedOperational.ofExpression allocatedInvariant.ready catalog
    signatureFormation functionsCanonical conditionExpected conditionSafe conditionSuccess
  have expectedSafeAtThen := safe_after_expression conditionOperational conditionInvariant.ready
    catalog signatureFormation functionsCanonical expectedAtCondition expectedSafeAtCondition
    expectedSafeAtCondition thenSuccess
  have thenOperational := conditionOperational.ofExpression conditionInvariant.ready catalog
    signatureFormation functionsCanonical expectedAtCondition expectedSafeAtCondition thenSuccess
  obtain ⟨coercions, contains⟩ := recordExpressionWithExpected_success_containsExpression recorded (bodyRoots selected)
  have edge : ∀ child ∈ [conditionResult.id, thenResult.id, elseResult.id],
      DirectChild (resultState.toTypedSource (bodyRoots selected)) (.expression inferred.id) (.expression child) := by
    intro child member
    refine ⟨.expression _, ⟨contains.1, rfl⟩, ?_⟩
    simpa [nodeChildIds, Node.references, ExpressionForm.references] using
      (List.mem_map.mpr ⟨child, member, rfl⟩ : NodeId.expression child ∈
        [conditionResult.id, thenResult.id, elseResult.id].map NodeId.expression)
  have conditionEdge := edge conditionResult.id (by simp)
  have conditionTypeRaw := expressionRooted_of_retained_for checked recursive
    (descend here (.expression_conditional_condition boundary.accepted expressionEq allocationEq conditionSuccess)) ({
    accepted := conditionSuccess
    interfaces := boundary.interfaces
    extension := laterCondition
    scope := boundary.scope
    invariant := allocatedInvariant
    actual := boundary.actual
    operational := allocatedOperational
    expectedBelow := conditionExpected
    expectedAdmissible := by
      intro type member
      have same : type = .bool := (Option.some.inj member).symm
      subst type
      exact TypeAdmissible.bool (boundary.invariant.typeParameterBinders (by
        simpa [boundary.scope.owner, boundary.scope.parameters] using canonical))
    expectedSafe := conditionSafe
    integerPatterns := List.Subset.trans conditionIntegerPatternsSubset boundary.integerPatterns
    integerLiterals := List.Subset.trans conditionIntegerLiteralsSubset boundary.integerLiterals
    requirements := List.Subset.trans conditionRequirementsSubset boundary.requirements
    covered := boundary.covered.expressionChild resources.graph_closed (boundary.directChildren conditionEdge)
    actualCovered := boundary.actualCovered.directChild (boundary.directChildren conditionEdge)
    rawSubtree := (boundary.rawProper.childSubtree conditionEdge).monoBefore conditionToParent } :
    RootedExpressionBoundary selected childFuel inferenceContext condition (some .bool)
      allocated conditionResult conditionState frames target)
  have thenEdge := edge thenResult.id (by simp)
  have thenTypeRaw := expressionRooted_of_retained_for checked recursive
    (descend here (.expression_conditional_then boundary.accepted expressionEq allocationEq conditionSuccess thenSuccess)) ({
    accepted := thenSuccess
    interfaces := boundary.interfaces
    extension := laterThen
    scope := boundary.scope
    invariant := conditionInvariant
    actual := boundary.actual
    operational := conditionOperational
    expectedBelow := expectedAtCondition
    expectedAdmissible := boundary.expectedAdmissible
    expectedSafe := expectedSafeAtCondition
    integerPatterns := List.Subset.trans thenIntegerPatternsSubset boundary.integerPatterns
    integerLiterals := List.Subset.trans thenIntegerLiteralsSubset boundary.integerLiterals
    requirements := List.Subset.trans thenRequirementsSubset boundary.requirements
    covered := boundary.covered.expressionChild resources.graph_closed (boundary.directChildren thenEdge)
    actualCovered := boundary.actualCovered.directChild (boundary.directChildren thenEdge)
    rawSubtree := (boundary.rawProper.childSubtree thenEdge).monoBefore thenToParent } :
    RootedExpressionBoundary selected childFuel inferenceContext thenBranch expected
      conditionState thenResult thenState frames target)
  have elseEdge := edge elseResult.id (by simp)
  have elseTypeRaw := expressionRooted_of_retained_for checked recursive
    (descend here (.expression_conditional_else boundary.accepted expressionEq allocationEq conditionSuccess thenSuccess elseSuccess)) ({
    accepted := elseSuccess
    interfaces := boundary.interfaces
    extension := laterElse
    scope := boundary.scope
    invariant := thenInvariant
    actual := boundary.actual
    operational := thenOperational
    expectedBelow := expectedAtThen
    expectedAdmissible := boundary.expectedAdmissible
    expectedSafe := expectedSafeAtThen
    integerPatterns := List.Subset.trans elseIntegerPatternsSubset boundary.integerPatterns
    integerLiterals := List.Subset.trans elseIntegerLiteralsSubset boundary.integerLiterals
    requirements := List.Subset.trans elseRequirementsSubset boundary.requirements
    covered := boundary.covered.expressionChild resources.graph_closed (boundary.directChildren elseEdge)
    actualCovered := boundary.actualCovered.directChild (boundary.directChildren elseEdge)
    rawSubtree := (boundary.rawProper.childSubtree elseEdge).monoBefore elseToParent } :
    RootedExpressionBoundary selected childFuel inferenceContext elseBranch expected
      thenState elseResult elseState frames target)
  have conditionEq : selected.body.finalized.substitution.apply conditionResult.type =
      .bool := by
    simpa using Detail.inferExprFuel_expected_type_apply_eq conditionSuccess
      laterCondition
  have conditionType : ExpressionHasType selected.body.finalized.typedSource target
      conditionResult.id .bool := by
    rw [← conditionEq]
    exact conditionTypeRaw
  have resolvedThenEq :
      selected.body.finalized.substitution.apply
          (unifiedState.resolve thenResult.type) =
        selected.body.finalized.substitution.apply thenResult.type := by
    simpa [Frontend.SourceInference.State.resolve,
      TypeSystem.InferState.resolve] using laterUnified thenResult.type
  have resolvedElseEq :
      selected.body.finalized.substitution.apply
          (unifiedState.resolve elseResult.type) =
        selected.body.finalized.substitution.apply elseResult.type := by
    simpa [Frontend.SourceInference.State.resolve,
      TypeSystem.InferState.resolve] using laterUnified elseResult.type
  have unifiedEq : unifiedState.resolve thenResult.type =
      unifiedState.resolve elseResult.type := by
    simpa [Frontend.SourceInference.State.resolve] using
      Detail.unify_resolve_eq unifySuccess
  have branchEq : selected.body.finalized.substitution.apply thenResult.type =
      selected.body.finalized.substitution.apply elseResult.type := by
    calc
      selected.body.finalized.substitution.apply thenResult.type =
          selected.body.finalized.substitution.apply
            (unifiedState.resolve thenResult.type) := resolvedThenEq.symm
      _ = selected.body.finalized.substitution.apply
          (unifiedState.resolve elseResult.type) :=
        congrArg selected.body.finalized.substitution.apply unifiedEq
      _ = selected.body.finalized.substitution.apply elseResult.type := resolvedElseEq
  have thenType : ExpressionHasType selected.body.finalized.typedSource target thenResult.id
      (selected.body.finalized.substitution.apply
        (unifiedState.resolve thenResult.type)) := by
    rw [resolvedThenEq]
    exact thenTypeRaw
  have elseType : ExpressionHasType selected.body.finalized.typedSource target elseResult.id
      (selected.body.finalized.substitution.apply
        (unifiedState.resolve thenResult.type)) := by
    rw [resolvedThenEq, branchEq]
    exact elseTypeRaw
  have formType : ExpressionFormHasRawType selected.body.finalized.typedSource target
      ((ExpressionForm.conditional conditionResult.id thenResult.id
        elseResult.id).applySubstitution selected.body.finalized.substitution)
      (selected.body.finalized.substitution.apply
        (unifiedState.resolve thenResult.type)) (.ordinary []) := by
    simpa [ExpressionForm.applySubstitution] using
      ExpressionFormHasRawType.conditional conditionType thenType elseType
  exact recordExpressionWithExpected_success_expressionTypingBase_actual resources boundary.interfaces
    recorded boundary.extension boundary.requirements boundary.expressionRequirements boundary.coercionPrimaries
    catalog boundary.scope.signatures boundary.invariant formType thenType.type_admissible boundary.covered

theorem expressionRetained_conditional
    {raw : Workspace.RawWorkspace} {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel childFuel : Nat}
    {selected : BodySelection compiled row fuel}
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    (recursive : ExpressionRetainedSoundness selected childFuel)
    {inferenceContext : SourceInference.Context} {expression condition thenBranch elseBranch : Syntax.Expr}
    {question colon : Syntax.SourceSpan}
    {expected : Option Ty} {initial resultState : State} {inferred : InferredExpression}
    {frames : List InitializedLetBinding} {target : SourceSemantics.Context}
    (expressionEq : expression.value = .conditional condition question thenBranch colon elseBranch)
    (boundary : RetainedExpressionBoundary selected (childFuel + 1) inferenceContext
      expression expected initial inferred resultState frames target) :
    ExpressionTypingBase (resultState.toTypedSource (bodyRoots selected))
      selected.body.finalized.typedSource target selected.body.finalized.substitution inferred := by
  exact expressionRetained_conditional_for (callProvenance := fun _ => True) checked true_childClosed
    (fun _ boundary => recursive boundary) True.intro expressionEq boundary

end Solcore.SourceSemantics.SourceCompiledGeneralizedSoundness
