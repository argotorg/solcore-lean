import Solcore.SourceSemantics.SourceInferenceSelectedForItemTransport
import Solcore.SourceSemantics.SourceInferenceSelectedStatementReferences

set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceSoundness
open Frontend Frontend.SourceInference TypeSystem
open SourceInferenceStatementsSoundness

theorem actualInferForItemFuelRootedSoundness_expression {fuel : Nat}
    (expressionSound : ActualInferExprFuelRootedSoundness fuel) :
  ∀ {wholeContext inferenceContext : Frontend.SourceInference.Context}
    {wholeReturn expectedReturn : Ty}
    {item : Syntax.ForItem} {expression : Syntax.Expr} {initial final : State}
    {inferred : ForItemForm} {evidenceState : State}
    {roots : List NodeId}
    {finalized : Frontend.SourceInference.Result}
    {semanticSource : TypedSource}
    {frames : List InitializedLetBinding}
    {semanticContext : SourceSemantics.Context}
    {control : ControlContext},
    item.value = .expression expression →
    Detail.inferForItemFuel (fuel + 1) inferenceContext item initial =
      .ok (inferred, final) →
    FinalInferenceResources wholeContext wholeReturn evidenceState roots
      finalized →
    ExecutableCoercionInterfaces.SourceInterfaces wholeContext.signatures
      finalized.solvedRequirements finalized.typedSource →
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
    RecursiveStatementInvariant wholeContext expectedReturn finalized
      initial semanticContext →
    ActualContext wholeContext finalized frames semanticContext →
    ActualStateInvariant initial (evidenceState.toTypedSource roots) →
    TypeAdmissible semanticContext (finalized.substitution.apply expectedReturn) →
    finalized.substitution.SemanticallyExtends final.inference.substitution →
    (∀ reference ∈ inferred.references, SubtreePreserved finalized.substitution
      (final.toTypedSource roots) semanticSource reference) →
    (∀ reference ∈ inferred.references, RawSubtreePreserved (final.toTypedSource roots)
      (evidenceState.toTypedSource roots) reference) →
    final.integerPatterns ⊆ evidenceState.integerPatterns →
    final.integerLiterals ⊆ evidenceState.integerLiterals →
    final.requirements ⊆ evidenceState.requirements →
    semanticSource.owner = initial.owner →
    ForItemReferencesCovered finalized.typedSource
      finalized.substitution semanticContext inferred →
    ForItemBindingRetained (evidenceState.toTypedSource roots) inferred →
    (∀ reference ∈ inferred.references, ActualContext.Covers finalized frames reference) →
    ActualForItemBindings finalized frames inferred →
    ∃ finalContext,
      RecursiveStatementInvariant wholeContext expectedReturn finalized
        final finalContext ∧
      ActualContext wholeContext finalized frames finalContext ∧
      ActualStateInvariant final (evidenceState.toTypedSource roots) ∧
      ForItemHasType semanticSource control semanticContext
        (inferred.applySubstitution finalized.substitution)
        finalContext := by
  intro wholeContext inferenceContext wholeReturn expectedReturn item expression initial final inferred
    evidenceState roots finalized semanticSource frames semanticContext control itemEq success resources interfaces
    signaturesEq ownerEq parametersEq assumptionsEq formation functions catalog canonical invariant actual operational
    _returnAdmissible extension semantic raw patterns literals requirements sourceOwner covered _bindings actualCovered _actualBindings
  obtain ⟨value, resultState, child, resultEq⟩ := inferForItemFuel_success_expression_facts itemEq success
  have sameItem : inferred = .expression value.id := congrArg Prod.fst resultEq
  have sameState : final = resultState := congrArg Prod.snd resultEq
  subst inferred
  subst final
  have member : (.expression value.id : NodeId) ∈ (ForItemForm.expression value.id).references := by simp [ForItemForm.references]
  have typed := expressionSound child resources interfaces extension signaturesEq ownerEq parametersEq assumptionsEq
    formation functions catalog canonical (RecursiveExpressionInvariant.ofStatement invariant) actual operational
    (by simp) (by simp) (semantic _ member) (raw _ member) patterns literals requirements
    (covered _ member) (actualCovered _ member)
  have properties := Detail.inferExprFuel_inferenceProperties invariant.ready formation functions (by simp) child
  exact ⟨semanticContext, invariant.inferExprFuel child formation functions (by simp) extension,
    actual, operational.ofExpression child properties.1.next_le,
    ForItemHasType.expression typed⟩

theorem actualInferForItemFuelRootedSoundness_assignValue {fuel : Nat}
    (placeSound : ActualInferPlaceFuelRootedSoundness fuel)
    (expressionSound : ActualInferExprFuelRootedSoundness fuel) :
  ∀ {wholeContext inferenceContext : Frontend.SourceInference.Context}
    {wholeReturn expectedReturn : Ty}
    {item : Syntax.ForItem} {target valueExpression : Syntax.Expr} {operator : Syntax.Located Syntax.ValueAssignOp} {initial final : State}
    {inferred : ForItemForm} {evidenceState : State}
    {roots : List NodeId}
    {finalized : Frontend.SourceInference.Result}
    {semanticSource : TypedSource}
    {frames : List InitializedLetBinding}
    {semanticContext : SourceSemantics.Context}
    {control : ControlContext},
    item.value = .assignValue target operator valueExpression →
    Detail.inferForItemFuel (fuel + 1) inferenceContext item initial =
      .ok (inferred, final) →
    FinalInferenceResources wholeContext wholeReturn evidenceState roots
      finalized →
    ExecutableCoercionInterfaces.SourceInterfaces wholeContext.signatures
      finalized.solvedRequirements finalized.typedSource →
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
    RecursiveStatementInvariant wholeContext expectedReturn finalized
      initial semanticContext →
    ActualContext wholeContext finalized frames semanticContext →
    ActualStateInvariant initial (evidenceState.toTypedSource roots) →
    TypeAdmissible semanticContext (finalized.substitution.apply expectedReturn) →
    finalized.substitution.SemanticallyExtends final.inference.substitution →
    (∀ reference ∈ inferred.references, SubtreePreserved finalized.substitution
      (final.toTypedSource roots) semanticSource reference) →
    (∀ reference ∈ inferred.references, RawSubtreePreserved (final.toTypedSource roots)
      (evidenceState.toTypedSource roots) reference) →
    final.integerPatterns ⊆ evidenceState.integerPatterns →
    final.integerLiterals ⊆ evidenceState.integerLiterals →
    final.requirements ⊆ evidenceState.requirements →
    semanticSource.owner = initial.owner →
    ForItemReferencesCovered finalized.typedSource
      finalized.substitution semanticContext inferred →
    ForItemBindingRetained (evidenceState.toTypedSource roots) inferred →
    (∀ reference ∈ inferred.references, ActualContext.Covers finalized frames reference) →
    ActualForItemBindings finalized frames inferred →
    ∃ finalContext,
      RecursiveStatementInvariant wholeContext expectedReturn finalized
        final finalContext ∧
      ActualContext wholeContext finalized frames finalContext ∧
      ActualStateInvariant final (evidenceState.toTypedSource roots) ∧
      ForItemHasType semanticSource control semanticContext
        (inferred.applySubstitution finalized.substitution)
        finalContext := by
  intro wholeContext inferenceContext wholeReturn expectedReturn item target valueExpression operator initial final inferred
    evidenceState roots finalized semanticSource frames semanticContext control itemEq success resources interfaces
    signaturesEq ownerEq parametersEq assumptionsEq formation functions catalog canonical invariant actual operational
    _returnAdmissible extension semantic raw patterns literals requirements sourceOwner covered _bindings actualCovered _actualBindings
  obtain ⟨assignment, value, resultState, child, resultEq⟩ := inferForItemFuel_success_assignValue_facts itemEq success
  have sameItem : inferred = .assignValue assignment operator.value value.id := congrArg Prod.fst resultEq
  have sameState : final = resultState := congrArg Prod.snd resultEq
  subst inferred
  subst final
  have keyMember : ∀ key, .expression key ∈ assignment.references →
      (.expression key : NodeId) ∈ (ForItemForm.assignValue assignment operator.value value.id).references := by
    intro key member
    exact List.mem_append_left _ member
  have rhsMember : (.expression value.id : NodeId) ∈
      (ForItemForm.assignValue assignment operator.value value.id).references := by simp [ForItemForm.references]
  obtain ⟨placeTyped, valueTyped⟩ := actualInferAssignedValueFuel_children_rootedSound
    (parentState := resultState) child resources interfaces signaturesEq ownerEq parametersEq assumptionsEq
    formation functions catalog canonical (RecursiveExpressionInvariant.ofStatement invariant) actual operational
    extension ⟨rfl, ⟨[], by simp⟩⟩
    (fun key member => raw _ (keyMember key member)) (raw _ rhsMember) patterns literals requirements
    (fun key member => covered _ (keyMember key member)) (covered _ rhsMember)
    (fun key member => actualCovered _ (keyMember key member)) (actualCovered _ rhsMember) placeSound expressionSound
  have typedLocal := inferAssignedValueFuel_success_sound_of_typed_result invariant.ready formation functions
    extension placeTyped valueTyped child
  have typed := sourceAssignment_transportExpressions typedLocal (after := semanticSource) (fun id member type typing =>
    (semantic (.expression id) (by simpa [ForItemForm.references, AssignmentResolution.references,
      AssignmentResolution.applySubstitution, PlaceResolution.references, PlaceResolution.applySubstitution] using member)).subgraph.expression typing (.inl rfl))
  have bindersEq : resultState.localBinders = initial.localBinders := by
    exact congrArg LexicalScope.binders (Detail.inferAssignedValueFuel_success_lexicalScope_eq child)
  have properties := Detail.inferForItemFuel_inferenceProperties invariant.ready formation functions success
  have active := invariant.active.inferAssignedValueFuel child
  have isolation := activeSchemeQuantifierIsolation_transport invariant.schemeIsolation bindersEq
  have itemTyped : ForItemHasType semanticSource control semanticContext
      ((ForItemForm.assignValue assignment operator.value value.id).applySubstitution finalized.substitution) semanticContext :=
    .assignValue typed
  exact ⟨semanticContext, invariant.of_forItem_typing success formation functions active isolation extension itemTyped,
    actual, operational.ofForItemPreservingBinders success bindersEq properties.1.next_le, itemTyped⟩

theorem actualInferForItemFuelRootedSoundness_assignBitNot {fuel : Nat}
    (placeSound : ActualInferPlaceFuelRootedSoundness fuel) :
  ∀ {wholeContext inferenceContext : Frontend.SourceInference.Context}
    {wholeReturn expectedReturn : Ty}
    {item : Syntax.ForItem} {target : Syntax.Expr} {operatorSpan : Syntax.SourceSpan} {initial final : State}
    {inferred : ForItemForm} {evidenceState : State}
    {roots : List NodeId}
    {finalized : Frontend.SourceInference.Result}
    {semanticSource : TypedSource}
    {frames : List InitializedLetBinding}
    {semanticContext : SourceSemantics.Context}
    {control : ControlContext},
    item.value = .assignBitNot target operatorSpan →
    Detail.inferForItemFuel (fuel + 1) inferenceContext item initial =
      .ok (inferred, final) →
    FinalInferenceResources wholeContext wholeReturn evidenceState roots
      finalized →
    ExecutableCoercionInterfaces.SourceInterfaces wholeContext.signatures
      finalized.solvedRequirements finalized.typedSource →
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
    RecursiveStatementInvariant wholeContext expectedReturn finalized
      initial semanticContext →
    ActualContext wholeContext finalized frames semanticContext →
    ActualStateInvariant initial (evidenceState.toTypedSource roots) →
    TypeAdmissible semanticContext (finalized.substitution.apply expectedReturn) →
    finalized.substitution.SemanticallyExtends final.inference.substitution →
    (∀ reference ∈ inferred.references, SubtreePreserved finalized.substitution
      (final.toTypedSource roots) semanticSource reference) →
    (∀ reference ∈ inferred.references, RawSubtreePreserved (final.toTypedSource roots)
      (evidenceState.toTypedSource roots) reference) →
    final.integerPatterns ⊆ evidenceState.integerPatterns →
    final.integerLiterals ⊆ evidenceState.integerLiterals →
    final.requirements ⊆ evidenceState.requirements →
    semanticSource.owner = initial.owner →
    ForItemReferencesCovered finalized.typedSource
      finalized.substitution semanticContext inferred →
    ForItemBindingRetained (evidenceState.toTypedSource roots) inferred →
    (∀ reference ∈ inferred.references, ActualContext.Covers finalized frames reference) →
    ActualForItemBindings finalized frames inferred →
    ∃ finalContext,
      RecursiveStatementInvariant wholeContext expectedReturn finalized
        final finalContext ∧
      ActualContext wholeContext finalized frames finalContext ∧
      ActualStateInvariant final (evidenceState.toTypedSource roots) ∧
      ForItemHasType semanticSource control semanticContext
        (inferred.applySubstitution finalized.substitution)
        finalContext := by
  intro wholeContext inferenceContext wholeReturn expectedReturn item target operatorSpan initial final inferred
    evidenceState roots finalized semanticSource frames semanticContext control itemEq success resources interfaces
    signaturesEq ownerEq parametersEq assumptionsEq formation functions catalog canonical invariant actual operational
    _returnAdmissible extension semantic raw patterns literals requirements sourceOwner covered _bindings actualCovered _actualBindings
  obtain ⟨place, placeState, unified, placeSuccess, unifySuccess, resultEq⟩ :=
    inferForItemFuel_success_assignBitNot_facts itemEq success
  have sameItem := congrArg Prod.fst resultEq
  have sameState := congrArg Prod.snd resultEq
  dsimp only at sameItem sameState
  subst inferred
  subst final
  have placeToParent : TypingSourceExtends (placeState.toTypedSource roots) (unified.toTypedSource roots) := by
    constructor
    · exact congrArg State.Header.owner (Detail.unify_state_header unifySuccess)
    · change placeState.nodes <+: unified.nodes
      rw [← (Detail.unify_occurrenceState_eq unifySuccess).1]
      exact ⟨[], by simp⟩
  have properties := Detail.inferPlaceFuel_inferenceProperties invariant.ready formation functions placeSuccess
  have placeExtension := extension.trans
    (Detail.unify_inferenceProgress properties.2.1.solved properties.2.2
      (Ty.variablesBelow_constructor _ _) unifySuccess).substitution_extends
  have keyMember : ∀ key, .expression key ∈ place.references →
      (.expression key : NodeId) ∈ (ForItemForm.assignBitNot
        {target := {place with type := unified.resolve place.type}}).references := by
    intro key member
    simpa [ForItemForm.references, AssignmentResolution.references, PlaceResolution.references] using member
  have placePatterns : placeState.integerPatterns ⊆ evidenceState.integerPatterns := by
    simpa only [Detail.unify_integerPatterns unifySuccess] using patterns
  have placeLiterals : placeState.integerLiterals ⊆ evidenceState.integerLiterals := by
    simpa only [Detail.unify_integerLiterals unifySuccess] using literals
  have placeRequirements : placeState.requirements ⊆ evidenceState.requirements := by
    simpa only [Detail.unify_requirements_eq unifySuccess] using requirements
  have placeLocal := placeSound placeSuccess resources interfaces signaturesEq ownerEq parametersEq assumptionsEq
    formation functions catalog canonical (RecursiveExpressionInvariant.ofStatement invariant) actual operational
    placeExtension placeToParent (fun key member => raw _ (keyMember key member))
    placePatterns placeLiterals placeRequirements (fun key member => covered _ (keyMember key member))
    (fun key member => actualCovered _ (keyMember key member))
  have placeTyped := sourcePlace_transportExpressions placeLocal (after := semanticSource) (fun id member type typing =>
    (semantic (.expression id) (keyMember id (by simpa [PlaceResolution.references, PlaceResolution.applySubstitution] using member))).subgraph.expression typing (.inl rfl))
  obtain ⟨finalContext, finalInvariant, typing⟩ := inferForItemFuel_success_assignBitNot_of_certificate
    success formation functions invariant extension ⟨place, placeState, unified, placeSuccess, unifySuccess, rfl, placeTyped⟩
  have bindersEq : unified.localBinders = initial.localBinders := by
    exact (congrArg LexicalScope.binders (Detail.unify_preserves_lexicalScope unifySuccess)).trans
      (congrArg LexicalScope.binders (Detail.inferPlaceFuel_success_lexicalScope_eq placeSuccess))
  have itemProperties := Detail.inferForItemFuel_inferenceProperties invariant.ready formation functions success
  exact ⟨finalContext, finalInvariant, actual.of_forItem typing,
    operational.ofForItemPreservingBinders success bindersEq itemProperties.1.next_le, typing⟩

end Solcore.SourceSemantics.SourceInferenceSoundness
