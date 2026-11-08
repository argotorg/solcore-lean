import Solcore.SourceSemantics.Internal.Selected.Statements
import Solcore.SourceSemantics.Internal.Selected.StatementReferences
import Solcore.SourceSemantics.Internal.Inference.RootedContracts
import Solcore.SourceSemantics.Internal.Selected.State
import Solcore.SourceSemantics.Internal.Inference.StatementControl
import Solcore.SourceSemantics.Internal.Inference.StatementResources

/-!
# Selected loops

The `for` statement step: header items, condition and body.
-/

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceSelectedForItemTransport
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceSoundness
open Frontend Frontend.SourceInference TypeSystem

theorem sourcePlace_transportExpressions {before after : TypedSource}
    {context : SourceSemantics.Context} {place : PlaceResolution} {type : Ty}
    (typed : SourcePlaceHasType before context place type)
    (children : ∀ id, .expression id ∈ place.references → ∀ type,
      ExpressionHasType before context id type → ExpressionHasType after context id type) :
    SourcePlaceHasType after context place type := by
  have projections {input output : Ty} {projections : List PlaceProjection}
      (typed : SourceProjectionsHaveType before context input projections output)
      (children : ∀ id, .expression id ∈ projections.flatMap PlaceProjection.references → ∀ type,
        ExpressionHasType before context id type → ExpressionHasType after context id type) :
      SourceProjectionsHaveType after context input projections output := by
    induction projections generalizing input output with
    | nil => cases typed; exact .nil _
    | cons projection rest induction =>
      cases typed with
      | index key tail =>
        exact .index (children _ (by simp [PlaceProjection.references]) _ key)
          (induction tail (fun id member => children id (by simp [member])))
      | member selected tail =>
        exact .member selected (induction tail (fun id member => children id (by simp [member])))
  cases typed with
  | intro root rest same => exact .intro root (projections rest children) same

theorem sourceAssignment_transportExpressions {before after : TypedSource}
    {context : SourceSemantics.Context} {assignment : AssignmentResolution}
    {operator : Syntax.ValueAssignOp} {value : ExpressionId}
    (typed : SourceAssignmentHasType before context assignment operator value)
    (children : ∀ id, .expression id ∈ assignment.references ++ [.expression value] → ∀ type,
      ExpressionHasType before context id type → ExpressionHasType after context id type) :
    SourceAssignmentHasType after context assignment operator value := by
  have place {type : Ty} (typed : SourcePlaceHasType before context assignment.target type) :
      SourcePlaceHasType after context assignment.target type :=
    sourcePlace_transportExpressions typed (fun id member => children id (by simp [AssignmentResolution.references, member]))
  cases typed with
  | equal target value requirements => exact .equal (place target) (children _ (by simp) _ value) requirements
  | wordCompound operator target value requirements =>
    exact .wordCompound operator (place target) (children _ (by simp) _ value) requirements

theorem ActualStateInvariant.ofForItemPreservingBinders
    {fuel : Nat} {context : Frontend.SourceInference.Context}
    {item : Syntax.ForItem} {initial final : State} {inferred : ForItemForm} {source : TypedSource}
    (invariant : ActualStateInvariant initial source)
    (success : Detail.inferForItemFuel fuel context item initial = .ok (inferred, final))
    (bindersEq : final.localBinders = initial.localBinders)
    (nextLe : initial.inference.next ≤ final.inference.next) : ActualStateInvariant final source := by
  obtain ⟨pending, ledger⟩ := invariant.ledger
  exact ⟨⟨pending ++ inferred.localSchemeTemplateIds, (actualLedgerFamily fuel).statements.forItem success ledger⟩,
    invariant.origins.congr_localBinders bindersEq,
    activeQuantifiersBelowNext_transport invariant.quantifiersBelow bindersEq nextLe, invariant.sourceMonomorphic⟩

end Solcore.SourceSemantics.SourceInferenceSoundness
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceSelectedForItemBranches
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
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceSelectedForItemsSequencing
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceSoundness
open Frontend Frontend.SourceInference TypeSystem
open SourceInferenceStatementsSoundness

theorem actualInferForItemsFuelRootedSoundness_of_itemSoundness
    {fuel : Nat}
    (itemSound : ActualInferForItemFuelRootedSoundness fuel) :
    ActualInferForItemsFuelRootedSoundness fuel := by
  intro wholeContext inferenceContext wholeReturn expectedReturn items
    initial result evidenceState roots finalized semanticSource
    frames semanticContext control success resources interfaces signaturesEq ownerEq
    parametersEq assumptionsEq signatureFormation functionsCanonical
    catalog signatureParameters initialInvariant actual operational returnAdmissible substitutionExtension
    resultExtension rawResultExtension
    integerPatternsSubset integerLiteralsSubset requirementsSubset
    sourceOwner covered bindingsRetained actualCovered actualBindings
  induction items generalizing initial result semanticContext with
  | nil =>
      simp only [Detail.inferForItemsFuel, pure, Pure.pure, Except.pure]
        at success
      injection success with resultEq
      subst result
      exact ⟨semanticContext, initialInvariant, actual, operational,
        ForItemsHaveType.nil control semanticContext⟩
  | cons item rest induction =>
      unfold Detail.inferForItemsFuel at success
      cases itemSuccess : Detail.inferForItemFuel fuel inferenceContext item
          initial with
      | error error =>
          simp [itemSuccess, bind, Except.bind] at success
      | ok itemPair =>
          rcases itemPair with ⟨inferredItem, itemState⟩
          simp only [itemSuccess, bind, Except.bind] at success
          cases tailSuccess : Detail.inferForItemsFuel fuel inferenceContext
              rest itemState with
          | error error =>
              simp [tailSuccess] at success
          | ok tail =>
              simp only [tailSuccess, pure, Pure.pure, Except.pure] at success
              injection success with resultEq
              subst result
              have itemProperties := Detail.inferForItemFuel_inferenceProperties
                initialInvariant.ready signatureFormation functionsCanonical
                itemSuccess
              have tailProperties := Detail.inferForItemsFuel_inferenceProperties
                itemProperties.2 signatureFormation functionsCanonical
                tailSuccess
              have itemSubstitutionExtension :
                  finalized.substitution.SemanticallyExtends
                    itemState.inference.substitution :=
                substitutionExtension.trans
                  tailProperties.1.substitution_extends
              have itemBelow : itemState.NodesBelowNextOccurrence :=
                (Detail.inferForItemFuel_occurrenceBoundExtends itemSuccess
                  ).nodesBelowNextOccurrence initialInvariant.nodesBelow
              have itemToResult : TypingSourceExtends
                  (itemState.toTypedSource roots)
                  (tail.state.toTypedSource roots) :=
                inferForItemsFuel_success_typingSourceExtends tailSuccess
                  itemBelow roots
              have itemExtension : ∀ reference ∈ inferredItem.references,
                  SubtreePreserved finalized.substitution (itemState.toTypedSource roots) semanticSource reference := by
                intro reference member
                exact (resultExtension inferredItem (by simp) reference member).monoBefore itemToResult
              have itemRawExtension : ∀ reference ∈ inferredItem.references,
                  RawSubtreePreserved (itemState.toTypedSource roots) (evidenceState.toTypedSource roots) reference := by
                intro reference member
                exact (rawResultExtension inferredItem (by simp) reference member).monoBefore itemToResult
              have itemPatternsSubset : itemState.integerPatterns ⊆
                  evidenceState.integerPatterns := by
                intro origin member
                exact integerPatternsSubset
                  ((Detail.inferForItemsFuel_integerPatterns_subset
                    tailSuccess) member)
              have itemLiteralsSubset : itemState.integerLiterals ⊆
                  evidenceState.integerLiterals := by
                intro origin member
                exact integerLiteralsSubset
                  ((Detail.inferForItemsFuel_integerLiterals_subset
                    tailSuccess) member)
              have itemRequirementsSubset : itemState.requirements ⊆
                  evidenceState.requirements := by
                intro requirement member
                exact requirementsSubset
                  ((Detail.inferForItemsFuel_requirements_subset
                    tailSuccess) member)
              have itemCovered : ForItemReferencesCovered
                  finalized.typedSource finalized.substitution
                  semanticContext inferredItem := by
                apply covered
                simp
              have itemBindingsRetained : ForItemBindingRetained
                  (evidenceState.toTypedSource roots) inferredItem := by
                intro binding member
                apply bindingsRetained
                simp only [List.flatMap_cons, List.mem_append]
                exact Or.inl member
              obtain ⟨middleContext, middleInvariant, middleActual, middleOperational, itemTyping⟩ :=
                itemSound itemSuccess resources interfaces signaturesEq ownerEq
                  parametersEq assumptionsEq signatureFormation
                  functionsCanonical catalog signatureParameters
                  initialInvariant actual operational returnAdmissible itemSubstitutionExtension itemExtension
                  itemRawExtension itemPatternsSubset
                  itemLiteralsSubset itemRequirementsSubset sourceOwner
                  itemCovered itemBindingsRetained
                  (actualCovered inferredItem (by simp)) (actualBindings inferredItem (by simp))
              have tailOwner : semanticSource.owner = itemState.owner :=
                sourceOwner.trans
                  (Detail.inferForItemFuel_preserves_owner itemSuccess).symm
              have tailCovered : ForItemsReferencesCovered
                  finalized.typedSource finalized.substitution middleContext
                  tail.items := by
                intro nextItem member
                have original : ForItemReferencesCovered
                    finalized.typedSource finalized.substitution
                    semanticContext nextItem := by
                  apply covered
                  simp [member]
                exact original.transportAssumptions
                  (forItemHasType_assumptions_eq itemTyping)
              have tailBindingsRetained : ForItemsBindingsRetained
                  (evidenceState.toTypedSource roots) tail.items := by
                intro binding member
                apply bindingsRetained
                simp only [List.flatMap_cons, List.mem_append]
                exact Or.inr member
              have fields := forItemHasType_nonlocal_fields_eq itemTyping
              have middleReturn : TypeAdmissible middleContext (finalized.substitution.apply expectedReturn) :=
                StructuralSubstitution.TypeAdmissible.transportContext fields.1 fields.2.1 fields.2.2.1
                  (middleActual.variables_eq.trans actual.variables_eq.symm) fields.2.2.2.1 returnAdmissible
              obtain ⟨finalContext, finalInvariant, finalActual, finalOperational, tailTyping⟩ :=
                induction (initial := itemState) (result := tail)
                  (semanticContext := middleContext) tailSuccess
                  middleInvariant middleActual middleOperational middleReturn substitutionExtension
                  (fun next member => resultExtension next (by simp [member]))
                  (fun next member => rawResultExtension next (by simp [member]))
                  integerPatternsSubset integerLiteralsSubset
                  requirementsSubset tailOwner tailCovered
                  tailBindingsRetained
                  (fun next member => actualCovered next (by simp [member]))
                  (fun next member => actualBindings next (by simp [member]))
              refine ⟨finalContext, finalInvariant, finalActual, finalOperational, ?_⟩
              exact ForItemsHaveType.cons itemTyping tailTyping

end Solcore.SourceSemantics.SourceInferenceSoundness
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceSelectedForLoopCoverage
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceSoundness
open Frontend Frontend.SourceInference TypeSystem

theorem forItemsReferencesCovered_of_rootedForLoop
    {rawSource finalSource : TypedSource} {outer : Substitution}
    {id : StatementId} {node : StatementNode}
    {initializer post : List ForItemForm} {condition : ExpressionId}
    {body : List StatementId} {context : SourceSemantics.Context}
    (containsRaw : ContainsStatement rawSource id node)
    (formEq : node.form = .forLoop initializer condition post body)
    (extension : SubtreePreserved outer rawSource finalSource (.statement id))
    (closed : OccurrenceGraphClosed finalSource)
    (parentCovered : TemplateScopeCovered finalSource context
      (.statement id)) :
    ForItemsReferencesCovered finalSource outer context initializer ∧
      ForItemsReferencesCovered finalSource outer context post := by
  have containsFinal : ContainsStatement finalSource id
      (node.applySubstitution outer) :=
    extension.containsStatement containsRaw
  have finalForm : (node.applySubstitution outer).form =
      .forLoop (initializer.map (ForItemForm.applySubstitution outer))
        condition (post.map (ForItemForm.applySubstitution outer)) body := by
    simp [StatementNode.applySubstitution, formEq,
      StatementForm.applySubstitution]
  have covered := forLoop_finalHeaderReferencesCovered closed
    containsFinal finalForm parentCovered
  constructor
  · intro item itemMem reference referenceMem
    have finalItemMem : item.applySubstitution outer ∈
        (initializer.map (ForItemForm.applySubstitution outer)) ++
          (post.map (ForItemForm.applySubstitution outer)) := by
      exact List.mem_append_left _
        (List.mem_map.mpr ⟨item, itemMem, rfl⟩)
    have finalRefMem : reference ∈
        (item.applySubstitution outer).references := by
      simpa using referenceMem
    have finalCovered := covered (item.applySubstitution outer)
      finalItemMem reference finalRefMem
    cases item with
    | letDecl binder initializerId =>
        cases initializerId <;>
          simpa [forItemCoverageContext, ForItemForm.applySubstitution]
            using finalCovered
    | expression expression =>
        simpa [forItemCoverageContext, ForItemForm.applySubstitution]
          using finalCovered
    | assignValue assignment operator value =>
        simpa [forItemCoverageContext, ForItemForm.applySubstitution]
          using finalCovered
    | assignBitNot assignment =>
        simpa [forItemCoverageContext, ForItemForm.applySubstitution]
          using finalCovered
  · intro item itemMem reference referenceMem
    have finalItemMem : item.applySubstitution outer ∈
        (initializer.map (ForItemForm.applySubstitution outer)) ++
          (post.map (ForItemForm.applySubstitution outer)) := by
      exact List.mem_append_right _
        (List.mem_map.mpr ⟨item, itemMem, rfl⟩)
    have finalRefMem : reference ∈
        (item.applySubstitution outer).references := by
      simpa using referenceMem
    have finalCovered := covered (item.applySubstitution outer)
      finalItemMem reference finalRefMem
    cases item with
    | letDecl binder initializerId =>
        cases initializerId <;>
          simpa [forItemCoverageContext, ForItemForm.applySubstitution]
            using finalCovered
    | expression expression =>
        simpa [forItemCoverageContext, ForItemForm.applySubstitution]
          using finalCovered
    | assignValue assignment operator value =>
        simpa [forItemCoverageContext, ForItemForm.applySubstitution]
          using finalCovered
    | assignBitNot assignment =>
        simpa [forItemCoverageContext, ForItemForm.applySubstitution]
          using finalCovered
private theorem item_reference {item : ForItemForm} {binding : InitializedLetBinding}
    (member : binding ∈ forItemInitializedLetBindings item) :
    binding.initializer ∈ item.references := by
  cases item with
  | letDecl binder value =>
    cases value with
    | none => simp [forItemInitializedLetBindings] at member
    | some value =>
      simp only [forItemInitializedLetBindings, List.mem_singleton] at member
      subst binding
      simp [ForItemForm.references]
  | expression _ | assignValue _ _ _ | assignBitNot _ =>
    simp [forItemInitializedLetBindings] at member

private theorem statement_reference {form : StatementForm} {binding : InitializedLetBinding}
    (member : binding ∈ statementInitializedLetBindings form) :
    binding.initializer ∈ form.references := by
  cases form with
  | letDecl binder value =>
    cases value with
    | none => simp [statementInitializedLetBindings] at member
    | some value =>
      simp only [statementInitializedLetBindings, List.mem_singleton] at member
      subst binding
      simp [StatementForm.references]
  | forLoop initializer condition post body =>
    simp only [statementInitializedLetBindings, List.mem_append] at member
    rcases member with member | member
    all_goals
      obtain ⟨item, present, member⟩ := List.mem_flatMap.mp member
      have reference := item_reference member
      simp only [StatementForm.references, List.mem_append, List.mem_cons]
    · exact .inl (.inl (.inl (List.mem_flatMap.mpr ⟨item, present, reference⟩)))
    · exact .inl (.inr (List.mem_flatMap.mpr ⟨item, present, reference⟩))
  | returnStmt _ | expression _ _ | assignValue _ _ _ | assignBitNot _
    | ifThen _ _ _ | block _ | matchWith _ | whileLoop _ _ | breakStmt | continueStmt =>
    simp [statementInitializedLetBindings] at member

/-- Membership in the original statement's binder list yields the literal
closed binder and its edge in the same final source. -/
theorem actualBinding_of_rootedStatement
    {before : TypedSource} {id : StatementId} {node : StatementNode}
    {finalized : Frontend.SourceInference.Result} {binding : InitializedLetBinding}
    (recorded : ContainsStatement before id node)
    (extension : SubtreePreserved finalized.substitution before finalized.typedSource (.statement id))
    (member : binding ∈ statementInitializedLetBindings node.form) :
    let closed := FlexibleSubstitution.applyInitializedLetBinding finalized.substitution binding
    closed ∈ initializedLetBindings finalized.typedSource ∧
      DirectChild finalized.typedSource (.statement id) closed.initializer := by
  have retained := extension.containsStatement recorded
  have closedMember : FlexibleSubstitution.applyInitializedLetBinding finalized.substitution binding ∈
      statementInitializedLetBindings (node.form.applySubstitution finalized.substitution) := by
    rw [FlexibleSubstitution.statementInitializedLetBindings_applySubstitution]
    exact List.mem_map_of_mem member
  constructor
  · unfold initializedLetBindings
    exact List.mem_flatMap.mpr ⟨.statement (node.applySubstitution finalized.substitution), retained.1, closedMember⟩
  · refine ⟨.statement (node.applySubstitution finalized.substitution),
      ⟨retained.1, congrArg NodeId.statement retained.2⟩, ?_⟩
    exact statement_reference closedMember

/-- Both header lists obtain scope provenance from their original enclosing
loop, including initialized binders whose template-requirement list is empty. -/
theorem actualForItemsBindings_of_rootedForLoop
    {before : TypedSource} {id : StatementId} {span : Syntax.SourceSpan} {type : Ty}
    {initializer post : List ForItemForm} {condition : ExpressionId} {body : List StatementId}
    {finalized : Frontend.SourceInference.Result} {frames : List InitializedLetBinding}
    (recorded : ContainsStatement before id {id, span, type, form := .forLoop initializer condition post body})
    (extension : SubtreePreserved finalized.substitution before finalized.typedSource (.statement id))
    (covered : ActualContext.Covers finalized frames (.statement id)) :
    ActualForItemsBindings finalized frames initializer ∧ ActualForItemsBindings finalized frames post := by
  have all : ∀ binding ∈ statementInitializedLetBindings (.forLoop initializer condition post body),
      let closed := FlexibleSubstitution.applyInitializedLetBinding finalized.substitution binding
      closed ∈ initializedLetBindings finalized.typedSource ∧
        ∀ outer ∈ frames, Descends finalized.typedSource outer.initializer closed.initializer := by
    intro binding member
    obtain ⟨retained, edge⟩ := actualBinding_of_rootedStatement recorded extension member
    refine ⟨retained, ?_⟩
    intro outer present
    rcases covered outer present with same | below
    · exact same ▸ Descends.direct edge
    · exact below.trans (.direct edge)
  constructor
  · intro item present binding member
    exact all binding (by
      simp only [statementInitializedLetBindings, List.mem_append]
      exact .inl (List.mem_flatMap.mpr ⟨item, present, member⟩))
  · intro item present binding member
    exact all binding (by
      simp only [statementInitializedLetBindings, List.mem_append]
      exact .inr (List.mem_flatMap.mpr ⟨item, present, member⟩))


theorem RawSubtreePreserved.containsStatement
    {before after : TypedSource} {id : StatementId} {node : StatementNode}
    (preserved : RawSubtreePreserved before after (.statement id))
    (contains : ContainsStatement before id node) : ContainsStatement after id node := by
  refine ⟨preserved.nodes (.statement node) contains.1 (.inl ?_), contains.2⟩
  simpa [Node.id] using congrArg NodeId.statement contains.2

end Solcore.SourceSemantics.SourceInferenceSoundness
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceSelectedForLoopCondition
/-!
The actual `for` condition is inferred after the initializer header has
established its loop-local lexical context.  This bridge uses the completed
parent's provenance and the unique condition slot to type that expression
without attributing header-let template scopes to it.
-/

set_option autoImplicit false
set_option Elab.async false

namespace Solcore.SourceSemantics.SourceInferenceSoundness

open Frontend Frontend.SourceInference TypeSystem

/-- A successful `for` condition is typed under the initializer-produced
context in the completed parent statement source. -/
theorem actualInferStatementFuel_success_forLoop_condition_rooted
    {fuel : Nat}
    {wholeContext inferenceContext : Frontend.SourceInference.Context}
    {wholeReturn expectedReturn : Ty}
    {statement : Syntax.Statement} {headerSpan : Syntax.SourceSpan}
    {initializer post : List Syntax.ForItem} {condition : Syntax.Expr}
    {body : Syntax.Block}
    {initial allocated evidenceState : State}
    {id : StatementId} {result : Detail.StatementResult}
    {initializerResult : Detail.InferredForItems}
    {inferredCondition : InferredExpression} {conditionState : State}
    {roots : List NodeId} {finalized : Frontend.SourceInference.Result}
    {semanticContext loopContext : SourceSemantics.Context}
    {frames : List InitializedLetBinding}
    (statementEq : statement.value =
      .forLoop headerSpan initializer condition post body)
    (allocationEq : initial.allocateStatementId = (id, allocated))
    (success : Detail.inferStatementFuel (fuel + 1) inferenceContext
      statement expectedReturn initial = .ok result)
    (initializerSuccess : Detail.inferForItemsFuel fuel inferenceContext
      initializer allocated = .ok initializerResult)
    (conditionSuccess : Detail.inferExprFuel fuel inferenceContext condition
      (some .bool) initializerResult.state =
        .ok (inferredCondition, conditionState))
    (resources : FinalInferenceResources wholeContext wholeReturn
      evidenceState roots finalized)
    (interfaces : ExecutableCoercionInterfaces.SourceInterfaces wholeContext.signatures finalized.solvedRequirements finalized.typedSource)
    (signaturesEq : inferenceContext.signatures = wholeContext.signatures)
    (ownerEq : inferenceContext.scope.genericOwner =
      wholeContext.scope.genericOwner)
    (parametersEq : inferenceContext.typeParameters =
      wholeContext.typeParameters)
    (assumptionsEq : inferenceContext.assumptions = wholeContext.assumptions)
    (signatureFormation : ProgramSignatureFormationValidated
      inferenceContext.signatures)
    (functionsCanonical : ∀ candidate ∈ inferenceContext.signatures.functions,
      candidate.scheme.body = .function
        (Ty.productMany candidate.parameterTypes)
        (Ty.productMany candidate.returnTypes))
    (catalog : SignatureCatalogWellFormed inferenceContext.signatures)
    (signatureParameters : SignatureParametersWellFormed
      inferenceContext.scope.genericOwner inferenceContext.typeParameters)
    (initialInvariant : RecursiveStatementInvariant wholeContext
      expectedReturn finalized initial semanticContext)
    (initializerInvariant : RecursiveStatementInvariant wholeContext
      expectedReturn finalized initializerResult.state loopContext)
    (actual : ActualContext wholeContext finalized frames loopContext)
    (operational : ActualStateInvariant initializerResult.state (evidenceState.toTypedSource roots))
    (actualCovered : ActualContext.Covers finalized frames (.statement result.id))
    (resultSubstitutionExtension : finalized.substitution.SemanticallyExtends
      result.state.inference.substitution)
    (resultExtension : SubtreePreserved finalized.substitution
      (result.state.toTypedSource roots) finalized.typedSource (.statement result.id))
    (rawResultExtension : RawSubtreePreserved (result.state.toTypedSource roots)
      (evidenceState.toTypedSource roots) (.statement result.id))
    (integerPatternsSubset : result.state.integerPatterns ⊆
      evidenceState.integerPatterns)
    (integerLiteralsSubset : result.state.integerLiterals ⊆
      evidenceState.integerLiterals)
    (requirementsSubset : result.state.requirements ⊆
      evidenceState.requirements)
    (parentCovered : TemplateScopeCovered finalized.typedSource
      semanticContext (.statement result.id))
    (loopAssumptionsEq : loopContext.assumptions =
      semanticContext.assumptions)
    (expressionSound : ActualInferExprFuelRootedSoundness fuel) :
    ExpressionHasType
      ((result.state.toTypedSource roots).applySubstitution
        finalized.substitution)
      loopContext inferredCondition.id .bool := by
  obtain ⟨actualInitializer, actualCondition, actualConditionState,
      bodyResult, postResult, actualInitializerSuccess,
      actualConditionSuccess, bodySuccess, postSuccess, initializerBelow,
      conditionSubstitutionExtension, conditionToParent,
      conditionPatternsSubset, conditionLiteralsSubset,
      conditionRequirementsSubset⟩ :=
    inferStatementFuel_success_forLoop_condition_resources statementEq
      allocationEq success signatureFormation functionsCanonical
      initialInvariant resultSubstitutionExtension integerPatternsSubset
      integerLiteralsSubset requirementsSubset
  rw [initializerSuccess] at actualInitializerSuccess
  have initializerEq := (Except.ok.inj actualInitializerSuccess).symm
  subst actualInitializer
  rw [conditionSuccess] at actualConditionSuccess
  obtain ⟨rfl, rfl⟩ := (Except.ok.inj actualConditionSuccess).symm
  obtain ⟨factInitializer, factCondition, factConditionState,
      factBody, factPost, factInitializerSuccess, factConditionSuccess,
      factBodySuccess, factPostSuccess, resultEq, containsRaw⟩ :=
    inferStatementFuel_success_forLoop_facts statementEq allocationEq
      success roots
  rw [initializerSuccess] at factInitializerSuccess
  have factInitializerEq := (Except.ok.inj factInitializerSuccess).symm
  subst factInitializer
  rw [conditionSuccess] at factConditionSuccess
  obtain ⟨rfl, rfl⟩ := (Except.ok.inj factConditionSuccess).symm
  have containsFinal : ContainsStatement finalized.typedSource result.id
      (({
        id := result.id
        span := statement.span
        type := result.type
        form := .forLoop initializerResult.items inferredCondition.id
          factPost.items factBody.statements
      } : StatementNode).applySubstitution finalized.substitution) :=
    resultExtension.containsStatement containsRaw
  have conditionCovered : TemplateScopeCovered finalized.typedSource
      loopContext (.expression inferredCondition.id) := by
    apply TemplateScopeCovered.forLoopCondition parentCovered
      resources.graph_closed
    · simpa [StatementNode.applySubstitution,
        StatementForm.applySubstitution] using containsFinal
    · exact loopAssumptionsEq
  have conditionTyped : ExpressionHasType
      ((result.state.toTypedSource roots).applySubstitution
        finalized.substitution)
      loopContext inferredCondition.id
      (finalized.substitution.apply inferredCondition.type) :=
    expressionSound conditionSuccess resources interfaces
      conditionSubstitutionExtension signaturesEq ownerEq parametersEq
      assumptionsEq signatureFormation functionsCanonical catalog
      signatureParameters (RecursiveExpressionInvariant.ofStatement
        initializerInvariant) actual operational (by
          intro expected member
          simp only [Option.mem_def] at member
          injection member with expectedEq
          subst expected
          simp [Ty.bool])
      (by intro type member; simp only [Option.mem_def] at member; cases member; exact TypeAdmissible.bool ((RecursiveExpressionInvariant.ofStatement initializerInvariant).typeParameterBinders
        (by simpa only [ownerEq, parametersEq] using signatureParameters)))
      (SubtreePreserved.ofTypingSourceExtends (conditionToParent.applySubstitution finalized.substitution))
      ((rawResultExtension.child (directChild_statement_reference containsRaw (by simp [StatementForm.references]))).monoBefore conditionToParent)
      conditionPatternsSubset conditionLiteralsSubset
      conditionRequirementsSubset conditionCovered
      (actualCovered.preserved_statement_reference containsRaw resultExtension (by simp [StatementForm.references]))
  have conditionTypeEq :
      finalized.substitution.apply inferredCondition.type = .bool := by
    simpa using Detail.inferExprFuel_expected_type_apply_eq
      conditionSuccess conditionSubstitutionExtension
  simpa [conditionTypeEq] using conditionTyped

end Solcore.SourceSemantics.SourceInferenceSoundness
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceSelectedForLoopSoundness
/-!
The recursive `for` statement step.  Each induction hypothesis is invoked
only on the actual initializer, condition, body, or post-header trace exposed
by the successful parent computation.  The completed local statement source
is separate from the whole-body finalization and coverage evidence.
-/

set_option autoImplicit false
set_option Elab.async false

namespace Solcore.SourceSemantics.SourceInferenceSoundness

open Frontend Frontend.SourceInference TypeSystem
open SourceInferenceStatementsSoundness

/-- Scoped soundness of one successful `for` statement, conditional only on
the four smaller-fuel recursive soundness propositions. -/
theorem actualInferStatementFuel_success_forLoop_rooted
    {fuel : Nat}
    {wholeContext inferenceContext : Frontend.SourceInference.Context}
    {wholeReturn expectedReturn : Ty}
    {statement : Syntax.Statement} {headerSpan : Syntax.SourceSpan}
    {initializer post : List Syntax.ForItem} {condition : Syntax.Expr}
    {body : Syntax.Block}
    {initial allocated evidenceState : State} {id : StatementId}
    {result : Detail.StatementResult} {roots : List NodeId}
    {finalized : Frontend.SourceInference.Result}
    {semanticContext : SourceSemantics.Context}
    {frames : List InitializedLetBinding}
    (statementEq : statement.value =
      .forLoop headerSpan initializer condition post body)
    (allocationEq : initial.allocateStatementId = (id, allocated))
    (success : Detail.inferStatementFuel (fuel + 1) inferenceContext
      statement expectedReturn initial = .ok result)
    (resources : FinalInferenceResources wholeContext wholeReturn
      evidenceState roots finalized)
    (interfaces : ExecutableCoercionInterfaces.SourceInterfaces wholeContext.signatures finalized.solvedRequirements finalized.typedSource)
    (signaturesEq : inferenceContext.signatures = wholeContext.signatures)
    (ownerEq : inferenceContext.scope.genericOwner =
      wholeContext.scope.genericOwner)
    (parametersEq : inferenceContext.typeParameters =
      wholeContext.typeParameters)
    (assumptionsEq : inferenceContext.assumptions =
      wholeContext.assumptions)
    (signatureFormation :
      ProgramSignatureFormationValidated inferenceContext.signatures)
    (functionsCanonical : ∀ candidate ∈
      inferenceContext.signatures.functions,
      candidate.scheme.body = .function
        (Ty.productMany candidate.parameterTypes)
        (Ty.productMany candidate.returnTypes))
    (catalog : SignatureCatalogWellFormed inferenceContext.signatures)
    (signatureParameters : SignatureParametersWellFormed
      inferenceContext.scope.genericOwner inferenceContext.typeParameters)
    (initialInvariant : RecursiveStatementInvariant wholeContext
      expectedReturn finalized initial semanticContext)
    (actual : ActualContext wholeContext finalized frames semanticContext)
    (operational : ActualStateInvariant initial (evidenceState.toTypedSource roots))
    (returnAdmissible : TypeAdmissible semanticContext (finalized.substitution.apply expectedReturn))
    (parentActualCovered : ActualContext.Covers finalized frames (.statement result.id))
    (resultSubstitutionExtension : finalized.substitution.SemanticallyExtends
      result.state.inference.substitution)
    (resultExtension : SubtreePreserved finalized.substitution
      (result.state.toTypedSource roots) finalized.typedSource (.statement result.id))
    (rawResultExtension : RawSubtreePreserved (result.state.toTypedSource roots)
      (evidenceState.toTypedSource roots) (.statement result.id))
    (integerPatternsSubset : result.state.integerPatterns ⊆
      evidenceState.integerPatterns)
    (integerLiteralsSubset : result.state.integerLiterals ⊆
      evidenceState.integerLiterals)
    (requirementsSubset : result.state.requirements ⊆
      evidenceState.requirements)
    (parentCovered : TemplateScopeCovered finalized.typedSource
      semanticContext (.statement result.id))
    (initializerSound : ActualInferForItemsFuelRootedSoundness fuel)
    (expressionSound : ActualInferExprFuelRootedSoundness fuel)
    (bodySound : ActualInferStatementsFuelRootedSoundness fuel)
    (postSound : ActualInferForItemsFuelRootedSoundness fuel) :
    ∃ finalContext facts,
      RecursiveStatementInvariant wholeContext expectedReturn finalized
        result.state finalContext ∧
      ActualContext wholeContext finalized frames finalContext ∧
      ActualStateInvariant result.state (evidenceState.toTypedSource roots) ∧
      StatementHasType
        ((result.state.toTypedSource roots).applySubstitution
          finalized.substitution)
        { returnType := finalized.substitution.apply expectedReturn
          loopDepth := inferenceContext.loopDepth }
        semanticContext result.id finalContext facts ∧
      StatementResultMatchesFactsAfterSubstitution finalized.substitution
        result facts := by
  obtain ⟨initializerResult, inferredCondition, conditionState, bodyResult,
    postResult, initializerSuccess, conditionSuccess, bodySuccess,
    postSuccess, resultEq, containsRaw⟩ :=
    inferStatementFuel_success_forLoop_facts statementEq allocationEq success
      roots
  obtain ⟨progressInitializer, progressCondition, progressConditionState,
    progressBody, progressPost, progressInitializerSuccess,
    progressConditionSuccess, progressBodySuccess, progressPostSuccess,
    initializerSubstitutionExtension, conditionSubstitutionExtension,
    bodySubstitutionExtension, postSubstitutionExtension,
    initializerLiteralsParent, conditionLiteralsParent,
    bodyLiteralsParent, postLiteralsParent⟩ :=
    inferStatementFuel_success_forLoop_child_progress statementEq
      allocationEq success signatureFormation functionsCanonical
      initialInvariant resultSubstitutionExtension
  rw [initializerSuccess] at progressInitializerSuccess
  have progressInitializerEq :=
    (Except.ok.inj progressInitializerSuccess).symm
  subst progressInitializer
  rw [conditionSuccess] at progressConditionSuccess
  obtain ⟨rfl, rfl⟩ :=
    (Except.ok.inj progressConditionSuccess).symm
  rw [bodySuccess] at progressBodySuccess
  have progressBodyEq := (Except.ok.inj progressBodySuccess).symm
  subst progressBody
  rw [postSuccess] at progressPostSuccess
  have progressPostEq := (Except.ok.inj progressPostSuccess).symm
  subst progressPost
  obtain ⟨provenanceInitializer, provenanceCondition,
    provenanceConditionState, provenanceBody, provenancePost,
    provenanceInitializerSuccess, provenanceConditionSuccess,
    provenanceBodySuccess, provenancePostSuccess,
    initializerProvenance, bodyProvenance, postProvenance⟩ :=
    inferStatementFuel_success_forLoop_child_provenance statementEq
      allocationEq success initialInvariant.nodesBelow roots
  rw [initializerSuccess] at provenanceInitializerSuccess
  have provenanceInitializerEq :=
    (Except.ok.inj provenanceInitializerSuccess).symm
  subst provenanceInitializer
  rw [conditionSuccess] at provenanceConditionSuccess
  obtain ⟨rfl, rfl⟩ :=
    (Except.ok.inj provenanceConditionSuccess).symm
  rw [bodySuccess] at provenanceBodySuccess
  have provenanceBodyEq := (Except.ok.inj provenanceBodySuccess).symm
  subst provenanceBody
  rw [postSuccess] at provenancePostSuccess
  have provenancePostEq := (Except.ok.inj provenancePostSuccess).symm
  subst provenancePost
  have allocatedInvariant : RecursiveStatementInvariant wholeContext
      expectedReturn finalized allocated semanticContext :=
    initialInvariant.allocateStatementId allocationEq
  have headerCovered := forItemsReferencesCovered_of_rootedForLoop
    containsRaw rfl resultExtension resources.graph_closed parentCovered
  have headerBindings := forItemsBindingsRetained_of_containedForLoop
    (rawResultExtension.containsStatement containsRaw) ⟨rfl, ⟨[], by simp⟩⟩
  have headerActualBindings := actualForItemsBindings_of_rootedForLoop containsRaw resultExtension parentActualCovered
  have initializerReference : ∀ item ∈ initializerResult.items, ∀ reference ∈ item.references,
      reference ∈ (StatementForm.forLoop initializerResult.items inferredCondition.id postResult.items bodyResult.statements).references := by
    intro item member reference present
    simp only [StatementForm.references, List.mem_append, List.mem_cons]
    exact .inl (.inl (.inl (List.mem_flatMap.mpr ⟨item, member, present⟩)))
  have postReference : ∀ item ∈ postResult.items, ∀ reference ∈ item.references,
      reference ∈ (StatementForm.forLoop initializerResult.items inferredCondition.id postResult.items bodyResult.statements).references := by
    intro item member reference present
    simp only [StatementForm.references, List.mem_append, List.mem_cons]
    exact .inl (.inr (List.mem_flatMap.mpr ⟨item, member, present⟩))
  have initializerSourceOwner :
      ((result.state.toTypedSource roots).applySubstitution
        finalized.substitution).owner = allocated.owner := by
    have ownerToInitializer := initializerProvenance.sourceExtension.owner_eq
    have initializerOwner :=
      Detail.inferForItemsFuel_preserves_owner initializerSuccess
    simpa [State.toTypedSource] using ownerToInitializer.trans initializerOwner
  obtain ⟨loopContext, initializerInvariant, initializerActual, initializerOperational, initializerTyping⟩ :=
    (initializerSound (control := {
        returnType := finalized.substitution.apply expectedReturn
        loopDepth := inferenceContext.loopDepth })
      initializerSuccess resources interfaces signaturesEq ownerEq parametersEq
      assumptionsEq signatureFormation functionsCanonical catalog
      signatureParameters allocatedInvariant actual (operational.allocateStatementId allocationEq) returnAdmissible initializerSubstitutionExtension
      (fun _ _ _ _ => SubtreePreserved.ofTypingSourceExtends
        (initializerProvenance.sourceExtension.applySubstitution finalized.substitution))
      (fun item member reference present => (rawResultExtension.child (directChild_statement_reference
        containsRaw (initializerReference item member reference present))).monoBefore initializerProvenance.sourceExtension)
      (List.Subset.trans initializerProvenance.integerPatternsSubset
        integerPatternsSubset)
      (List.Subset.trans initializerLiteralsParent integerLiteralsSubset)
      (List.Subset.trans initializerProvenance.requirementsSubset
        requirementsSubset)
      initializerSourceOwner headerCovered.1 headerBindings.1
      (fun item member reference present => parentActualCovered.preserved_statement_reference containsRaw
        resultExtension (initializerReference item member reference present)) headerActualBindings.1)
  have loopAssumptionsEq : loopContext.assumptions =
      semanticContext.assumptions :=
    forItemsHaveType_assumptions_eq initializerTyping
  have conditionTyping :=
    actualInferStatementFuel_success_forLoop_condition_rooted statementEq
      allocationEq success initializerSuccess conditionSuccess resources interfaces
      signaturesEq ownerEq parametersEq assumptionsEq signatureFormation
      functionsCanonical catalog signatureParameters initialInvariant
      initializerInvariant initializerActual initializerOperational parentActualCovered resultSubstitutionExtension resultExtension
      rawResultExtension integerPatternsSubset integerLiteralsSubset
      requirementsSubset parentCovered loopAssumptionsEq expressionSound
  have conditionInvariant : RecursiveStatementInvariant wholeContext
      expectedReturn finalized conditionState loopContext :=
    initializerInvariant.inferExprFuel conditionSuccess signatureFormation
      functionsCanonical (by
        intro expected member
        simp only [Option.mem_def] at member
        injection member with expectedEq
        subst expected
        simp [Ty.bool]) conditionSubstitutionExtension
  have loopReturn : TypeAdmissible loopContext (finalized.substitution.apply expectedReturn) :=
    StructuralSubstitution.TypeAdmissible.transportContext
      (initializerInvariant.signaturesEq.trans initialInvariant.signaturesEq.symm)
      (initializerInvariant.typeParametersEq.trans initialInvariant.typeParametersEq.symm)
      (initializerInvariant.declarationEq.trans initialInvariant.declarationEq.symm)
      (initializerActual.variables_eq.trans actual.variables_eq.symm)
      (initializerInvariant.residual.trans initialInvariant.residual.symm) returnAdmissible
  have conditionProperties := Detail.inferExprFuel_inferenceProperties
    initializerInvariant.ready signatureFormation functionsCanonical
    (by intro expected member; cases member; simp [Ty.bool]) conditionSuccess
  have conditionOperational := initializerOperational.ofExpression conditionSuccess conditionProperties.1.next_le
  have bodyCovered : ∀ child, child ∈ bodyResult.statements →
      TemplateScopeCovered finalized.typedSource loopContext
        (.statement child) := by
    intro child member
    have childReference : (.statement child : NodeId) ∈
        (StatementForm.forLoop initializerResult.items inferredCondition.id
          postResult.items bodyResult.statements).references := by
      simp [StatementForm.references, member]
    apply rooted_statement_child_covered
      containsRaw childReference resultExtension parentCovered
      resources.graph_closed
    intro predicate predicateMember
    simpa [loopAssumptionsEq] using predicateMember
  obtain ⟨bodyFinal, bodyFacts, bodyInvariant, bodyActual, bodyOperational, bodyTyping,
    bodyAgreement⟩ :=
    bodySound bodySuccess resources interfaces
      (by simpa using signaturesEq)
      (by simpa using ownerEq)
      (by simpa using parametersEq)
      (by simpa using assumptionsEq)
      signatureFormation functionsCanonical catalog signatureParameters
      conditionInvariant initializerActual conditionOperational loopReturn bodySubstitutionExtension
      (fun _ _ => SubtreePreserved.ofTypingSourceExtends
        (bodyProvenance.sourceExtension.applySubstitution finalized.substitution))
      (fun child member => (rawResultExtension.child (directChild_statement_reference containsRaw
        (by simp [StatementForm.references, member]))).monoBefore bodyProvenance.sourceExtension)
      (List.Subset.trans bodyProvenance.integerPatternsSubset
        integerPatternsSubset)
      (List.Subset.trans bodyLiteralsParent integerLiteralsSubset)
      (List.Subset.trans bodyProvenance.requirementsSubset
        requirementsSubset)
      bodyCovered (fun child member => parentActualCovered.preserved_statement_reference containsRaw resultExtension
        (by simp [StatementForm.references, member]))
  have conditionProperties := Detail.inferExprFuel_inferenceProperties
    initializerInvariant.ready signatureFormation functionsCanonical
    (by
      intro expected member
      simp only [Option.mem_def] at member
      injection member with expectedEq
      subst expected
      simp [Ty.bool]) conditionSuccess
  have conditionReturnBelow : expectedReturn.VariablesBelow
      conditionState.inference.next :=
    initializerInvariant.returnBelow.weaken conditionProperties.1.next_le
  have bodyProperties := Detail.inferStatementsFuel_inferenceProperties
    (context := { inferenceContext with
      loopDepth := inferenceContext.loopDepth + 1 })
    conditionProperties.2.1 signatureFormation functionsCanonical
    conditionReturnBelow bodySuccess
  have bodyBelow : bodyResult.state.NodesBelowNextOccurrence :=
    (Detail.inferStatementsFuel_occurrenceBoundExtends bodySuccess
      ).nodesBelowNextOccurrence bodyProvenance.initialBelow
  have nextLocalLe : initializerResult.state.nextLocal ≤
      bodyResult.state.nextLocal :=
    Nat.le_trans (Detail.inferExprFuel_nextLocal_le conditionSuccess)
      (Detail.inferStatementsFuel_nextLocal_le bodySuccess)
  have postInputInvariant : RecursiveStatementInvariant wholeContext
      expectedReturn finalized
      (bodyResult.state.restoreLexicalScope
        initializerResult.state.lexicalScope) loopContext :=
    initializerInvariant.restoreLexicalScope
      (conditionProperties.1.trans bodyProperties.1) bodyBelow nextLocalLe
      bodySubstitutionExtension
  have postOperational : ActualStateInvariant
      (bodyResult.state.restoreLexicalScope initializerResult.state.lexicalScope) (evidenceState.toTypedSource roots) := by
    obtain ⟨pending, ledger⟩ := bodyOperational.ledger
    refine ⟨⟨pending, ledger.restoreLexicalScope _⟩, initializerOperational.origins.congr_localBinders rfl, ?_, initializerOperational.sourceMonomorphic⟩
    exact activeQuantifiersBelowNext_transport initializerOperational.quantifiersBelow rfl
      (Nat.le_trans conditionProperties.1.next_le bodyProperties.1.next_le)
  have postCovered : ForItemsReferencesCovered finalized.typedSource
      finalized.substitution loopContext postResult.items := by
    intro item itemMember
    exact (headerCovered.2 item itemMember).transportAssumptions
      loopAssumptionsEq
  have postSourceOwner :
      ((result.state.toTypedSource roots).applySubstitution
        finalized.substitution).owner =
        (bodyResult.state.restoreLexicalScope
          initializerResult.state.lexicalScope).owner := by
    have ownerToPost := postProvenance.sourceExtension.owner_eq
    have postOwner := Detail.inferForItemsFuel_preserves_owner postSuccess
    simpa [State.toTypedSource] using ownerToPost.trans postOwner
  obtain ⟨postContext, postInvariant, postActual, postFinalOperational, postTyping⟩ :=
    (postSound (control := ({
        returnType := finalized.substitution.apply expectedReturn
        loopDepth := inferenceContext.loopDepth } : ControlContext).enterLoop)
      postSuccess resources interfaces
      (by simpa using signaturesEq)
      (by simpa using ownerEq)
      (by simpa using parametersEq)
      (by simpa using assumptionsEq)
      signatureFormation functionsCanonical catalog signatureParameters
      postInputInvariant initializerActual postOperational loopReturn postSubstitutionExtension
      (fun _ _ _ _ => SubtreePreserved.ofTypingSourceExtends
        (postProvenance.sourceExtension.applySubstitution finalized.substitution))
      (fun item member reference present => (rawResultExtension.child (directChild_statement_reference
        containsRaw (postReference item member reference present))).monoBefore postProvenance.sourceExtension)
      (List.Subset.trans postProvenance.integerPatternsSubset
        integerPatternsSubset)
      (List.Subset.trans postLiteralsParent integerLiteralsSubset)
      (List.Subset.trans postProvenance.requirementsSubset
        requirementsSubset)
      postSourceOwner postCovered headerBindings.2
      (fun item member reference present => parentActualCovered.preserved_statement_reference containsRaw
        resultExtension (postReference item member reference present)) headerActualBindings.2)
  have assembled : ∃ finalContext facts,
      RecursiveStatementInvariant wholeContext expectedReturn finalized result.state finalContext ∧
      StatementHasType ((result.state.toTypedSource roots).applySubstitution finalized.substitution)
        {returnType := finalized.substitution.apply expectedReturn, loopDepth := inferenceContext.loopDepth}
        semanticContext result.id finalContext facts ∧
      StatementResultMatchesFactsAfterSubstitution finalized.substitution result facts := by
    apply inferStatementFuel_success_forLoop_of_actual_typed_children
      statementEq allocationEq success signatureFormation functionsCanonical
      initialInvariant resultSubstitutionExtension
    intro actualInitializer actualCondition actualConditionState actualBody
      actualPost actualInitializerSuccess actualConditionSuccess
      actualBodySuccess actualPostSuccess
    rw [initializerSuccess] at actualInitializerSuccess
    have actualInitializerEq := (Except.ok.inj actualInitializerSuccess).symm
    subst actualInitializer
    rw [conditionSuccess] at actualConditionSuccess
    obtain ⟨rfl, rfl⟩ := (Except.ok.inj actualConditionSuccess).symm
    rw [bodySuccess] at actualBodySuccess
    have actualBodyEq := (Except.ok.inj actualBodySuccess).symm
    subst actualBody
    rw [postSuccess] at actualPostSuccess
    have actualPostEq := (Except.ok.inj actualPostSuccess).symm
    subst actualPost
    exact ⟨loopContext, bodyFinal, bodyFacts, postContext,
      initializerTyping, conditionTyping, bodyTyping, postTyping⟩
  obtain ⟨finalContext, facts, finalInvariant, typing, agreement⟩ := assembled
  have bindersEq : result.state.localBinders = initial.localBinders := by
    have allocatedBinders := congrArg LexicalScope.binders (Detail.allocateStatementId_success_lexicalScope allocationEq)
    simpa only [resultEq, State.recordNode, State.restoreLexicalScope, State.lexicalScope] using allocatedBinders
  have properties := Detail.inferStatementFuel_inferenceProperties initialInvariant.ready signatureFormation functionsCanonical initialInvariant.returnBelow success
  exact ⟨finalContext, facts, finalInvariant, actual.of_statement typing,
    operational.ofStatementPreservingBinders success bindersEq properties.1.next_le, typing, agreement⟩

theorem actualInferStatementFuelRootedSoundness_forLoop {fuel : Nat}
    (itemsSound : ActualInferForItemsFuelRootedSoundness fuel)
    (expressionSound : ActualInferExprFuelRootedSoundness fuel)
    (bodySound : ActualInferStatementsFuelRootedSoundness fuel) :
  ∀ {wholeContext inferenceContext : Frontend.SourceInference.Context}
    {wholeReturn expectedReturn : Ty}
    {statement : Syntax.Statement} {headerSpan : Syntax.SourceSpan}
    {initializer post : List Syntax.ForItem} {condition : Syntax.Expr} {body : Syntax.Block} {initial : State}
    {result : Detail.StatementResult} {evidenceState : State}
    {roots : List NodeId}
    {finalized : Frontend.SourceInference.Result}
    {semanticSource : TypedSource}
    {frames : List InitializedLetBinding}
    {semanticContext : SourceSemantics.Context},
    statement.value = .forLoop headerSpan initializer condition post body →
    Detail.inferStatementFuel (fuel + 1) inferenceContext statement expectedReturn
      initial = .ok result →
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
    finalized.substitution.SemanticallyExtends
      result.state.inference.substitution →
    SubtreePreserved finalized.substitution
      (result.state.toTypedSource roots) semanticSource (.statement result.id) →
    RawSubtreePreserved (result.state.toTypedSource roots)
      (evidenceState.toTypedSource roots) (.statement result.id) →
    result.state.integerPatterns ⊆ evidenceState.integerPatterns →
    result.state.integerLiterals ⊆ evidenceState.integerLiterals →
    result.state.requirements ⊆ evidenceState.requirements →
    TemplateScopeCovered finalized.typedSource semanticContext
      (.statement result.id) →
    ActualContext.Covers finalized frames (.statement result.id) →
    ∃ finalContext facts,
      RecursiveStatementInvariant wholeContext expectedReturn finalized
        result.state finalContext ∧
      ActualContext wholeContext finalized frames finalContext ∧
      ActualStateInvariant result.state (evidenceState.toTypedSource roots) ∧
      StatementHasType
        ((result.state.toTypedSource roots).applySubstitution
          finalized.substitution)
        { returnType := finalized.substitution.apply expectedReturn
          loopDepth := inferenceContext.loopDepth }
        semanticContext result.id finalContext facts ∧
      StatementResultMatchesFactsAfterSubstitution finalized.substitution
        result facts := by
  intro wholeContext inferenceContext wholeReturn expectedReturn statement headerSpan initializer post condition body
    initial result evidenceState roots finalized semanticSource frames semanticContext statementEq success resources
    interfaces signaturesEq ownerEq parametersEq assumptionsEq formation functions catalog canonical invariant actual
    operational returnAdmissible extension _semantic raw patterns literals requirements covered actualCovered
  generalize allocationEq : initial.allocateStatementId = pair
  obtain ⟨id, allocated⟩ := pair
  exact actualInferStatementFuel_success_forLoop_rooted statementEq allocationEq success resources interfaces
    signaturesEq ownerEq parametersEq assumptionsEq formation functions catalog canonical invariant actual operational
    returnAdmissible actualCovered extension (raw.finalized resources) raw patterns literals requirements covered
    itemsSound expressionSound bodySound itemsSound

end Solcore.SourceSemantics.SourceInferenceSoundness
end
