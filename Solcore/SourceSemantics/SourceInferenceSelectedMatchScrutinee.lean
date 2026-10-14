import Solcore.SourceSemantics.SourceInferenceSelectedExpressionList
import Solcore.SourceSemantics.SourceInferenceActualRootedContracts

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1600000

namespace Solcore.SourceSemantics.SourceInferenceSoundness
open Frontend Frontend.SourceInference TypeSystem

/-- The actual common match-scrutinee traversal retains a single expression,
or its actual ordered children under the generated ordinary tuple. -/
theorem actualInferMatchScrutineesFuelRootedSoundness {fuel : Nat}
    (recursive : ∀ smaller, smaller < fuel + 1 → ActualInferExprFuelRetainedSoundness smaller) :
∀ {wholeContext inferenceContext : Frontend.SourceInference.Context}
    {wholeReturn : Ty} {span : Syntax.SourceSpan} {sources : List Syntax.Expr}
    {initial resultState evidenceState : State}
    {inferred : InferredExpression} {roots : List NodeId}
    {finalized : Frontend.SourceInference.Result}
    {semanticSource : TypedSource}
    {frames : List InitializedLetBinding}
    {semanticContext : SourceSemantics.Context},
    inferMatchScrutineesFuel fuel inferenceContext span sources initial =
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
    SubtreePreserved finalized.substitution
      (resultState.toTypedSource roots) semanticSource (.expression inferred.id) →
    RawSubtreePreserved (resultState.toTypedSource roots)
      (evidenceState.toTypedSource roots) (.expression inferred.id) →
    resultState.integerPatterns ⊆ evidenceState.integerPatterns →
    resultState.integerLiterals ⊆ evidenceState.integerLiterals →
    resultState.requirements ⊆ evidenceState.requirements →
    TemplateScopeCovered finalized.typedSource semanticContext
      (.expression inferred.id) →
    ActualContext.Covers finalized frames (.expression inferred.id) →
    ExpressionHasType semanticSource semanticContext inferred.id
      (finalized.substitution.apply inferred.type) := by
  intro wholeContext inferenceContext wholeReturn span sources initial resultState evidenceState inferred roots finalized
    semanticSource frames semanticContext success resources interfaces extension signaturesEq ownerEq parametersEq assumptionsEq
    formation functions catalog canonical invariant actual operational semantic raw patterns literals requirements covered actualCovered
  have finalPreserved : SubtreePreserved finalized.substitution (resultState.toTypedSource roots)
      finalized.typedSource (.expression inferred.id) := by
    rw [resources.source_eq]
    exact raw.substituted finalized.substitution
  have generated {elements : List InferredExpression} {elementsState allocated : State} {tupleId : ExpressionId}
      (elementsSuccess : Detail.inferExprsFuel fuel inferenceContext sources initial = .ok (elements, elementsState))
      (allocation : elementsState.allocateExpressionId = (tupleId, allocated))
      (resultEq : (inferred, resultState) =
        (⟨tupleId, Ty.productMany (elements.map (·.type))⟩,
          allocated.recordNode (.expression {
            id := tupleId, span, type := Ty.productMany (elements.map (·.type)),
            form := .tuple (elements.map (·.id)) }))) :
      ExpressionHasType semanticSource semanticContext inferred.id
        (finalized.substitution.apply inferred.type) := by
    cases resultEq
    let node : ExpressionNode := {
      id := tupleId, span, type := Ty.productMany (elements.map (·.type)),
      form := .tuple (elements.map (·.id)) }
    have contains : ContainsExpression ((allocated.recordNode (.expression node)).toTypedSource roots) tupleId node :=
      recordNode_containsExpression allocated node
    have edge : ∀ element ∈ elements, DirectChild
        ((allocated.recordNode (.expression node)).toTypedSource roots)
        (.expression tupleId) (.expression element.id) := by
      intro element member
      refine ⟨.expression node, ⟨contains.1, rfl⟩, ?_⟩
      simp only [nodeChildIds, Node.references, node, ExpressionForm.references]
      exact List.mem_map.mpr ⟨element.id, List.mem_map.mpr ⟨element, member, rfl⟩, rfl⟩
    have elementsToParent : TypingSourceExtends (elementsState.toTypedSource roots)
        ((allocated.recordNode (.expression node)).toTypedSource roots) := by
      have allocatedEq : elementsState.allocateExpressionId.2 = allocated := congrArg Prod.snd allocation
      rw [← allocatedEq]
      exact ⟨rfl, ⟨[.expression node], rfl⟩⟩
    have containsFinal := finalPreserved.subgraph.containsExpression
      (FlexibleSubstitution.ContainsExpression.applySubstitution finalized.substitution contains) (.inl rfl)
    have finalEdge : ∀ element ∈ elements, DirectChild finalized.typedSource
        (.expression tupleId) (.expression element.id) := by
      intro element member
      refine ⟨.expression (node.applySubstitution finalized.substitution),
        ⟨containsFinal.1, rfl⟩, ?_⟩
      simpa [nodeChildIds, Node.references, node, ExpressionNode.applySubstitution,
        ExpressionForm.applySubstitution, ExpressionForm.references] using
        (List.mem_map.mpr ⟨element.id, List.mem_map.mpr ⟨element, member, rfl⟩, rfl⟩ :
          NodeId.expression element.id ∈ (elements.map (·.id)).map NodeId.expression)
    have elementsExtension : finalized.substitution.SemanticallyExtends elementsState.inference.substitution := by
      have allocatedEq : elementsState.allocateExpressionId.2 = allocated := congrArg Prod.snd allocation
      have same : allocated.inference.substitution = elementsState.inference.substitution := by
        rw [← allocatedEq]
        rfl
      simpa only [State.recordNode, same] using extension
    have elementPatterns : elementsState.integerPatterns ⊆ evidenceState.integerPatterns := by
      have allocatedEq : elementsState.allocateExpressionId.2 = allocated := congrArg Prod.snd allocation
      have same : allocated.integerPatterns = elementsState.integerPatterns := by
        rw [← allocatedEq]
        rfl
      simpa only [State.recordNode, same] using patterns
    have elementLiterals : elementsState.integerLiterals ⊆ evidenceState.integerLiterals := by
      have allocatedEq : elementsState.allocateExpressionId.2 = allocated := congrArg Prod.snd allocation
      have same : allocated.integerLiterals = elementsState.integerLiterals := by
        rw [← allocatedEq]
        rfl
      simpa only [State.recordNode, same] using literals
    have elementRequirements : elementsState.requirements ⊆ evidenceState.requirements := by
      have allocatedEq : elementsState.allocateExpressionId.2 = allocated := congrArg Prod.snd allocation
      have same : allocated.requirements = elementsState.requirements := by
        rw [← allocatedEq]
        rfl
      simpa only [State.recordNode, same] using requirements
    have typed := actualInferExprsFuelFinalSubtreeSoundness fuel
      (fun smaller less => recursive smaller (Nat.lt_trans less (Nat.lt_succ_self fuel)))
      elementsSuccess resources interfaces elementsExtension signaturesEq ownerEq parametersEq assumptionsEq
      formation functions catalog canonical invariant actual operational
      (fun element member => (semantic.child (edge element member)).monoBefore elementsToParent)
      (fun element member => (finalPreserved.child (edge element member)).monoBefore elementsToParent)
      (fun element member => ((raw.child (edge element member)).monoBefore elementsToParent).proper)
      elementPatterns elementLiterals elementRequirements
      (fun element member => covered.expressionChild resources.graph_closed (finalEdge element member))
      (fun element member => actualCovered.directChild (finalEdge element member))
    have containsSemantic := semantic.subgraph.containsExpression
      (FlexibleSubstitution.ContainsExpression.applySubstitution finalized.substitution contains) (.inl rfl)
    have rawAdmissible : TypeAdmissible semanticContext
        (finalized.substitution.apply (Ty.productMany (elements.map (·.type)))) := by
      simpa [FlexibleSubstitution.apply_productMany, List.map_map, Function.comp_def] using
        typed.product_type_admissible (invariant.typeParameterBinders (by
          simpa [ownerEq, parametersEq] using canonical))
    apply ExpressionHasType.ofOrdinary (owned := []) containsSemantic
    · simpa [node, ExpressionNode.applySubstitution, ExpressionForm.applySubstitution,
        FlexibleSubstitution.apply_productMany, List.map_map, Function.comp_def] using
        ExpressionFormHasRawType.tuple typed
    · simpa [node, ExpressionNode.applySubstitution, FlexibleSubstitution.apply_productMany,
        List.map_map, Function.comp_def] using rawAdmissible
    · simpa [node, ExpressionNode.applySubstitution, FlexibleSubstitution.apply_productMany,
        List.map_map, Function.comp_def] using rawAdmissible
    · intro requirement member
      simp at member
    · simpa [node, ExpressionNode.applySubstitution, FlexibleSubstitution.apply_productMany,
        List.map_map, Function.comp_def] using
        (CoercionPathValid.nil (context := semanticContext)
          (Ty.productMany (elements.map fun argument => finalized.substitution.apply argument.type)))
    · simp [node, ExpressionNode.applySubstitution, coercionRequirementIds]
  cases sources with
  | nil =>
    unfold inferMatchScrutineesFuel at success
    cases elementsSuccess : Detail.inferExprsFuel fuel inferenceContext [] initial with
    | error error => simp [elementsSuccess, bind, Except.bind] at success
    | ok pair =>
      obtain ⟨elements, elementsState⟩ := pair
      simp only [elementsSuccess, bind, Except.bind] at success
      obtain ⟨tupleId, allocated⟩ := elementsState.allocateExpressionId
      exact generated elementsSuccess rfl (Except.ok.inj success).symm
  | cons first rest =>
    cases rest with
    | nil =>
      have childSuccess : Detail.inferExprFuel fuel inferenceContext first none initial = .ok (inferred, resultState) := by
        simpa [inferMatchScrutineesFuel] using success
      exact actualInferExprFuelFinalSubtreeSoundness_of_retainedSoundness
        (recursive fuel (Nat.lt_succ_self fuel)) childSuccess resources interfaces extension
        signaturesEq ownerEq parametersEq assumptionsEq formation functions catalog canonical invariant actual operational
        (by simp) (by simp) semantic finalPreserved raw.proper patterns literals requirements covered actualCovered
    | cons second rest =>
      unfold inferMatchScrutineesFuel at success
      cases elementsSuccess : Detail.inferExprsFuel fuel inferenceContext (first :: second :: rest) initial with
      | error error => simp [elementsSuccess, bind, Except.bind] at success
      | ok pair =>
        obtain ⟨elements, elementsState⟩ := pair
        simp only [elementsSuccess, bind, Except.bind] at success
        obtain ⟨tupleId, allocated⟩ := elementsState.allocateExpressionId
        exact generated elementsSuccess rfl (Except.ok.inj success).symm

end Solcore.SourceSemantics.SourceInferenceSoundness
