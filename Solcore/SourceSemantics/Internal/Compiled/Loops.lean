import Solcore.SourceSemantics.Internal.Compiled.BodySelection
import Solcore.SourceSemantics.Internal.Compiled.Expressions
import Solcore.SourceSemantics.Internal.Compiled.OperationalState
import Solcore.SourceSemantics.Internal.Selected.Lets
import Solcore.SourceSemantics.Internal.Compiled.Contracts
import Solcore.SourceSemantics.Internal.Compiled.Statements
import Solcore.SourceSemantics.Internal.Compiled.InitializerOccurrences
import Solcore.SourceSemantics.Internal.Privacy.Lifetimes
import Solcore.SourceSemantics.Internal.Inference.StatementControl
import Solcore.SourceSemantics.Internal.Selected.Loops

/-!
# For and while statements

The complete for-loop consumer follows the actual initializer, condition, body and post calls.
Header items use their actual result and the same selected final source.
-/

section
-- leanmerge: from Solcore.SourceSemantics.SourceCompiledGeneralizedForAnnotatedInitializer
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledGeneralizedSoundness
open Frontend SourceInference TypeSystem SourceInferenceSoundness
open SourceCompiledLocalFinalization SourceInferenceExecution

theorem forItem_annotatedInitialized_for {callProvenance : CallIndex → Prop}
    {raw : Workspace.RawWorkspace} {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel childFuel : Nat}
    {selected : BodySelection compiled row fuel}
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    (descend : ChildClosed callProvenance)
    (expressionSound : ExpressionRootedSoundnessFor callProvenance selected childFuel)
    {inferenceContext : SourceInference.Context} {item : Syntax.ForItem}
    {name : Syntax.Identifier} {sourceType : Syntax.TypeExpr} {initializer : Syntax.Expr}
    {expectedReturn : Ty} {initial final : State} {inferred : ForItemForm}
    {frames : List InitializedLetBinding} {target : SourceSemantics.Context}
    (here : callProvenance (.forItem (childFuel + 1) inferenceContext item initial inferred final))
    (form : item.value = .letDecl name (some sourceType) (some initializer))
    (boundary : ForItemBoundary selected (childFuel + 1) inferenceContext item expectedReturn
      initial inferred final frames target) :
    ForItemConclusion selected inferenceContext expectedReturn inferred final frames target := by
  have signaturesEq := boundary.scope.signatures
  have parametersEq := boundary.scope.parameters
  have ownerEq := boundary.scope.owner
  have formation := boundary.scope.formation checked
  have functions := boundary.scope.functionsCanonical checked
  have catalog := boundary.scope.catalog checked
  have canonical := boundary.scope.canonical checked
  have semanticSignatures : target.signatures = inferenceContext.signatures :=
    (RecursiveExpressionInvariant.ofStatement boundary.invariant).signatures_eq_whole.trans signaturesEq.symm
  have semanticParameters : target.typeParameters = inferenceContext.typeParameters :=
    boundary.invariant.typeParametersEq.trans parametersEq.symm
  have semanticOwner : target.currentDeclaration = some inferenceContext.scope.genericOwner := by
    rw [ownerEq]
    exact boundary.invariant.declarationEq
  obtain ⟨resolvedType, child, initializerState, locals, valueType, generalized, binding,
    resolution, childSuccess, localsEq, valueEq, generalizedEq, bindingEq, resultEq⟩ :=
    inferForItemFuel_success_letAnnotatedInitialized_facts form boundary.accepted
  have sameItem : inferred = .letDecl binding.1 (some child.id) := congrArg Prod.fst resultEq
  have sameState : final = binding.2 := congrArg Prod.snd resultEq
  subst inferred
  subst final
  have expectedBelow : ∀ type ∈ (some resolvedType : Option Ty), type.VariablesBelow initial.inference.next := by
    intro type member
    cases Option.mem_def.mp member
    exact Detail.resolveSourceType_success_variablesBelow resolution _
  have childProperties := Detail.inferExprFuel_inferenceProperties boundary.invariant.ready formation functions expectedBelow childSuccess
  have rawExpected := inferExprFuel_success_expected_type_afterProgress childSuccess
    (State.InferenceProgress.refl childProperties.2.1.solved)
  have annotationValueEq : valueType = initializerState.resolve resolvedType := valueEq.trans rawExpected
  obtain ⟨typeWellFormed, closedScheme, closedRequirements, generalizes⟩ :=
    resolvedAnnotationBinderFacts_afterSubstitution (outer := selected.body.finalized.substitution)
      resolution annotationValueEq generalizedEq bindingEq canonical semanticSignatures semanticParameters semanticOwner
  have childExpected : ∀ type ∈ (some resolvedType : Option Ty),
      TypeAdmissible target (selected.body.finalized.substitution.apply type) := by
    intro type member
    cases Option.mem_def.mp member
    rw [Detail.resolveSourceType_success_apply_eq_self selected.body.finalized.substitution resolution]
    exact TypeAdmissible.ofWellFormed typeWellFormed
  have childMember : (.expression child.id : NodeId) ∈ (ForItemForm.letDecl binding.1 (some child.id)).references := by
    simp [ForItemForm.references]
  have initializerContextEq : localSchemeInitializerContext target
      (binding.1.applySubstitution selected.body.finalized.substitution) = target := by
    rw [localSchemeInitializerContext_eq_withTypeVariables _ _ closedRequirements]
    simp only [closedScheme, Scheme.mono, Context.withTypeVariables, List.append_nil]
  have childCovered : TemplateScopeCovered selected.body.finalized.typedSource target (.expression child.id) := by
    have selectedCoverage := boundary.covered _ childMember
    simpa only [forItemCoverageContext, initializerContextEq] using selectedCoverage
  have childToFinal : TypingSourceExtends (initializerState.toTypedSource (bodyRoots selected)) (binding.2.toTypedSource (bodyRoots selected)) := by
    rw [← bindingEq]
    exact ⟨rfl, ⟨[], by simp [State.allocateBinder, State.withLocals, State.toTypedSource]⟩⟩
  have childExtension : selected.body.finalized.substitution.SemanticallyExtends initializerState.inference.substitution := by
    simpa [← bindingEq, State.allocateBinder, State.withLocals] using boundary.extension
  have childPatterns : initializerState.integerPatterns ⊆ selected.body.returned.integerPatterns := by
    simpa [← bindingEq, State.allocateBinder, State.withLocals] using boundary.integerPatterns
  have childLiterals : initializerState.integerLiterals ⊆ selected.body.returned.integerLiterals := by
    simpa [← bindingEq, State.allocateBinder, State.withLocals] using boundary.integerLiterals
  have childRequirements : initializerState.requirements ⊆ selected.body.returned.requirements := by
    simpa [← bindingEq, State.allocateBinder, State.withLocals] using boundary.requirements
  have childHere := descend here (.forItem_initializer boundary.accepted form (.present resolution) childSuccess)
  have childTyped := expressionSound childHere ({
    accepted := childSuccess
    interfaces := boundary.interfaces
    extension := childExtension
    scope := boundary.scope
    invariant := RecursiveExpressionInvariant.ofStatement boundary.invariant
    actual := boundary.actual
    operational := boundary.operational
    expectedBelow := expectedBelow
    expectedAdmissible := childExpected
    expectedSafe := by
      intro binder member type typeMember
      cases Option.mem_def.mp typeMember
      exact ProtectedVariables.safe_closed _ _ (Detail.resolveSourceType_success_variablesBelow resolution 0)
    rawSubtree := ((boundary.rawReferences _ childMember).monoBefore childToFinal)
    integerPatterns := childPatterns
    integerLiterals := childLiterals
    requirements := childRequirements
    covered := childCovered
    actualCovered := boundary.actualCovered _ childMember
  } : RootedExpressionBoundary selected childFuel inferenceContext initializer (some resolvedType)
    initial child initializerState frames target)
  have certificate : ActualAnnotatedInitializedForItemCertificate childFuel inferenceContext name sourceType initializer initial
      (.letDecl binding.1 (some child.id), binding.2) selected.body.finalized.typedSource target selected.body.finalized.substitution :=
    ⟨resolvedType, child, initializerState, locals, valueType, generalized, binding,
      resolution, childSuccess, localsEq, valueEq, generalizedEq, bindingEq, rfl, childTyped⟩
  obtain ⟨finalContext, finalInvariant, typing⟩ := inferForItemFuel_success_letAnnotatedInitialized_of_certificate
    boundary.accepted formation functions canonical semanticSignatures semanticParameters semanticOwner boundary.invariant boundary.owner boundary.extension
      (control := {returnType := selected.body.finalized.substitution.apply expectedReturn, loopDepth := inferenceContext.loopDepth}) certificate
  have resolvedByState : initializerState.resolve resolvedType = resolvedType := by
    simpa [State.resolve, InferState.resolve] using
      Detail.resolveSourceType_success_apply_eq_self initializerState.inference.substitution resolution
  have valueClosed : valueType.freeVariables = [] := by
    rw [annotationValueEq, resolvedByState]
    exact StructuralSubstitution.TypeWellFormed.freeVariables_eq_nil typeWellFormed
  have schemeEq : generalized.scheme = .mono valueType := by
    rw [generalizedEq]
    exact (generalizeValue_closed_facts initializerState locals initial.nextRequirement valueType target valueClosed).1
  have requirementsEq : generalized.requirements = [] := by
    rw [generalizedEq]
    exact (generalizeValue_closed_facts initializerState locals initial.nextRequirement valueType target valueClosed).2.1
  have bindingOperational : GeneralizedActualStateInvariant binding.2 (evidenceSource selected) := by
    rw [← bindingEq, schemeEq, requirementsEq]
    have childOperational := boundary.operational.ofExpression boundary.invariant.ready catalog formation functions
      expectedBelow (by
        intro binder member type typeMember
        cases Option.mem_def.mp typeMember
        exact ProtectedVariables.safe_closed _ _ (Detail.resolveSourceType_success_variablesBelow resolution 0)) childSuccess
    apply (childOperational.withLocals locals).allocateMonoBinder
    intro binder member
    exact ProtectedVariables.safe_closed _ _ (by intro metavariable present; simp [valueClosed] at present)

  exact ⟨finalContext, finalInvariant, boundary.actual.of_forItem typing, bindingOperational, typing⟩

theorem forItem_annotatedInitialized
    {raw : Workspace.RawWorkspace} {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel childFuel : Nat}
    {selected : BodySelection compiled row fuel}
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    (expressionSound : ExpressionRootedSoundness selected childFuel)
    {inferenceContext : SourceInference.Context} {item : Syntax.ForItem}
    {name : Syntax.Identifier} {sourceType : Syntax.TypeExpr} {initializer : Syntax.Expr}
    {expectedReturn : Ty} {initial final : State} {inferred : ForItemForm}
    {frames : List InitializedLetBinding} {target : SourceSemantics.Context}
    (form : item.value = .letDecl name (some sourceType) (some initializer))
    (boundary : ForItemBoundary selected (childFuel + 1) inferenceContext item expectedReturn
      initial inferred final frames target) :
    ForItemConclusion selected inferenceContext expectedReturn inferred final frames target := by
  exact forItem_annotatedInitialized_for (callProvenance := fun _ => True) checked true_childClosed
    (fun _ boundary => expressionSound boundary) True.intro form boundary

end Solcore.SourceSemantics.SourceCompiledGeneralizedSoundness
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceCompiledGeneralizedForAnnotation
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledGeneralizedSoundness
open Frontend SourceInference TypeSystem SourceInferenceSoundness
open SourceCompiledLocalFinalization

theorem forItem_annotatedUninitialized
    {raw : Workspace.RawWorkspace} {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel childFuel : Nat}
    {selected : BodySelection compiled row fuel}
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    {inferenceContext : SourceInference.Context} {item : Syntax.ForItem}
    {name : Syntax.Identifier} {sourceType : Syntax.TypeExpr}
    {expectedReturn : Ty} {initial final : State} {inferred : ForItemForm}
    {frames : List InitializedLetBinding} {target : SourceSemantics.Context}
    (form : item.value = .letDecl name (some sourceType) none)
    (boundary : ForItemBoundary selected (childFuel + 1) inferenceContext item expectedReturn
      initial inferred final frames target) :
    ForItemConclusion selected inferenceContext expectedReturn inferred final frames target := by
  have signaturesEq := (RecursiveExpressionInvariant.ofStatement boundary.invariant).signatures_eq_whole.trans
    boundary.scope.signatures.symm
  have parametersEq := boundary.invariant.typeParametersEq.trans boundary.scope.parameters.symm
  have ownerEq : target.currentDeclaration = some inferenceContext.scope.genericOwner := by
    rw [boundary.scope.owner]
    exact boundary.invariant.declarationEq
  obtain ⟨finalContext, finalInvariant, typing⟩ :=
    inferForItemFuel_success_letAnnotatedUninitialized_scoped form boundary.accepted
      (boundary.scope.formation checked) (boundary.scope.functionsCanonical checked)
      (boundary.scope.canonical checked) signaturesEq parametersEq ownerEq
      boundary.invariant boundary.owner boundary.extension
  obtain ⟨resolvedType, locals, valueType, generalized, binding,
      resolution, _localsEq, valueTypeEq, generalizedEq, bindingEq, resultEq⟩ :=
    inferForItemFuel_success_letAnnotatedUninitialized_facts form boundary.accepted
  obtain ⟨wellFormed, _closedScheme, _closedRequirements, _generalizes⟩ :=
    resolvedAnnotationBinderFacts_afterSubstitution
      (target := target) (outer := selected.body.finalized.substitution)
      resolution valueTypeEq generalizedEq bindingEq (boundary.scope.canonical checked)
      signaturesEq parametersEq ownerEq
  have resolvedByState : initial.resolve resolvedType = resolvedType := by
    simpa [State.resolve, InferState.resolve] using
      Detail.resolveSourceType_success_apply_eq_self initial.inference.substitution resolution
  have valueClosed : valueType.freeVariables = [] := by
    rw [valueTypeEq, resolvedByState]
    exact StructuralSubstitution.TypeWellFormed.freeVariables_eq_nil wellFormed
  have schemeEq : generalized.scheme = .mono valueType := by
    rw [generalizedEq]
    exact (generalizeValue_closed_facts initial locals initial.nextRequirement valueType target valueClosed).1
  have requirementsEq : generalized.requirements = [] := by
    rw [generalizedEq]
    exact (generalizeValue_closed_facts initial locals initial.nextRequirement valueType target valueClosed).2.1
  have bindingOperational : GeneralizedActualStateInvariant binding.2 (evidenceSource selected) := by
    rw [← bindingEq, schemeEq, requirementsEq]
    apply (boundary.operational.withLocals locals).allocateMonoBinder
    intro binder member
    exact ProtectedVariables.safe_closed _ _
      (by intro metavariable present; simp [valueClosed] at present)
  have stateEq : final = binding.2 := congrArg Prod.snd resultEq
  have operational : GeneralizedActualStateInvariant final (evidenceSource selected) :=
    stateEq ▸ bindingOperational
  exact ⟨finalContext, finalInvariant, boundary.actual.of_forItem typing, operational, typing⟩

end Solcore.SourceSemantics.SourceCompiledGeneralizedSoundness
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceCompiledGeneralizedForBitNot
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledGeneralizedSoundness
open Frontend SourceInference TypeSystem SourceInferenceSoundness
open SourceCompiledLocalFinalization SourceInferenceExecution

theorem forItem_assignBitNot_for
    {raw : Workspace.RawWorkspace} {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel childFuel : Nat}
    {selected : BodySelection compiled row fuel}
    {provenance : CallIndex → Prop}
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    (descend : ChildClosed provenance)
    (placeSound : PlaceRootedSoundnessFor provenance selected childFuel)
    {inferenceContext : SourceInference.Context} {item : Syntax.ForItem}
    {expression : Syntax.Expr} {operatorSpan : Syntax.SourceSpan}
    {expectedReturn : Ty} {initial final : State} {inferred : ForItemForm}
    {frames : List InitializedLetBinding} {target : SourceSemantics.Context}
    (here : provenance (.forItem (childFuel + 1) inferenceContext item initial inferred final))
    (form : item.value = .assignBitNot expression operatorSpan)
    (boundary : ForItemBoundary selected (childFuel + 1) inferenceContext item expectedReturn
      initial inferred final frames target) :
    ForItemConclusion selected inferenceContext expectedReturn inferred final frames target := by
  obtain ⟨place, placeState, unified, placeSuccess, unifySuccess, resultEq⟩ :=
    inferForItemFuel_success_assignBitNot_facts form boundary.accepted
  have sameItem := congrArg Prod.fst resultEq
  have sameState := congrArg Prod.snd resultEq
  dsimp only at sameItem sameState
  subst inferred
  subst final
  have placeToFinal : TypingSourceExtends
      (placeState.toTypedSource (bodyRoots selected)) (unified.toTypedSource (bodyRoots selected)) := by
    constructor
    · exact congrArg State.Header.owner (Detail.unify_state_header unifySuccess)
    · change placeState.nodes <+: unified.nodes
      rw [← (Detail.unify_occurrenceState_eq unifySuccess).1]
      exact ⟨[], by simp⟩
  have properties := Detail.inferPlaceFuel_inferenceProperties boundary.invariant.ready
    (boundary.scope.formation checked) (boundary.scope.functionsCanonical checked) placeSuccess
  have placeExtension := boundary.extension.trans
    (Detail.unify_inferenceProgress properties.2.1.solved properties.2.2
      (Ty.variablesBelow_constructor _ _) unifySuccess).substitution_extends
  have keyMember : ∀ key, .expression key ∈ place.references →
      (.expression key : NodeId) ∈ (ForItemForm.assignBitNot
        {target := {place with type := unified.resolve place.type}}).references := by
    intro key member
    simpa [ForItemForm.references, AssignmentResolution.references, PlaceResolution.references] using member
  obtain ⟨placeTyped, _placeOperational, _placeSafe⟩ := placeSound (descend here (ChildStep.forItem_bitnot boundary.accepted form placeSuccess)) ({
    accepted := placeSuccess
    interfaces := boundary.interfaces
    extension := placeExtension
    scope := boundary.scope
    invariant := RecursiveExpressionInvariant.ofStatement boundary.invariant
    actual := boundary.actual
    operational := boundary.operational
    rawKeys := fun key member => (boundary.rawReferences _ (keyMember key member)).monoBefore placeToFinal
    integerPatterns := by simpa only [Detail.unify_integerPatterns unifySuccess] using boundary.integerPatterns
    integerLiterals := by simpa only [Detail.unify_integerLiterals unifySuccess] using boundary.integerLiterals
    requirements := by simpa only [Detail.unify_requirements_eq unifySuccess] using boundary.requirements
    covered := fun key member => boundary.covered _ (keyMember key member)
    actualCovered := fun key member => boundary.actualCovered _ (keyMember key member)
  } : PlaceBoundary selected childFuel inferenceContext expression initial place placeState frames target)
  obtain ⟨finalContext, finalInvariant, typing⟩ := inferForItemFuel_success_assignBitNot_of_certificate
    boundary.accepted (boundary.scope.formation checked) (boundary.scope.functionsCanonical checked)
    boundary.invariant boundary.extension ⟨place, placeState, unified, placeSuccess, unifySuccess, rfl, placeTyped⟩
  have binders : unified.localBinders = initial.localBinders :=
    (congrArg LexicalScope.binders (Detail.unify_preserves_lexicalScope unifySuccess)).trans
      (congrArg LexicalScope.binders (Detail.inferPlaceFuel_success_lexicalScope_eq placeSuccess))
  exact ⟨finalContext, finalInvariant, boundary.actual.of_forItem typing,
    boundary.operational.ofForItemPreservingBinders boundary.invariant.ready
      (boundary.scope.catalog checked) (boundary.scope.formation checked)
      (boundary.scope.functionsCanonical checked) boundary.accepted binders, typing⟩

theorem forItem_assignBitNot
    {raw : Workspace.RawWorkspace} {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel childFuel : Nat}
    {selected : BodySelection compiled row fuel}
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    (placeSound : PlaceRootedSoundness selected childFuel)
    {inferenceContext : SourceInference.Context} {item : Syntax.ForItem}
    {expression : Syntax.Expr} {operatorSpan : Syntax.SourceSpan}
    {expectedReturn : Ty} {initial final : State} {inferred : ForItemForm}
    {frames : List InitializedLetBinding} {target : SourceSemantics.Context}
    (form : item.value = .assignBitNot expression operatorSpan)
    (boundary : ForItemBoundary selected (childFuel + 1) inferenceContext item expectedReturn
      initial inferred final frames target) :
    ForItemConclusion selected inferenceContext expectedReturn inferred final frames target := by
  exact forItem_assignBitNot_for (provenance := fun _ => True) checked true_childClosed
    (fun _ boundary => placeSound boundary) trivial form boundary

end Solcore.SourceSemantics.SourceCompiledGeneralizedSoundness
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceCompiledGeneralizedForExpression
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledGeneralizedSoundness
open Frontend SourceInference TypeSystem SourceInferenceSoundness
open SourceCompiledLocalFinalization SourceInferenceExecution

theorem forItem_expression_for {callProvenance : CallIndex → Prop}
    {raw : Workspace.RawWorkspace} {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel childFuel : Nat}
    {selected : BodySelection compiled row fuel}
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    (descend : ChildClosed callProvenance)
    (recursive : ExpressionRootedSoundnessFor callProvenance selected childFuel)
    {inferenceContext : SourceInference.Context} {item : Syntax.ForItem} {expression : Syntax.Expr}
    {expectedReturn : Ty} {initial final : State} {inferred : ForItemForm}
    {frames : List InitializedLetBinding} {target : SourceSemantics.Context}
    (here : callProvenance (.forItem (childFuel + 1) inferenceContext item initial inferred final))
    (form : item.value = .expression expression)
    (boundary : ForItemBoundary selected (childFuel + 1) inferenceContext item expectedReturn
      initial inferred final frames target) :
    ForItemConclusion selected inferenceContext expectedReturn inferred final frames target := by
  obtain ⟨value, resultState, child, resultEq⟩ :=
    inferForItemFuel_success_expression_facts form boundary.accepted
  have sameItem : inferred = .expression value.id := congrArg Prod.fst resultEq
  have sameState : final = resultState := congrArg Prod.snd resultEq
  subst inferred
  subst final
  have member : (.expression value.id : NodeId) ∈ (ForItemForm.expression value.id).references := by
    simp [ForItemForm.references]
  have childHere := descend here (.forItem_expression boundary.accepted form child)
  have typed := recursive childHere ({
    accepted := child
    interfaces := boundary.interfaces
    extension := boundary.extension
    scope := boundary.scope
    invariant := RecursiveExpressionInvariant.ofStatement boundary.invariant
    actual := boundary.actual
    operational := boundary.operational
    expectedBelow := by simp
    expectedAdmissible := by simp
    expectedSafe := by simp
    rawSubtree := boundary.rawReferences _ member
    integerPatterns := boundary.integerPatterns
    integerLiterals := boundary.integerLiterals
    requirements := boundary.requirements
    covered := boundary.covered _ member
    actualCovered := boundary.actualCovered _ member
  } : RootedExpressionBoundary selected childFuel inferenceContext expression none
    initial value resultState frames target)
  exact ⟨target, boundary.invariant.inferExprFuel child (boundary.scope.formation checked)
      (boundary.scope.functionsCanonical checked) (by simp) boundary.extension,
    boundary.actual, boundary.operational.ofExpression boundary.invariant.ready
      (boundary.scope.catalog checked) (boundary.scope.formation checked)
      (boundary.scope.functionsCanonical checked) (by simp) (by simp) child,
    ForItemHasType.expression typed⟩

theorem forItem_expression
    {raw : Workspace.RawWorkspace} {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel childFuel : Nat}
    {selected : BodySelection compiled row fuel}
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    (recursive : ExpressionRootedSoundness selected childFuel)
    {inferenceContext : SourceInference.Context} {item : Syntax.ForItem} {expression : Syntax.Expr}
    {expectedReturn : Ty} {initial final : State} {inferred : ForItemForm}
    {frames : List InitializedLetBinding} {target : SourceSemantics.Context}
    (form : item.value = .expression expression)
    (boundary : ForItemBoundary selected (childFuel + 1) inferenceContext item expectedReturn
      initial inferred final frames target) :
    ForItemConclusion selected inferenceContext expectedReturn inferred final frames target := by
  exact forItem_expression_for (callProvenance := fun _ => True) checked true_childClosed
    (fun _ boundary => recursive boundary) True.intro form boundary

end Solcore.SourceSemantics.SourceCompiledGeneralizedSoundness
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceCompiledGeneralizedForValueAssignment
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledGeneralizedSoundness
open Frontend SourceInference TypeSystem SourceInferenceSoundness
open SourceCompiledLocalFinalization SourceInferenceExecution

theorem forItem_assignValue_for
    {raw : Workspace.RawWorkspace} {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel childFuel : Nat}
    {selected : BodySelection compiled row fuel}
    {provenance : CallIndex → Prop}
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    (descend : ChildClosed provenance)
    (placeSound : PlaceRootedSoundnessFor provenance selected childFuel)
    (expressionSound : ExpressionRootedSoundnessFor provenance selected childFuel)
    {inferenceContext : SourceInference.Context} {item : Syntax.ForItem}
    {targetExpression valueExpression : Syntax.Expr} {operator : Syntax.Located Syntax.ValueAssignOp}
    {expectedReturn : Ty} {initial final : State} {inferred : ForItemForm}
    {frames : List InitializedLetBinding} {target : SourceSemantics.Context}
    (here : provenance (.forItem (childFuel + 1) inferenceContext item initial inferred final))
    (form : item.value = .assignValue targetExpression operator valueExpression)
    (boundary : ForItemBoundary selected (childFuel + 1) inferenceContext item expectedReturn
      initial inferred final frames target) :
    ForItemConclusion selected inferenceContext expectedReturn inferred final frames target := by
  obtain ⟨assignment, value, resultState, accepted, resultEq⟩ :=
    inferForItemFuel_success_assignValue_facts form boundary.accepted
  have sameItem : inferred = .assignValue assignment operator.value value.id := congrArg Prod.fst resultEq
  have sameState : final = resultState := congrArg Prod.snd resultEq
  subst inferred
  subst final
  have keyMember : ∀ key, .expression key ∈ assignment.references →
      (.expression key : NodeId) ∈ (ForItemForm.assignValue assignment operator.value value.id).references := by
    intro key member
    exact List.mem_append_left _ member
  have valueMember : (.expression value.id : NodeId) ∈
      (ForItemForm.assignValue assignment operator.value value.id).references := by
    simp [ForItemForm.references]
  obtain ⟨typed, operational⟩ := assignedValue_of_actual_children_for checked descend placeSound expressionSound
    (descend here (ChildStep.forItem_assignment boundary.accepted form accepted)) ({
    accepted
    interfaces := boundary.interfaces
    extension := boundary.extension
    scope := boundary.scope
    invariant := RecursiveExpressionInvariant.ofStatement boundary.invariant
    actual := boundary.actual
    operational := boundary.operational
    rawKeys := fun key member => boundary.rawReferences _ (keyMember key member)
    rawValue := boundary.rawReferences _ valueMember
    integerPatterns := boundary.integerPatterns
    integerLiterals := boundary.integerLiterals
    requirements := boundary.requirements
    keysCovered := fun key member => boundary.covered _ (keyMember key member)
    valueCovered := boundary.covered _ valueMember
    keysActualCovered := fun key member => boundary.actualCovered _ (keyMember key member)
    valueActualCovered := boundary.actualCovered _ valueMember
  } : AssignedValueBoundary selected childFuel inferenceContext targetExpression operator.value valueExpression
    initial assignment value resultState frames target)
  have binders : resultState.localBinders = initial.localBinders :=
    congrArg LexicalScope.binders (Detail.inferAssignedValueFuel_success_lexicalScope_eq accepted)
  have itemTyped : ForItemHasType selected.body.finalized.typedSource
      { returnType := selected.body.finalized.substitution.apply expectedReturn,
        loopDepth := inferenceContext.loopDepth } target
      ((ForItemForm.assignValue assignment operator.value value.id).applySubstitution
        selected.body.finalized.substitution) target := .assignValue typed
  have invariant := boundary.invariant.of_forItem_typing boundary.accepted
    (boundary.scope.formation checked) (boundary.scope.functionsCanonical checked)
    (boundary.invariant.active.inferAssignedValueFuel accepted)
    (activeSchemeQuantifierIsolation_transport boundary.invariant.schemeIsolation binders)
    boundary.extension itemTyped
  exact ⟨target, invariant, boundary.actual, operational, itemTyped⟩

theorem forItem_assignValue
    {raw : Workspace.RawWorkspace} {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel childFuel : Nat}
    {selected : BodySelection compiled row fuel}
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    (placeSound : PlaceRootedSoundness selected childFuel)
    (expressionSound : ExpressionRootedSoundness selected childFuel)
    {inferenceContext : SourceInference.Context} {item : Syntax.ForItem}
    {targetExpression valueExpression : Syntax.Expr} {operator : Syntax.Located Syntax.ValueAssignOp}
    {expectedReturn : Ty} {initial final : State} {inferred : ForItemForm}
    {frames : List InitializedLetBinding} {target : SourceSemantics.Context}
    (form : item.value = .assignValue targetExpression operator valueExpression)
    (boundary : ForItemBoundary selected (childFuel + 1) inferenceContext item expectedReturn
      initial inferred final frames target) :
    ForItemConclusion selected inferenceContext expectedReturn inferred final frames target := by
  exact forItem_assignValue_for (provenance := fun _ => True) checked true_childClosed
    (fun _ boundary => placeSound boundary) (fun _ boundary => expressionSound boundary) trivial form boundary

end Solcore.SourceSemantics.SourceCompiledGeneralizedSoundness
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceCompiledGeneralizedForDispatch
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledGeneralizedSoundness
open Frontend SourceInference TypeSystem SourceInferenceSoundness
open SourceCompiledLocalFinalization SourceInferenceExecution

variable {raw : Workspace.RawWorkspace} {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel childFuel : Nat}
    {selected : BodySelection compiled row fuel}
    {callProvenance : CallIndex → Prop}

theorem forItemRooted_zero_for : ForItemRootedSoundnessFor callProvenance selected 0 := by
  intro inferenceContext item expectedReturn initial final inferred frames target here boundary
  have success := boundary.accepted
  simp only [Detail.inferForItemFuel] at success
  cases success

theorem forItemRooted_step_for
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    (descend : ChildClosed callProvenance)
    (barriers : BodyInitializerBarriersFor callProvenance selected)
    (expressionSound : ExpressionRootedSoundnessFor callProvenance selected childFuel)
    (placeSound : PlaceRootedSoundnessFor callProvenance selected childFuel) :
    ForItemRootedSoundnessFor callProvenance selected (childFuel + 1) := by
  intro inferenceContext item expectedReturn initial final inferred frames target here boundary
  cases form : item.value with
  | letDecl name annotation initializer =>
    cases annotation with
    | some sourceType =>
      cases initializer with
      | none => exact forItem_annotatedUninitialized checked form boundary
      | some source => exact forItem_annotatedInitialized_for checked descend expressionSound here form boundary
    | none =>
      cases initializer with
      | none =>
        have success := boundary.accepted
        simp [Detail.inferForItemFuel, form, bind, Except.bind, throw] at success
      | some source =>
        obtain ⟨receipt⟩ := LocalHeaderRequirementTiming.of_accepted form boundary.accepted
        exact forItem_initialized_of_receipt_for checked descend expressionSound here boundary receipt
          (barriers.header here boundary receipt)
  | expression source => exact forItem_expression_for checked descend expressionSound here form boundary
  | assignValue target operator value =>
    exact forItem_assignValue_for checked descend placeSound expressionSound here form boundary
  | assignBitNot target span => exact forItem_assignBitNot_for checked descend placeSound here form boundary

theorem forItemRooted_zero : ForItemRootedSoundness selected 0 :=
  forItemRootedSoundness_of_true (forItemRooted_zero_for (selected := selected) (callProvenance := fun _ => True))

theorem forItemRooted_step
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    (barriers : BodyInitializerBarriers selected)
    (expressionSound : ExpressionRootedSoundness selected childFuel)
    (placeSound : PlaceRootedSoundness selected childFuel) :
    ForItemRootedSoundness selected (childFuel + 1) := by
  apply forItemRootedSoundness_of_true
  exact forItemRooted_step_for checked true_childClosed barriers.with_true
    (fun _ boundary => expressionSound boundary) (placeRootedSoundnessFor_true placeSound)

end Solcore.SourceSemantics.SourceCompiledGeneralizedSoundness
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceCompiledGeneralizedForSequence
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledGeneralizedSoundness
open Frontend SourceInference TypeSystem SourceInferenceSoundness
open SourceCompiledLocalFinalization SourceInferenceStatementsSoundness SourceInferenceExecution

variable {raw : Workspace.RawWorkspace} {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel childFuel : Nat}
    {selected : BodySelection compiled row fuel}

theorem forItemsRooted_of_item_for {callProvenance : CallIndex → Prop}
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    (descend : ChildClosed callProvenance)
    (itemSound : ForItemRootedSoundnessFor callProvenance selected childFuel) :
    ForItemsRootedSoundnessFor callProvenance selected childFuel := by
  intro inferenceContext items expectedReturn initial result frames target here boundary
  induction items generalizing initial result target with
  | nil =>
      have success := boundary.accepted
      simp only [Detail.inferForItemsFuel, pure, Pure.pure, Except.pure] at success
      cases Except.ok.inj success
      exact ⟨target, boundary.invariant, boundary.actual, boundary.operational, .nil _ _⟩
  | cons item rest induction =>
      have success := boundary.accepted
      unfold Detail.inferForItemsFuel at success
      cases itemSuccess : Detail.inferForItemFuel childFuel inferenceContext item initial with
      | error error => simp [itemSuccess, bind, Except.bind] at success
      | ok pair =>
          obtain ⟨inferredItem, itemState⟩ := pair
          simp only [itemSuccess, bind, Except.bind] at success
          cases tailSuccess : Detail.inferForItemsFuel childFuel inferenceContext rest itemState with
          | error error => simp [tailSuccess] at success
          | ok tail =>
              simp only [tailSuccess, pure, Pure.pure, Except.pure] at success
              cases Except.ok.inj success
              have itemProperties := Detail.inferForItemFuel_inferenceProperties boundary.invariant.ready
                (boundary.scope.formation checked) (boundary.scope.functionsCanonical checked) itemSuccess
              have tailProperties := Detail.inferForItemsFuel_inferenceProperties itemProperties.2
                (boundary.scope.formation checked) (boundary.scope.functionsCanonical checked) tailSuccess
              have itemBelow := (Detail.inferForItemFuel_occurrenceBoundExtends itemSuccess
                ).nodesBelowNextOccurrence boundary.invariant.nodesBelow
              have itemToTail := inferForItemsFuel_success_typingSourceExtends tailSuccess itemBelow (bodyRoots selected)
              obtain ⟨middle, middleInvariant, middleActual, middleOperational, itemTyped⟩ :=
                itemSound (descend here (.forItems_head boundary.accepted itemSuccess)) ({
                  accepted := itemSuccess
                  interfaces := boundary.interfaces
                  extension := boundary.extension.trans tailProperties.1.substitution_extends
                  scope := boundary.scope
                  invariant := boundary.invariant
                  actual := boundary.actual
                  operational := boundary.operational
                  rawReferences := fun reference member =>
                    (boundary.rawReferences inferredItem (by simp) reference member).monoBefore itemToTail
                  integerPatterns := (Detail.inferForItemsFuel_integerPatterns_subset tailSuccess).trans boundary.integerPatterns
                  integerLiterals := (Detail.inferForItemsFuel_integerLiterals_subset tailSuccess).trans boundary.integerLiterals
                  requirements := (Detail.inferForItemsFuel_requirements_subset tailSuccess).trans boundary.requirements
                  owner := boundary.owner
                  covered := boundary.covered inferredItem (by simp)
                  bindingsRetained := by
                    intro binding member
                    apply boundary.bindingsRetained
                    simp only [List.flatMap_cons, List.mem_append]
                    exact .inl member
                  actualCovered := boundary.actualCovered inferredItem (by simp)
                  actualBindings := boundary.actualBindings inferredItem (by simp)
                } : ForItemBoundary selected childFuel inferenceContext item expectedReturn
                  initial inferredItem itemState frames target)
              obtain ⟨finalContext, invariant, actual, operational, tailTyped⟩ :=
                induction (descend here (.forItems_tail boundary.accepted itemSuccess tailSuccess)) ({
                  accepted := tailSuccess
                  interfaces := boundary.interfaces
                  extension := boundary.extension
                  scope := boundary.scope
                  invariant := middleInvariant
                  actual := middleActual
                  operational := middleOperational
                  rawReferences := fun next member => boundary.rawReferences next (by simp [member])
                  integerPatterns := boundary.integerPatterns
                  integerLiterals := boundary.integerLiterals
                  requirements := boundary.requirements
                  owner := boundary.owner.trans (Detail.inferForItemFuel_preserves_owner itemSuccess).symm
                  covered := fun next member => (boundary.covered next (by simp [member])).transportAssumptions
                    (forItemHasType_assumptions_eq itemTyped)
                  bindingsRetained := by
                    intro binding member
                    apply boundary.bindingsRetained
                    simp only [List.flatMap_cons, List.mem_append]
                    exact .inr member
                  actualCovered := fun next member => boundary.actualCovered next (by simp [member])
                  actualBindings := fun next member => boundary.actualBindings next (by simp [member])
                } : ForItemsBoundary selected childFuel inferenceContext rest expectedReturn itemState tail frames middle)
              exact ⟨finalContext, invariant, actual, operational, .cons itemTyped tailTyped⟩

theorem forItemsRooted_of_item
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    (itemSound : ForItemRootedSoundness selected childFuel) :
    ForItemsRootedSoundness selected childFuel := by
  exact forItemsRooted_of_item_for (callProvenance := fun _ => True) checked true_childClosed
    (fun _ boundary => itemSound boundary) True.intro

end Solcore.SourceSemantics.SourceCompiledGeneralizedSoundness
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceCompiledGeneralizedForStatement
/-! The complete for-loop consumer follows the actual initializer, condition,
body and post calls. The initializer's return-type privacy is kept explicit
until its producer for newly generalized declarations is assembled. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledGeneralizedSoundness
open Frontend SourceInference TypeSystem SourceInferenceSoundness
open SourceCompiledLocalFinalization SourceInferenceStatementsSoundness SourceInferenceExecution

theorem statement_for_of_initializer_privacy_for {callProvenance : CallIndex → Prop}
    {raw : Workspace.RawWorkspace} {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel childFuel : Nat}
    {selected : BodySelection compiled row fuel}
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    (descend : ChildClosed callProvenance)
    (recursiveItems : ForItemsRootedSoundnessFor callProvenance selected childFuel)
    (recursiveExpression : ExpressionRootedSoundnessFor callProvenance selected childFuel)
    {inferenceContext : SourceInference.Context} {statement : Syntax.Statement}
    {headerSpan : Syntax.SourceSpan} {initializer post : List Syntax.ForItem}
    {condition : Syntax.Expr} {body : Syntax.Block} {expectedReturn : Ty}
    {initial : State} {result : Detail.StatementResult}
    {frames : List InitializedLetBinding} {target : SourceSemantics.Context}
    (here : callProvenance (.statement (childFuel + 1) inferenceContext statement expectedReturn initial result))
    (form : statement.value = .forLoop headerSpan initializer condition post body)
    (boundary : StatementBoundary selected (childFuel + 1) inferenceContext statement
      expectedReturn initial result frames target)
    (returnSafe : ∀ binder ∈ initial.localBinders,
      ProtectedVariables.Safe binder.scheme.quantified initial expectedReturn)
    (returnAdmissible : TypeAdmissible target (selected.body.finalized.substitution.apply expectedReturn))
    (initializerPrivacy : ∀ {actualInitializer : Detail.InferredForItems},
      Detail.inferForItemsFuel childFuel inferenceContext initializer initial.allocateStatementId.2 = .ok actualInitializer →
      ∀ binder ∈ actualInitializer.state.localBinders,
        ProtectedVariables.Safe binder.scheme.quantified actualInitializer.state expectedReturn)
    (recursiveBody : ∀ {bodyInitial : State} {bodyResult : Detail.BlockResult}
      {loopContext : SourceSemantics.Context},
      callProvenance (.statements childFuel {inferenceContext with loopDepth := inferenceContext.loopDepth + 1}
        body.value expectedReturn bodyInitial bodyResult) →
      (∀ binder ∈ bodyInitial.localBinders,
        ProtectedVariables.Safe binder.scheme.quantified bodyInitial expectedReturn) →
      TypeAdmissible loopContext (selected.body.finalized.substitution.apply expectedReturn) →
      StatementsBoundary selected childFuel {inferenceContext with loopDepth := inferenceContext.loopDepth + 1} body.value expectedReturn
        bodyInitial bodyResult frames loopContext →
      StatementsConclusion selected {inferenceContext with loopDepth := inferenceContext.loopDepth + 1} expectedReturn bodyResult frames loopContext) :
    StatementConclusion selected inferenceContext expectedReturn result frames target := by
  have resources := selected.body.resources
  have formation := boundary.scope.formation checked
  have canonical := boundary.scope.functionsCanonical checked
  have catalog := boundary.scope.catalog checked
  have allocatedInvariant := boundary.invariant.allocateStatementId rfl
  have allocatedOperational := boundary.operational.allocateStatementId
  have resultExtension := boundary.rawSubtree.finalized resources
  obtain ⟨initializerResult, inferredCondition, conditionState, bodyResult,
    postResult, initializerSuccess, conditionSuccess, bodySuccess,
    postSuccess, resultEq, containsRaw⟩ :=
    inferStatementFuel_success_forLoop_facts form rfl boundary.accepted
      (bodyRoots selected)
  obtain ⟨progressInitializer, progressCondition, progressConditionState,
    progressBody, progressPost, progressInitializerSuccess,
    progressConditionSuccess, progressBodySuccess, progressPostSuccess,
    initializerSubstitutionExtension, conditionSubstitutionExtension,
    bodySubstitutionExtension, postSubstitutionExtension,
    initializerLiteralsParent, conditionLiteralsParent,
    bodyLiteralsParent, postLiteralsParent⟩ :=
    inferStatementFuel_success_forLoop_child_progress form
      rfl boundary.accepted formation canonical
      boundary.invariant boundary.extension
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
    inferStatementFuel_success_forLoop_child_provenance form
      rfl boundary.accepted boundary.invariant.nodesBelow (bodyRoots selected)
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
  have containsFinal := resultExtension.containsStatement containsRaw
  have headerCovered := forItemsReferencesCovered_of_rootedForLoop
    containsRaw rfl resultExtension resources.graph_closed boundary.covered
  have headerBindings := forItemsBindingsRetained_of_containedForLoop
    (boundary.rawSubtree.containsStatement containsRaw) ⟨rfl, ⟨[], by simp⟩⟩
  have headerActualBindings := actualForItemsBindings_of_rootedForLoop
    containsRaw resultExtension boundary.actualCovered
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
  have initializerOwner : selected.body.finalized.typedSource.owner = initial.allocateStatementId.2.owner := by
    have retained := resultExtension.owner_eq
    have parentOwner := Detail.inferStatementFuel_preserves_owner boundary.accepted
    have allocatedOwner := congrArg (fun header : State.Header => header.owner)
      (State.allocateStatementId_header initial)
    exact retained.trans (parentOwner.trans allocatedOwner.symm)
  obtain ⟨loopContext, initializerInvariant, initializerActual, initializerOperational, initializerTyping⟩ :=
    recursiveItems (descend here (.statement_for_initializer boundary.accepted form rfl initializerSuccess)) ({
      accepted := initializerSuccess
      interfaces := boundary.interfaces
      extension := initializerSubstitutionExtension
      scope := boundary.scope
      invariant := allocatedInvariant
      actual := boundary.actual
      operational := allocatedOperational
      rawReferences := fun item member reference present =>
        (boundary.rawSubtree.child (directChild_statement_reference containsRaw
          (initializerReference item member reference present))).monoBefore initializerProvenance.sourceExtension
      integerPatterns := List.Subset.trans initializerProvenance.integerPatternsSubset boundary.integerPatterns
      integerLiterals := List.Subset.trans initializerLiteralsParent boundary.integerLiterals
      requirements := List.Subset.trans initializerProvenance.requirementsSubset boundary.requirements
      owner := initializerOwner
      covered := headerCovered.1
      bindingsRetained := headerBindings.1
      actualCovered := fun item member reference present =>
        boundary.actualCovered.preserved_statement_reference containsRaw resultExtension
          (initializerReference item member reference present)
      actualBindings := headerActualBindings.1 } :
      ForItemsBoundary selected childFuel inferenceContext initializer expectedReturn
        initial.allocateStatementId.2 initializerResult frames target)
  have loopAssumptions : loopContext.assumptions = target.assumptions :=
    forItemsHaveType_assumptions_eq initializerTyping
  have conditionExpected : ∀ type ∈ some Ty.bool,
      type.VariablesBelow initializerResult.state.inference.next := by
    intro type member
    cases member
    exact Ty.variablesBelow_constructor _ _
  have conditionSafe : ∀ binder ∈ initializerResult.state.localBinders, ∀ type ∈ some Ty.bool,
      ProtectedVariables.Safe binder.scheme.quantified initializerResult.state type := by
    intro binder _ type member
    cases member
    exact ProtectedVariables.safe_closed _ _ (Ty.variablesBelow_constructor _ _)
  have conditionProperties := Detail.inferExprFuel_inferenceProperties initializerInvariant.ready
    formation canonical conditionExpected conditionSuccess
  have conditionInvariant := initializerInvariant.inferExprFuel conditionSuccess formation canonical
    conditionExpected conditionSubstitutionExtension
  have conditionOperational := initializerOperational.ofExpression initializerInvariant.ready
    catalog formation canonical conditionExpected conditionSafe conditionSuccess
  have conditionSource := (inferStatementsFuel_success_typingSourceExtends bodySuccess
    conditionInvariant.nodesBelow (bodyRoots selected)).trans bodyProvenance.sourceExtension
  have conditionCovered : TemplateScopeCovered selected.body.finalized.typedSource
      loopContext (.expression inferredCondition.id) := by
    apply TemplateScopeCovered.forLoopCondition boundary.covered resources.graph_closed
    · simpa [StatementNode.applySubstitution, StatementForm.applySubstitution] using containsFinal
    · exact loopAssumptions
  have conditionTyping := recursiveExpression
    (descend here (.statement_for_condition boundary.accepted form rfl initializerSuccess conditionSuccess)) ({
    accepted := conditionSuccess
    interfaces := boundary.interfaces
    extension := conditionSubstitutionExtension
    scope := boundary.scope
    invariant := RecursiveExpressionInvariant.ofStatement initializerInvariant
    actual := initializerActual
    operational := initializerOperational
    expectedBelow := conditionExpected
    expectedAdmissible := by
      intro type member
      cases member
      exact TypeAdmissible.bool ((RecursiveExpressionInvariant.ofStatement initializerInvariant).typeParameterBinders
        (by simpa [boundary.scope.owner, boundary.scope.parameters] using boundary.scope.canonical checked))
    expectedSafe := conditionSafe
    rawSubtree := (boundary.rawSubtree.child (directChild_statement_reference containsRaw
      (by simp [StatementForm.references]))).monoBefore conditionSource
    integerPatterns := List.Subset.trans (Detail.inferStatementsFuel_integerPatterns_subset bodySuccess)
      (List.Subset.trans bodyProvenance.integerPatternsSubset boundary.integerPatterns)
    integerLiterals := List.Subset.trans (Detail.inferStatementsFuel_integerLiterals_subset bodySuccess)
      (List.Subset.trans bodyLiteralsParent boundary.integerLiterals)
    requirements := List.Subset.trans (Detail.inferStatementsFuel_requirements_subset bodySuccess)
      (List.Subset.trans bodyProvenance.requirementsSubset boundary.requirements)
    covered := conditionCovered
    actualCovered := boundary.actualCovered.preserved_statement_reference containsRaw resultExtension
      (by simp [StatementForm.references]) } :
    RootedExpressionBoundary selected childFuel inferenceContext condition (some .bool)
      initializerResult.state inferredCondition conditionState frames loopContext)
  have conditionBool : ExpressionHasType selected.body.finalized.typedSource
      loopContext inferredCondition.id .bool := by
    have same : selected.body.finalized.substitution.apply inferredCondition.type = .bool := by
      simpa using Detail.inferExprFuel_expected_type_apply_eq conditionSuccess conditionSubstitutionExtension
    simpa [same] using conditionTyping
  have loopReturn : TypeAdmissible loopContext (selected.body.finalized.substitution.apply expectedReturn) :=
    StructuralSubstitution.TypeAdmissible.transportContext
      (initializerInvariant.signaturesEq.trans boundary.invariant.signaturesEq.symm)
      (initializerInvariant.typeParametersEq.trans boundary.invariant.typeParametersEq.symm)
      (initializerInvariant.declarationEq.trans boundary.invariant.declarationEq.symm)
      (initializerActual.variables_eq.trans boundary.actual.variables_eq.symm)
      (initializerInvariant.residual.trans boundary.invariant.residual.symm) returnAdmissible
  have conditionBinders := congrArg LexicalScope.binders
    (Detail.inferExprFuel_success_lexicalScope_eq conditionSuccess)
  change conditionState.localBinders = initializerResult.state.localBinders at conditionBinders
  have bodyReturnSafe : ∀ binder ∈ conditionState.localBinders,
      ProtectedVariables.Safe binder.scheme.quantified conditionState expectedReturn := by
    intro binder member
    have old : binder ∈ initializerResult.state.localBinders := conditionBinders ▸ member
    have privacy := ProtectedVariables.inferExprFuel_private binder.scheme.quantified childFuel
      inferenceContext condition (some .bool) initializerResult.state initializerInvariant.ready
      initializerOperational.requirements (initializerOperational.quantifiersBelow binder old)
      (initializerOperational.privacy binder old) catalog formation canonical conditionExpected
      (conditionSafe binder old) _ conditionSuccess
    exact privacy.1 expectedReturn (initializerPrivacy initializerSuccess binder old)
  have bodyCovered : ∀ child ∈ bodyResult.statements,
      TemplateScopeCovered selected.body.finalized.typedSource loopContext (.statement child) := by
    intro child member
    apply rooted_statement_child_covered containsRaw
      (by simp [StatementForm.references, member]) resultExtension boundary.covered resources.graph_closed
    intro predicate present
    simpa [loopAssumptions] using present
  obtain ⟨bodyFinal, bodyFacts, _, _, bodyOperational, bodyTyping, bodyAgreement⟩ :=
    recursiveBody (descend here (.statement_for_body boundary.accepted form rfl initializerSuccess conditionSuccess bodySuccess))
      bodyReturnSafe loopReturn ({
      accepted := bodySuccess
      interfaces := boundary.interfaces
      extension := bodySubstitutionExtension
      scope := boundary.scope.withLoopDepth (inferenceContext.loopDepth + 1)
      invariant := conditionInvariant
      actual := initializerActual
      operational := conditionOperational
      rawSubtrees := fun child member => (boundary.rawSubtree.child
        (directChild_statement_reference containsRaw (by simp [StatementForm.references, member]))).monoBefore
          bodyProvenance.sourceExtension
      integerPatterns := List.Subset.trans bodyProvenance.integerPatternsSubset boundary.integerPatterns
      integerLiterals := List.Subset.trans bodyLiteralsParent boundary.integerLiterals
      requirements := List.Subset.trans bodyProvenance.requirementsSubset boundary.requirements
      covered := bodyCovered
      actualCovered := fun child member => boundary.actualCovered.preserved_statement_reference
        containsRaw resultExtension (by simp [StatementForm.references, member]) } :
      StatementsBoundary selected childFuel {inferenceContext with loopDepth := inferenceContext.loopDepth + 1}
        body.value expectedReturn conditionState bodyResult frames loopContext)
  have bodyProperties := Detail.inferStatementsFuel_inferenceProperties
    (context := {inferenceContext with loopDepth := inferenceContext.loopDepth + 1})
    conditionProperties.2.1 formation canonical conditionInvariant.returnBelow bodySuccess
  have bodyBelow := (Detail.inferStatementsFuel_occurrenceBoundExtends bodySuccess).nodesBelowNextOccurrence
    bodyProvenance.initialBelow
  have nextLocalLe := Nat.le_trans (Detail.inferExprFuel_nextLocal_le conditionSuccess)
    (Detail.inferStatementsFuel_nextLocal_le bodySuccess)
  have postInvariant := initializerInvariant.restoreLexicalScope
    (conditionProperties.1.trans bodyProperties.1) bodyBelow nextLocalLe bodySubstitutionExtension
  have savedBinders : initializerResult.state.localBinders ⊆ bodyResult.state.localBinders := by
    rw [← conditionBinders]
    exact ProtectedVariables.inferStatementsFuel_binders_subset bodySuccess
  have postOperational := bodyOperational.restoreSaved initializerOperational.origins savedBinders
  have postOwner : selected.body.finalized.typedSource.owner =
      (bodyResult.state.restoreLexicalScope initializerResult.state.lexicalScope).owner := by
    have ownerToPost := postProvenance.sourceExtension.owner_eq
    have postOwner := Detail.inferForItemsFuel_preserves_owner postSuccess
    have retained := resultExtension.owner_eq
    simpa [State.toTypedSource] using retained.trans (ownerToPost.trans postOwner)
  obtain ⟨postContext, _, _, _, postTyping⟩ :=
    recursiveItems (descend here (.statement_for_post boundary.accepted form rfl initializerSuccess conditionSuccess bodySuccess postSuccess)) ({
      accepted := postSuccess
      interfaces := boundary.interfaces
      extension := postSubstitutionExtension
      scope := boundary.scope.withLoopDepth (inferenceContext.loopDepth + 1)
      invariant := postInvariant
      actual := initializerActual
      operational := postOperational
      rawReferences := fun item member reference present => (boundary.rawSubtree.child
        (directChild_statement_reference containsRaw (postReference item member reference present))).monoBefore
          postProvenance.sourceExtension
      integerPatterns := List.Subset.trans postProvenance.integerPatternsSubset boundary.integerPatterns
      integerLiterals := List.Subset.trans postLiteralsParent boundary.integerLiterals
      requirements := List.Subset.trans postProvenance.requirementsSubset boundary.requirements
      owner := postOwner
      covered := fun item member => (headerCovered.2 item member).transportAssumptions loopAssumptions
      bindingsRetained := headerBindings.2
      actualCovered := fun item member reference present =>
        boundary.actualCovered.preserved_statement_reference containsRaw resultExtension
          (postReference item member reference present)
      actualBindings := headerActualBindings.2 } :
      ForItemsBoundary selected childFuel {inferenceContext with loopDepth := inferenceContext.loopDepth + 1}
        post expectedReturn (bodyResult.state.restoreLexicalScope initializerResult.state.lexicalScope)
        postResult frames loopContext)
  let facts : StatementFacts := {
    type := .unit, hasValue := false, sawReturn := false,
    control := .loop bodyFacts.control }
  have typing : StatementHasType selected.body.finalized.typedSource
      {returnType := selected.body.finalized.substitution.apply expectedReturn, loopDepth := inferenceContext.loopDepth}
      target result.id target facts :=
    .forLoop containsFinal rfl initializerTyping conditionBool bodyTyping postTyping
      (by simp [StatementNode.applySubstitution, resultEq])
  have agreement : StatementResultMatchesFactsAfterSubstitution
      selected.body.finalized.substitution result facts := by
    rw [resultEq]
    exact StatementResultMatchesFactsAfterSubstitution.forLoop _ bodyFacts _ _
  have bindersEq : result.state.localBinders = initial.localBinders := by
    simp [resultEq, State.restoreLexicalScope, State.recordNode, State.lexicalScope]
  have active : ActiveLocalContextInvariant result.state selected.body.finalized.substitution target := by
    rw [resultEq]
    exact allocatedInvariant.active.restoreLexicalScope_recordNode _
  have finalInvariant := boundary.invariant.of_retained_statement_typing boundary.accepted formation canonical active
    (inferStatementFuel_preserves_localBindersBelowNextLocal boundary.invariant.bindersBelow boundary.accepted)
    boundary.extension (activeSchemeQuantifierIsolation_transport boundary.invariant.schemeIsolation bindersEq) typing
  have finalOperational := boundary.operational.ofStatementPreservingBinders boundary.invariant.ready
    catalog formation canonical boundary.invariant.returnBelow returnSafe boundary.accepted bindersEq
  exact ⟨target, facts, finalInvariant, boundary.actual, finalOperational, typing, agreement⟩

theorem statement_for_of_initializer_privacy
    {raw : Workspace.RawWorkspace} {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel childFuel : Nat}
    {selected : BodySelection compiled row fuel}
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    (recursiveItems : ForItemsRootedSoundness selected childFuel)
    (recursiveExpression : ExpressionRootedSoundness selected childFuel)
    {inferenceContext : SourceInference.Context} {statement : Syntax.Statement}
    {headerSpan : Syntax.SourceSpan} {initializer post : List Syntax.ForItem}
    {condition : Syntax.Expr} {body : Syntax.Block} {expectedReturn : Ty}
    {initial : State} {result : Detail.StatementResult}
    {frames : List InitializedLetBinding} {target : SourceSemantics.Context}
    (form : statement.value = .forLoop headerSpan initializer condition post body)
    (boundary : StatementBoundary selected (childFuel + 1) inferenceContext statement
      expectedReturn initial result frames target)
    (returnSafe : ∀ binder ∈ initial.localBinders,
      ProtectedVariables.Safe binder.scheme.quantified initial expectedReturn)
    (returnAdmissible : TypeAdmissible target (selected.body.finalized.substitution.apply expectedReturn))
    (initializerPrivacy : ∀ {actualInitializer : Detail.InferredForItems},
      Detail.inferForItemsFuel childFuel inferenceContext initializer initial.allocateStatementId.2 = .ok actualInitializer →
      ∀ binder ∈ actualInitializer.state.localBinders,
        ProtectedVariables.Safe binder.scheme.quantified actualInitializer.state expectedReturn)
    (recursiveBody : ∀ {bodyInitial : State} {bodyResult : Detail.BlockResult}
      {loopContext : SourceSemantics.Context},
      (∀ binder ∈ bodyInitial.localBinders,
        ProtectedVariables.Safe binder.scheme.quantified bodyInitial expectedReturn) →
      TypeAdmissible loopContext (selected.body.finalized.substitution.apply expectedReturn) →
      StatementsBoundary selected childFuel {inferenceContext with loopDepth := inferenceContext.loopDepth + 1} body.value expectedReturn
        bodyInitial bodyResult frames loopContext →
      StatementsConclusion selected {inferenceContext with loopDepth := inferenceContext.loopDepth + 1} expectedReturn bodyResult frames loopContext) :
    StatementConclusion selected inferenceContext expectedReturn result frames target := by
  exact statement_for_of_initializer_privacy_for (callProvenance := fun _ => True) checked true_childClosed
    (fun _ boundary => recursiveItems boundary) (fun _ boundary => recursiveExpression boundary)
    True.intro form boundary returnSafe returnAdmissible initializerPrivacy
    (fun _ safe admissible boundary => recursiveBody safe admissible boundary)

end Solcore.SourceSemantics.SourceCompiledGeneralizedSoundness
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceCompiledGeneralizedForReturnConnection
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledGeneralizedSoundness
open Frontend SourceInference TypeSystem SourceInferenceSoundness
open SourceCompiledLocalFinalization SourceInferenceStatementsSoundness SourceInferenceExecution

/-- The actual ordered initializer supplies return-type privacy for the loop body. -/
theorem statement_for_for {callProvenance : CallIndex → Prop}
    {raw : Workspace.RawWorkspace} {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel childFuel : Nat}
    {selected : BodySelection compiled row fuel}
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    (descend : ChildClosed callProvenance)
    (recursiveItems : ForItemsRootedSoundnessFor callProvenance selected childFuel)
    (recursiveExpression : ExpressionRootedSoundnessFor callProvenance selected childFuel)
    {inferenceContext : SourceInference.Context} {statement : Syntax.Statement}
    {headerSpan : Syntax.SourceSpan} {initializer post : List Syntax.ForItem}
    {condition : Syntax.Expr} {body : Syntax.Block} {expectedReturn : Ty}
    {initial : State} {result : Detail.StatementResult}
    {frames : List InitializedLetBinding} {target : SourceSemantics.Context}
    (here : callProvenance (.statement (childFuel + 1) inferenceContext statement expectedReturn initial result))
    (form : statement.value = .forLoop headerSpan initializer condition post body)
    (boundary : StatementBoundary selected (childFuel + 1) inferenceContext statement
      expectedReturn initial result frames target)
    (returnSafe : ∀ binder ∈ initial.localBinders,
      ProtectedVariables.Safe binder.scheme.quantified initial expectedReturn)
    (returnAdmissible : TypeAdmissible target (selected.body.finalized.substitution.apply expectedReturn))
    (recursiveBody : ∀ {bodyInitial : State} {bodyResult : Detail.BlockResult}
      {loopContext : SourceSemantics.Context},
      callProvenance (.statements childFuel {inferenceContext with loopDepth := inferenceContext.loopDepth + 1}
        body.value expectedReturn bodyInitial bodyResult) →
      (∀ binder ∈ bodyInitial.localBinders,
        ProtectedVariables.Safe binder.scheme.quantified bodyInitial expectedReturn) →
      TypeAdmissible loopContext (selected.body.finalized.substitution.apply expectedReturn) →
      StatementsBoundary selected childFuel {inferenceContext with loopDepth := inferenceContext.loopDepth + 1} body.value expectedReturn
        bodyInitial bodyResult frames loopContext →
      StatementsConclusion selected {inferenceContext with loopDepth := inferenceContext.loopDepth + 1} expectedReturn bodyResult frames loopContext) :
    StatementConclusion selected inferenceContext expectedReturn result frames target := by
  apply statement_for_of_initializer_privacy_for checked descend recursiveItems recursiveExpression here form boundary
    returnSafe returnAdmissible ?_ recursiveBody
  intro actualInitializer actualRun
  obtain ⟨initializerResult, inferredCondition, conditionState, bodyResult,
    postResult, initializerSuccess, conditionSuccess, bodySuccess,
    postSuccess, resultEq, containsRaw⟩ :=
    inferStatementFuel_success_forLoop_facts form rfl boundary.accepted (bodyRoots selected)
  change Detail.inferForItemsFuel childFuel inferenceContext initializer initial.allocateStatementId.2 = .ok initializerResult at initializerSuccess
  rw [actualRun] at initializerSuccess
  have same := (Except.ok.inj initializerSuccess).symm
  subst initializerResult
  obtain ⟨progressInitializer, progressCondition, progressConditionState,
    progressBody, progressPost, progressInitializerSuccess,
    progressConditionSuccess, progressBodySuccess, progressPostSuccess,
    initializerExtension, conditionExtension, bodyExtension, postExtension,
    initializerLiterals, conditionLiterals, bodyLiterals, postLiterals⟩ :=
    inferStatementFuel_success_forLoop_child_progress form rfl boundary.accepted
      (boundary.scope.formation checked) (boundary.scope.functionsCanonical checked)
      boundary.invariant boundary.extension
  change Detail.inferForItemsFuel childFuel inferenceContext initializer initial.allocateStatementId.2 = .ok progressInitializer at progressInitializerSuccess
  rw [actualRun] at progressInitializerSuccess
  have same := (Except.ok.inj progressInitializerSuccess).symm
  subst progressInitializer
  have retained : actualInitializer.items.flatMap ForItemForm.initializedLetBinders ⊆
      (evidenceSource selected).initializedLetBinders := by
    intro binder member
    apply (boundary.rawSubtree.containsStatement containsRaw).initializedLetBinder_mem
    exact List.mem_append_left _ member
  exact boundary.operational.allocateStatementId.forItems_return_safe selected.body.resources
    boundary.invariant.ready.allocateStatementId (boundary.scope.catalog checked)
    (boundary.scope.formation checked) (boundary.scope.functionsCanonical checked)
    retained initializerExtension boundary.invariant.returnBelow returnSafe actualRun

theorem statement_for
    {raw : Workspace.RawWorkspace} {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel childFuel : Nat}
    {selected : BodySelection compiled row fuel}
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    (recursiveItems : ForItemsRootedSoundness selected childFuel)
    (recursiveExpression : ExpressionRootedSoundness selected childFuel)
    {inferenceContext : SourceInference.Context} {statement : Syntax.Statement}
    {headerSpan : Syntax.SourceSpan} {initializer post : List Syntax.ForItem}
    {condition : Syntax.Expr} {body : Syntax.Block} {expectedReturn : Ty}
    {initial : State} {result : Detail.StatementResult}
    {frames : List InitializedLetBinding} {target : SourceSemantics.Context}
    (form : statement.value = .forLoop headerSpan initializer condition post body)
    (boundary : StatementBoundary selected (childFuel + 1) inferenceContext statement
      expectedReturn initial result frames target)
    (returnSafe : ∀ binder ∈ initial.localBinders,
      ProtectedVariables.Safe binder.scheme.quantified initial expectedReturn)
    (returnAdmissible : TypeAdmissible target (selected.body.finalized.substitution.apply expectedReturn))
    (recursiveBody : ∀ {bodyInitial : State} {bodyResult : Detail.BlockResult}
      {loopContext : SourceSemantics.Context},
      (∀ binder ∈ bodyInitial.localBinders,
        ProtectedVariables.Safe binder.scheme.quantified bodyInitial expectedReturn) →
      TypeAdmissible loopContext (selected.body.finalized.substitution.apply expectedReturn) →
      StatementsBoundary selected childFuel {inferenceContext with loopDepth := inferenceContext.loopDepth + 1} body.value expectedReturn
        bodyInitial bodyResult frames loopContext →
      StatementsConclusion selected {inferenceContext with loopDepth := inferenceContext.loopDepth + 1} expectedReturn bodyResult frames loopContext) :
    StatementConclusion selected inferenceContext expectedReturn result frames target := by
  exact statement_for_for (callProvenance := fun _ => True) checked true_childClosed
    (fun _ boundary => recursiveItems boundary) (fun _ boundary => recursiveExpression boundary)
    True.intro form boundary returnSafe returnAdmissible
    (fun _ safe admissible boundary => recursiveBody safe admissible boundary)

end Solcore.SourceSemantics.SourceCompiledGeneralizedSoundness
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceCompiledGeneralizedWhileStatement
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledGeneralizedSoundness
open Frontend SourceInference TypeSystem SourceInferenceSoundness
open SourceCompiledLocalFinalization SourceInferenceStatementsSoundness SourceInferenceExecution

theorem statement_while_for {callProvenance : CallIndex → Prop}
    {raw : Workspace.RawWorkspace} {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel childFuel : Nat}
    {selected : BodySelection compiled row fuel}
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    (descend : ChildClosed callProvenance)
    (recursiveExpression : ExpressionRootedSoundnessFor callProvenance selected childFuel)
    {inferenceContext : SourceInference.Context} {statement : Syntax.Statement}
    {condition : Syntax.Expr} {body : Syntax.Block} {expectedReturn : Ty}
    {initial : State} {result : Detail.StatementResult}
    {frames : List InitializedLetBinding} {target : SourceSemantics.Context}
    (here : callProvenance (.statement (childFuel + 1) inferenceContext statement expectedReturn initial result))
    (form : statement.value = .whileLoop condition body)
    (boundary : StatementBoundary selected (childFuel + 1) inferenceContext statement
      expectedReturn initial result frames target)
    (returnSafe : ∀ binder ∈ initial.localBinders,
      ProtectedVariables.Safe binder.scheme.quantified initial expectedReturn)
    (returnAdmissible : TypeAdmissible target (selected.body.finalized.substitution.apply expectedReturn))
    (recursiveBody : ∀ {bodyInitial : State} {bodyResult : Detail.BlockResult},
      callProvenance (.statements childFuel {inferenceContext with loopDepth := inferenceContext.loopDepth + 1} body.value expectedReturn bodyInitial bodyResult) →
      (∀ binder ∈ bodyInitial.localBinders,
        ProtectedVariables.Safe binder.scheme.quantified bodyInitial expectedReturn) →
      TypeAdmissible target (selected.body.finalized.substitution.apply expectedReturn) →
      StatementsBoundary selected childFuel {inferenceContext with loopDepth := inferenceContext.loopDepth + 1} body.value expectedReturn
        bodyInitial bodyResult frames target →
      StatementsConclusion selected {inferenceContext with loopDepth := inferenceContext.loopDepth + 1} expectedReturn bodyResult frames target) :
    StatementConclusion selected inferenceContext expectedReturn result frames target := by
  have resources := selected.body.resources
  have formation := boundary.scope.formation checked
  have canonical := boundary.scope.functionsCanonical checked
  have catalog := boundary.scope.catalog checked
  have allocatedInvariant := boundary.invariant.allocateStatementId rfl
  have allocatedOperational := boundary.operational.allocateStatementId
  obtain ⟨conditionValue, conditionState, bodyResult, conditionAccepted, bodyAccepted,
      resultEq, containsRaw⟩ :=
    inferStatementFuel_success_whileLoop_facts form rfl boundary.accepted (bodyRoots selected)
  obtain ⟨otherState, otherBody, ⟨otherCondition, otherAccepted⟩, otherBodyAccepted,
      _, bodyExtension, bodyPatterns, bodyRequirements⟩ :=
    inferStatementFuel_success_whileLoop_child_provenance form rfl boundary.accepted
      boundary.invariant.nodesBelow (bodyRoots selected)
  rw [conditionAccepted] at otherAccepted
  obtain ⟨rfl, rfl⟩ := (Except.ok.inj otherAccepted).symm
  rw [bodyAccepted] at otherBodyAccepted
  have same := (Except.ok.inj otherBodyAccepted).symm
  subst otherBody
  have conditionExpected : ∀ type ∈ some Ty.bool,
      type.VariablesBelow initial.allocateStatementId.2.inference.next := by
    intro type member
    have same : type = .bool := (Option.some.inj member).symm
    subst type
    exact Ty.variablesBelow_constructor _ _
  have conditionSafe : ∀ binder ∈ initial.allocateStatementId.2.localBinders, ∀ type ∈ some Ty.bool,
      ProtectedVariables.Safe binder.scheme.quantified initial.allocateStatementId.2 type := by
    intro binder _ type member
    have same : type = .bool := (Option.some.inj member).symm
    subst type
    exact ProtectedVariables.safe_closed _ _ (Ty.variablesBelow_constructor _ _)
  have conditionProperties := Detail.inferExprFuel_inferenceProperties allocatedInvariant.ready
    formation canonical conditionExpected conditionAccepted
  have bodyProperties := Detail.inferStatementsFuel_inferenceProperties
    (context := {inferenceContext with loopDepth := inferenceContext.loopDepth + 1}) conditionProperties.2.1
    formation canonical (allocatedInvariant.returnBelow.weaken conditionProperties.1.next_le) bodyAccepted
  have bodySubstitution : selected.body.finalized.substitution.SemanticallyExtends
      bodyResult.state.inference.substitution := by
    simpa [resultEq, State.restoreLexicalScope, State.recordNode] using boundary.extension
  have conditionSubstitution := bodySubstitution.trans bodyProperties.1.substitution_extends
  have conditionInvariant := allocatedInvariant.inferExprFuel conditionAccepted formation canonical
    conditionExpected conditionSubstitution
  have conditionOperational := allocatedOperational.ofExpression allocatedInvariant.ready
    catalog formation canonical conditionExpected conditionSafe conditionAccepted
  have containsFinal := (boundary.rawSubtree.finalized resources).containsStatement containsRaw
  have conditionEdge : DirectChild (result.state.toTypedSource (bodyRoots selected))
      (.statement result.id) (.expression conditionValue.id) :=
    directChild_statement_reference containsRaw (by simp [StatementForm.references])
  have bodyEdge : ∀ child ∈ bodyResult.statements,
      DirectChild (result.state.toTypedSource (bodyRoots selected))
        (.statement result.id) (.statement child) := by
    intro child member
    exact directChild_statement_reference containsRaw (by simp [StatementForm.references, member])
  have bodyLiterals : bodyResult.state.integerLiterals ⊆ selected.body.returned.integerLiterals := by
    simpa [resultEq, State.restoreLexicalScope, State.recordNode] using boundary.integerLiterals
  have conditionSource := (inferStatementsFuel_success_typingSourceExtends bodyAccepted
    conditionInvariant.nodesBelow (bodyRoots selected)).trans bodyExtension
  have conditionHere := descend here (.statement_while_condition boundary.accepted form rfl conditionAccepted)
  have conditionTyping := recursiveExpression conditionHere ({
    accepted := conditionAccepted
    interfaces := boundary.interfaces
    extension := conditionSubstitution
    scope := boundary.scope
    invariant := RecursiveExpressionInvariant.ofStatement allocatedInvariant
    actual := boundary.actual
    operational := allocatedOperational
    expectedBelow := conditionExpected
    expectedAdmissible := by
      intro type member
      have same : type = .bool := (Option.some.inj member).symm
      subst type
      exact TypeAdmissible.bool ((RecursiveExpressionInvariant.ofStatement allocatedInvariant).typeParameterBinders (by
        simpa [boundary.scope.owner, boundary.scope.parameters] using boundary.scope.canonical checked))
    expectedSafe := conditionSafe
    integerPatterns := List.Subset.trans (Detail.inferStatementsFuel_integerPatterns_subset bodyAccepted)
      (List.Subset.trans bodyPatterns boundary.integerPatterns)
    integerLiterals := List.Subset.trans (Detail.inferStatementsFuel_integerLiterals_subset bodyAccepted) bodyLiterals
    requirements := List.Subset.trans (Detail.inferStatementsFuel_requirements_subset bodyAccepted)
      (List.Subset.trans bodyRequirements boundary.requirements)
    covered := TemplateScopeCovered.statementExpressionChild_of_noBindings_and_reference
      boundary.covered resources.graph_closed containsFinal
      (by simp [StatementNode.applySubstitution, StatementForm.applySubstitution, statementInitializedLetBindings])
      (by simp [StatementNode.applySubstitution, StatementForm.applySubstitution, StatementForm.references])
    actualCovered := boundary.actualCovered.statement_reference containsFinal (by
      simp [StatementNode.applySubstitution, StatementForm.applySubstitution, StatementForm.references])
    rawSubtree := (boundary.rawSubtree.child conditionEdge).monoBefore conditionSource } :
    RootedExpressionBoundary selected childFuel inferenceContext condition (some .bool)
      initial.allocateStatementId.2 conditionValue conditionState frames target)
  have bodyReturnSafe : ∀ binder ∈ conditionState.localBinders,
      ProtectedVariables.Safe binder.scheme.quantified conditionState expectedReturn := by
    intro binder member
    have binders : conditionState.localBinders = initial.localBinders :=
      congrArg LexicalScope.binders (Detail.inferExprFuel_success_lexicalScope_eq conditionAccepted)
    have entering : binder ∈ initial.localBinders := binders ▸ member
    have privacy := ProtectedVariables.inferExprFuel_private binder.scheme.quantified childFuel
      inferenceContext condition (some .bool) initial.allocateStatementId.2
      allocatedInvariant.ready allocatedOperational.requirements
      (allocatedOperational.quantifiersBelow binder entering)
      (allocatedOperational.privacy binder entering) catalog formation canonical conditionExpected
      (conditionSafe binder entering) _ conditionAccepted
    exact privacy.1 expectedReturn (returnSafe binder entering)
  obtain ⟨bodyContext, bodyFacts, _, _, bodyOperational, bodyTyping, bodyAgreement⟩ :=
    recursiveBody (descend here (.statement_while_body boundary.accepted form rfl conditionAccepted bodyAccepted))
      bodyReturnSafe returnAdmissible ({
    accepted := bodyAccepted
    interfaces := boundary.interfaces
    extension := bodySubstitution
    scope := boundary.scope.withLoopDepth (inferenceContext.loopDepth + 1)
    invariant := conditionInvariant
    actual := boundary.actual
    operational := conditionOperational
    rawSubtrees := fun child member => (boundary.rawSubtree.child (bodyEdge child member)).monoBefore bodyExtension
    integerPatterns := List.Subset.trans bodyPatterns boundary.integerPatterns
    integerLiterals := bodyLiterals
    requirements := List.Subset.trans bodyRequirements boundary.requirements
    covered := fun child member => TemplateScopeCovered.statementChild boundary.covered
      resources.graph_closed ((boundary.rawSubtree.finalized resources).directChild (bodyEdge child member))
      (fun _ present => present)
    actualCovered := fun child member => boundary.actualCovered.statement_reference containsFinal (by
      simp [StatementNode.applySubstitution, StatementForm.applySubstitution, StatementForm.references, member]) } :
    StatementsBoundary selected childFuel {inferenceContext with loopDepth := inferenceContext.loopDepth + 1} body.value expectedReturn
      conditionState bodyResult frames target)
  let facts : StatementFacts := {
    type := .unit, hasValue := false, sawReturn := false,
    control := .loop bodyFacts.control }
  have active : ActiveLocalContextInvariant result.state selected.body.finalized.substitution target := by
    rw [resultEq]
    exact conditionInvariant.active.restoreLexicalScope_recordNode _
  have operational : GeneralizedActualStateInvariant result.state (evidenceSource selected) := by
    rw [resultEq]
    exact (bodyOperational.restoreSaved conditionOperational.origins
      (ProtectedVariables.inferStatementsFuel_binders_subset bodyAccepted)).recordStatement _ rfl
  have conditionBool : ExpressionHasType selected.body.finalized.typedSource target conditionValue.id .bool := by
    have typeEq : selected.body.finalized.substitution.apply conditionValue.type = .bool := by
      simpa using Detail.inferExprFuel_expected_type_apply_eq conditionAccepted conditionSubstitution
    rw [typeEq] at conditionTyping
    exact conditionTyping
  have typing : StatementHasType selected.body.finalized.typedSource
      { returnType := selected.body.finalized.substitution.apply expectedReturn,
        loopDepth := inferenceContext.loopDepth } target result.id target facts := by
    exact .whileLoop containsFinal rfl conditionBool bodyTyping
      (by simp [StatementNode.applySubstitution, resultEq])
  have agreement : StatementResultMatchesFactsAfterSubstitution
      selected.body.finalized.substitution result facts := by
    rw [resultEq]
    exact StatementResultMatchesFactsAfterSubstitution.whileLoop _ bodyFacts _ _
  have conditionBinders := congrArg LexicalScope.binders
    (Detail.inferExprFuel_success_lexicalScope_eq conditionAccepted)
  have bindersEq : result.state.localBinders = initial.localBinders := by
    simpa [resultEq, State.restoreLexicalScope, State.recordNode, State.lexicalScope] using conditionBinders
  have finalInvariant := boundary.invariant.of_retained_statement_typing boundary.accepted formation canonical active
    (inferStatementFuel_preserves_localBindersBelowNextLocal boundary.invariant.bindersBelow boundary.accepted)
    boundary.extension (activeSchemeQuantifierIsolation_transport boundary.invariant.schemeIsolation bindersEq) typing
  exact ⟨target, facts, finalInvariant, boundary.actual, operational, typing, agreement⟩

theorem statement_while
    {raw : Workspace.RawWorkspace} {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel childFuel : Nat}
    {selected : BodySelection compiled row fuel}
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    (recursiveExpression : ExpressionRootedSoundness selected childFuel)
    {inferenceContext : SourceInference.Context} {statement : Syntax.Statement}
    {condition : Syntax.Expr} {body : Syntax.Block} {expectedReturn : Ty}
    {initial : State} {result : Detail.StatementResult}
    {frames : List InitializedLetBinding} {target : SourceSemantics.Context}
    (form : statement.value = .whileLoop condition body)
    (boundary : StatementBoundary selected (childFuel + 1) inferenceContext statement
      expectedReturn initial result frames target)
    (returnSafe : ∀ binder ∈ initial.localBinders,
      ProtectedVariables.Safe binder.scheme.quantified initial expectedReturn)
    (returnAdmissible : TypeAdmissible target (selected.body.finalized.substitution.apply expectedReturn))
    (recursiveBody : ∀ {bodyInitial : State} {bodyResult : Detail.BlockResult},
      (∀ binder ∈ bodyInitial.localBinders,
        ProtectedVariables.Safe binder.scheme.quantified bodyInitial expectedReturn) →
      TypeAdmissible target (selected.body.finalized.substitution.apply expectedReturn) →
      StatementsBoundary selected childFuel {inferenceContext with loopDepth := inferenceContext.loopDepth + 1} body.value expectedReturn
        bodyInitial bodyResult frames target →
      StatementsConclusion selected {inferenceContext with loopDepth := inferenceContext.loopDepth + 1} expectedReturn bodyResult frames target) :
    StatementConclusion selected inferenceContext expectedReturn result frames target := by
  exact statement_while_for (callProvenance := fun _ => True) checked true_childClosed
    (fun _ boundary => recursiveExpression boundary) True.intro form boundary returnSafe returnAdmissible
    (fun _ safe admissible boundary => recursiveBody safe admissible boundary)

end Solcore.SourceSemantics.SourceCompiledGeneralizedSoundness
end
