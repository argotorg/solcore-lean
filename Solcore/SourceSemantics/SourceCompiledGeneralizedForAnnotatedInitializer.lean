import Solcore.SourceSemantics.SourceCompiledBodySelectionFormation
import Solcore.SourceSemantics.SourceCompiledGeneralizedForContracts
import Solcore.SourceSemantics.SourceInferenceGeneralizedLambdaParameters
import Solcore.SourceSemantics.SourceInferenceSelectedAnnotatedForItems

set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledGeneralizedSoundness
open Frontend SourceInference TypeSystem SourceInferenceSoundness
open SourceCompiledLocalFinalization

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
  have childTyped := expressionSound ({
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

end Solcore.SourceSemantics.SourceCompiledGeneralizedSoundness
