import Solcore.SourceSemantics.SourceInferenceGeneralizedHeaderInitializerState
import Solcore.SourceSemantics.SourceCompiledNormalizedTemplates
import Solcore.SourceSemantics.SourceCompiledGeneralizedInitializerContexts
import Solcore.SourceSemantics.SourceCompiledGeneralizedExpressionRooted

set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledGeneralizedSoundness
open Frontend SourceInference TypeSystem SourceInferenceSoundness
open SourceCompiledLocalFinalization SourceInferenceStatementsSoundness ProtectedVariables

private theorem annotation_admissible
    {inferenceContext : SourceInference.Context} {target : SourceSemantics.Context}
    {annotation : Option Syntax.TypeExpr} {expected : Option Ty} {outer : Substitution}
    (canonical : SignatureParametersWellFormed inferenceContext.scope.genericOwner inferenceContext.typeParameters)
    (signatures : target.signatures = inferenceContext.signatures)
    (parameters : target.typeParameters = inferenceContext.typeParameters)
    (owner : target.currentDeclaration = some inferenceContext.scope.genericOwner)
    (accepted : SourceInference.LocalLetRequirementTiming.Annotation inferenceContext annotation expected) :
    ∀ type ∈ expected, TypeAdmissible target (outer.apply type) := by
  cases accepted with
  | none => simp
  | some resolved =>
    intro type present
    cases Option.mem_def.mp present
    rw [Detail.resolveSourceType_success_apply_eq_self _ resolved]
    exact TypeAdmissible.ofWellFormed
      (resolveSourceType_success_typeWellFormed canonical signatures parameters owner resolved)

/-- The only remaining generalization premise concerns this exact header
allocation. Its child, source ownership and final predicates are produced by
actual inference and the selected finalizer. -/
theorem forItem_initialized_of_receipt
    {raw : Workspace.RawWorkspace} {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel childFuel : Nat}
    {selected : Selected compiled row fuel}
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    (childSound : ExpressionRootedSoundness selected childFuel)
    {inferenceContext : SourceInference.Context} {item : Syntax.ForItem}
    {expectedReturn : Ty} {initial final : State} {inferred : ForItemForm}
    {frames : List InitializedLetBinding} {target : SourceSemantics.Context}
    (boundary : ForItemBoundary selected (childFuel + 1) inferenceContext item expectedReturn
      initial inferred final frames target)
    (receipt : SourceInference.LocalHeaderRequirementTiming.Receipt childFuel inferenceContext item initial (inferred, final))
    (barrier : GeneralizationBarrierTransport receipt.ready receipt.locals initial.nextRequirement
      (receipt.ready.resolve receipt.value.type) selected.body.finalized.substitution target
      (localSchemeTemplateIds (receipt.binding.1.applySubstitution selected.body.finalized.substitution))) :
    ForItemConclusion selected inferenceContext expectedReturn inferred final frames target := by
  have formation := boundary.scope.formation checked
  have canonical := boundary.scope.functionsCanonical checked
  have catalog := boundary.scope.catalog checked
  have itemEq : inferred = .letDecl receipt.binding.1 (some receipt.value.id) := receipt.recorded
  have properties := receipt.initializer_inference boundary.invariant.ready formation canonical
  have extension : selected.body.finalized.substitution.SemanticallyExtends receipt.ready.inference.substitution := by
    have atResult := boundary.extension
    rw [receipt.inference_eq] at atResult
    exact atResult
  have priorAvoided := ProtectedVariables.LocalHeaderRequirementTiming.Receipt.value_avoids_active receipt
    boundary.invariant.ready boundary.operational.requirements boundary.operational.quantifiersBelow
    boundary.operational.privacy catalog formation canonical
  let binding : InitializedLetBinding := ⟨receipt.binding.1, .expression receipt.value.id⟩
  let closed : InitializedLetBinding := ⟨receipt.binding.1.applySubstitution selected.body.finalized.substitution,
    .expression receipt.value.id⟩
  have bindingMember : binding ∈ forItemInitializedLetBindings inferred := by
    rw [itemEq]
    exact List.mem_singleton_self _
  have retained := boundary.bindingsRetained binding bindingMember
  have noCapture := selected.body.resources.local_no_capture receipt.binding.1 retained.1
  have finalBody : closed.binder.scheme.body = selected.body.finalized.substitution.apply receipt.value.type := by
    have restriction : selected.body.finalized.substitution.without receipt.binding.1.scheme.quantified =
        selected.body.finalized.substitution :=
      FlexibleSubstitution.Substitution.without_eq_self_of_disjoint_domain _ _ noCapture.quantified_fresh
    have body : receipt.binding.1.scheme.body = receipt.ready.resolve receipt.value.type := by
      change receipt.generalized.scheme.body = _
      exact Detail.generalizeValue_scheme_body _ _ _ _
    change (receipt.binding.1.applySubstitution selected.body.finalized.substitution).scheme.body = _
    rw [FlexibleSubstitution.applyTypedBinder_scheme]
    change (selected.body.finalized.substitution.without receipt.binding.1.scheme.quantified).apply
      receipt.binding.1.scheme.body = _
    rw [restriction, body]
    exact extension receipt.value.type
  have childInvariant := (RecursiveExpressionInvariant.ofStatement boundary.invariant).generalizedInitializer closed.binder
  have nested := boundary.actualBindings binding bindingMember
  have childActual := boundary.actual.initializer closed nested.1 nested.2
  have reference : (.expression receipt.value.id : NodeId) ∈ inferred.references := by
    simp [itemEq, ForItemForm.references]
  have childCovered : ActualContext.Covers selected.body.finalized (frames ++ [closed]) (.expression receipt.value.id) :=
    (boundary.actualCovered _ reference).push (.inl rfl)
  have childSource : TypingSourceExtends (receipt.ready.toTypedSource (bodyRoots selected))
      (final.toTypedSource (bodyRoots selected)) := by
    have nodes : final.nodes = receipt.ready.nodes := congrArg (fun p : ForItemForm × State => p.2.nodes) receipt.completed
    refine ⟨congrArg (fun p : ForItemForm × State => p.2.owner) receipt.completed, ?_⟩
    change receipt.ready.nodes <+: final.nodes
    simpa only [nodes] using List.prefix_refl receipt.ready.nodes
  have patternEq : final.integerPatterns = receipt.ready.integerPatterns :=
    congrArg (fun p : ForItemForm × State => p.2.integerPatterns) receipt.completed
  have literalEq : final.integerLiterals = receipt.ready.integerLiterals :=
    congrArg (fun p : ForItemForm × State => p.2.integerLiterals) receipt.completed
  have requirementEq : final.requirements = receipt.ready.requirements :=
    congrArg (fun p : ForItemForm × State => p.2.requirements) receipt.completed
  have childTyping := childSound ({
    accepted := receipt.child, interfaces := boundary.interfaces, extension := extension, scope := boundary.scope
    invariant := childInvariant, actual := childActual, operational := boundary.operational
    expectedBelow := receipt.annotationAccepted.variablesBelow _
    expectedAdmissible := annotation_admissible (boundary.scope.canonical checked)
      (childInvariant.signatures_eq_whole.trans boundary.scope.signatures.symm)
      (childInvariant.typeParametersEq.trans boundary.scope.parameters.symm)
      (childInvariant.declarationEq.trans (congrArg some boundary.scope.owner.symm)) receipt.annotationAccepted
    expectedSafe := by
      intro binder member type present
      exact safe_closed _ _ (receipt.annotationAccepted.variablesBelow 0 type present)
    rawSubtree := (boundary.rawReferences _ reference).monoBefore childSource
    integerPatterns := by simpa only [patternEq] using boundary.integerPatterns
    integerLiterals := by simpa only [literalEq] using boundary.integerLiterals
    requirements := by simpa only [requirementEq] using boundary.requirements
    covered := by
      have covered := boundary.covered _ reference
      simpa only [itemEq, forItemCoverageContext, closed] using covered
    actualCovered := childCovered } : RootedExpressionBoundary selected childFuel inferenceContext
      receipt.initializer receipt.expected initial receipt.value receipt.ready (frames ++ [closed])
      (localSchemeInitializerContext target closed.binder))
  have declarationEq := (ProgramEnvironment.declaration?_sound selected.body.declared).2
  have owner : target.currentDeclaration = some selected.signature.id := by
    simpa only [checkingContext, context, ProgramTypeScope.ofDeclaration, declarationEq] using boundary.invariant.declarationEq
  have finalPredicates := selected.originalBindingPredicates checked
    (RecursiveExpressionInvariant.ofStatement boundary.invariant).signatures_eq_whole
    boundary.invariant.typeParametersEq owner boundary.invariant.residual retained.2
  have certificate : UnannotatedInitializedLetCertificate (evidenceSource selected) target
      selected.body.finalized.substitution receipt.binding.1 receipt.value.id := by
    apply unannotatedInitializedLetCertificate_of_finalBarrier_retained selected.body.resources
      (source := evidenceSource selected) (state := receipt.ready) (final := receipt.binding.2)
      (name := receipt.name) (generalized := receipt.generalized)
      rfl rfl rfl boundary.invariant.signaturesEq boundary.invariant.assumptionsMono
      boundary.invariant.solvedRequirementsEq retained.1 retained.2 barrier finalPredicates
      (priorQuantifiersBlockedAt_of_activeQuantifiersAvoided boundary.invariant.active.aligned priorAvoided)
    rw [← selected.body.resources.source_eq]
    change ExpressionHasType selected.body.finalized.typedSource
      (localSchemeInitializerContext target closed.binder) receipt.value.id closed.binder.scheme.body
    rw [finalBody]
    exact childTyping
  have readyActive := boundary.invariant.active.inferExprFuel receipt.child
  have readyBelow := Detail.inferExprFuel_preserves_localBindersBelowNextLocal boundary.invariant.bindersBelow receipt.child
  have sourceOwner : (evidenceSource selected).owner = receipt.ready.owner := by
    have evidenceOwner : (evidenceSource selected).owner = initial.owner := by
      have sourceEq : (evidenceSource selected).owner = selected.body.finalized.typedSource.owner := by
        rw [selected.body.resources.source_eq]
        rfl
      exact sourceEq.trans boundary.owner
    exact evidenceOwner.trans (Detail.inferExprFuel_preserves_owner receipt.child).symm
  obtain ⟨finalContext, active, typing⟩ := unannotatedInitializedForItemHasType_afterSubstitution
    (control := {returnType := selected.body.finalized.substitution.apply expectedReturn, loopDepth := inferenceContext.loopDepth})
    (source := evidenceSource selected) (name := receipt.name)
    (requirementStart := initial.nextRequirement) (generalized := receipt.generalized) rfl rfl
    readyActive readyBelow sourceOwner certificate
  have finalEq : final = receipt.binding.2 := congrArg Prod.snd receipt.completed
  have finalTyping : ForItemHasType selected.body.finalized.typedSource
      {returnType := selected.body.finalized.substitution.apply expectedReturn, loopDepth := inferenceContext.loopDepth}
      target (inferred.applySubstitution selected.body.finalized.substitution) finalContext := by
    rw [itemEq]
    rw [← selected.body.resources.source_eq] at typing
    exact typing
  have finalActive : ActiveLocalContextInvariant final selected.body.finalized.substitution finalContext := by
    rw [finalEq]
    exact active
  have allRetained : inferred.initializedLetBinders ⊆ (evidenceSource selected).initializedLetBinders := by
    rw [itemEq]
    intro binder member
    have same : binder = receipt.binding.1 := List.mem_singleton.mp member
    exact same ▸ retained.1
  have operational := boundary.operational.ofRetainedHeader selected.body.resources boundary.invariant.ready
    catalog formation canonical allRetained boundary.extension boundary.accepted
  have isolation := SourceInferenceSoundness.LocalHeaderRequirementTiming.Receipt.schemeIsolation receipt properties.2.1
    priorAvoided boundary.invariant.schemeIsolation operational.privacy
  have finalInvariant := RecursiveStatementInvariant.of_forItem_typing boundary.invariant boundary.accepted
    formation canonical finalActive isolation boundary.extension finalTyping
  exact ⟨finalContext, finalInvariant, boundary.actual.of_forItem finalTyping, operational, finalTyping⟩

end Solcore.SourceSemantics.SourceCompiledGeneralizedSoundness
