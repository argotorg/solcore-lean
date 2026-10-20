import Solcore.SourceSemantics.SourceCompiledBodySelectionFormation
import Solcore.SourceSemantics.SourceCompiledGeneralizedForContracts
import Solcore.SourceSemantics.SourceInferenceGeneralizedLambdaParameters
import Solcore.SourceSemantics.SourceInferenceSelectedAnnotatedForItems

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
