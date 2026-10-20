import Solcore.SourceSemantics.SourceCompiledBodySelectionFormation
import Solcore.SourceSemantics.SourceInferenceGeneralizedForState
import Solcore.SourceSemantics.SourceCompiledGeneralizedPlaceContracts

set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledGeneralizedSoundness
open Frontend SourceInference TypeSystem SourceInferenceSoundness
open SourceCompiledLocalFinalization

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
  obtain ⟨placeTyped, _placeOperational, _placeSafe⟩ := placeSound ({
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

end Solcore.SourceSemantics.SourceCompiledGeneralizedSoundness
