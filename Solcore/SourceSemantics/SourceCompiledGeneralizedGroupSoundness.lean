import Solcore.SourceSemantics.SourceCompiledBodySelectionFormation
import Solcore.SourceSemantics.SourceCompiledGeneralizedExpressionRooted
import Solcore.SourceSemantics.SourceInferenceSelectedOrdinaryRecorder

set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledGeneralizedSoundness
open Frontend SourceInference TypeSystem SourceInferenceSoundness
open SourceCompiledLocalFinalization

/-- The actual group child is checked in the same selected final source. -/
theorem expressionRetained_group
    {raw : Workspace.RawWorkspace} {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel childFuel : Nat}
    {selected : BodySelection compiled row fuel}
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    (recursive : ExpressionRetainedSoundness selected childFuel)
    {inferenceContext : SourceInference.Context} {expression inner : Syntax.Expr}
    {expected : Option Ty} {initial resultState : State} {inferred : InferredExpression}
    {frames : List InitializedLetBinding} {target : SourceSemantics.Context}
    (expressionEq : expression.value = .group inner)
    (boundary : RetainedExpressionBoundary selected (childFuel + 1) inferenceContext
      expression expected initial inferred resultState frames target) :
    ExpressionTypingBase (resultState.toTypedSource (bodyRoots selected))
      selected.body.finalized.typedSource target selected.body.finalized.substitution inferred := by
  have resources := selected.body.resources
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
  obtain ⟨innerResult, innerState, innerSuccess, recorded⟩ :=
    Detail.inferExprFuel_success_group_facts expressionEq allocationEq boundary.accepted
  have properties := Detail.inferExprFuel_inferenceProperties allocatedInvariant.ready
    (boundary.scope.formation checked) (boundary.scope.functionsCanonical checked) allocatedExpected innerSuccess
  have innerExpected : ∀ type ∈ expected, type.VariablesBelow innerState.inference.next := by
    intro type member
    exact (allocatedExpected type member).weaken properties.1.next_le
  have recording := Detail.recordExpressionWithExpected_inferenceProperties
    properties.2.1 properties.2.2 innerExpected recorded
  have innerExtension := boundary.extension.trans recording.1.substitution_extends
  have allocatedOwner : allocated.owner = initial.owner := by
    have stateEq : initial.allocateExpressionId.2 = allocated := congrArg Prod.snd allocationEq
    rw [← stateEq]
    rfl
  have innerToParent : TypingSourceExtends (innerState.toTypedSource (bodyRoots selected))
      (resultState.toTypedSource (bodyRoots selected)) := by
    refine ⟨?_, recordExpressionWithExpected_success_nodesPrefix recorded⟩
    exact (Detail.inferExprFuel_preserves_owner boundary.accepted).trans
      (allocatedOwner.symm.trans (Detail.inferExprFuel_preserves_owner innerSuccess).symm)
  obtain ⟨coercions, contains⟩ := recordExpressionWithExpected_success_containsExpression recorded (bodyRoots selected)
  have edge : DirectChild (resultState.toTypedSource (bodyRoots selected))
      (.expression inferred.id) (.expression innerResult.id) := by
    refine ⟨.expression _, ⟨contains.1, rfl⟩, ?_⟩
    simp [nodeChildIds, Node.references, ExpressionForm.references]
  have finalEdge := boundary.directChildren edge
  have childPatterns : innerState.integerPatterns ⊆ selected.body.returned.integerPatterns := by
    rw [← recordExpressionWithExpected_integerPatterns_eq recorded]
    exact boundary.integerPatterns
  have childLiterals : innerState.integerLiterals ⊆ selected.body.returned.integerLiterals := by
    rw [← Detail.recordExpressionWithExpected_integerLiterals_eq recorded]
    exact boundary.integerLiterals
  have childRequirements := List.Subset.trans
    (Detail.recordExpressionWithExpected_requirements_subset recorded) boundary.requirements
  have typed := expressionRooted_of_retained checked recursive ({
    accepted := innerSuccess
    interfaces := boundary.interfaces
    extension := innerExtension
    scope := boundary.scope
    invariant := allocatedInvariant
    actual := boundary.actual
    operational := allocatedOperational
    expectedBelow := allocatedExpected
    expectedAdmissible := boundary.expectedAdmissible
    expectedSafe := allocatedSafe
    integerPatterns := childPatterns
    integerLiterals := childLiterals
    requirements := childRequirements
    covered := boundary.covered.expressionChild resources.graph_closed finalEdge
    actualCovered := boundary.actualCovered.directChild finalEdge
    rawSubtree := (boundary.rawProper.childSubtree edge).monoBefore innerToParent } :
    RootedExpressionBoundary selected childFuel inferenceContext inner expected
      allocated innerResult innerState frames target)
  have formType : ExpressionFormHasRawType selected.body.finalized.typedSource target
      ((ExpressionForm.group innerResult.id).applySubstitution selected.body.finalized.substitution)
      (selected.body.finalized.substitution.apply innerResult.type) (.ordinary []) := by
    simpa [ExpressionForm.applySubstitution] using ExpressionFormHasRawType.group typed
  exact recordExpressionWithExpected_success_expressionTypingBase_actual resources boundary.interfaces
    recorded boundary.extension boundary.requirements boundary.expressionRequirements boundary.coercionPrimaries
    (boundary.scope.catalog checked) boundary.scope.signatures boundary.invariant formType typed.type_admissible boundary.covered

end Solcore.SourceSemantics.SourceCompiledGeneralizedSoundness
