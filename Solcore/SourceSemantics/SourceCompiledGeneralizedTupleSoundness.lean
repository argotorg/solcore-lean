import Solcore.SourceSemantics.SourceCompiledBodySelectionFormation
import Solcore.SourceSemantics.SourceCompiledGeneralizedExpressionList
import Solcore.SourceSemantics.SourceInferenceSelectedOrdinaryRecorder

set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledGeneralizedSoundness
open Frontend SourceInference TypeSystem SourceInferenceSoundness
open SourceCompiledLocalFinalization SourceInferenceExecution

/-- The actual tuple elements share the selected finalizer and carry generalized state through their ordered checker calls. -/
theorem expressionRetained_tuple_for
    {raw : Workspace.RawWorkspace} {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel childFuel : Nat}
    {selected : BodySelection compiled row fuel}
    {provenance : CallIndex → Prop}
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    (descend : ChildClosed provenance)
    (recursive : ∀ smaller, smaller < childFuel + 1 → ExpressionRetainedSoundnessFor provenance selected smaller)
    {inferenceContext : SourceInference.Context} {expression : Syntax.Expr} {elements : Syntax.DelimitedList Syntax.Expr}
    {expected : Option Ty} {initial resultState : State} {inferred : InferredExpression}
    {frames : List InitializedLetBinding} {target : SourceSemantics.Context}
    (here : provenance (.expression (childFuel + 1) inferenceContext expression expected
      initial inferred resultState))
    (expressionEq : expression.value = .tuple elements)
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
  have allocatedExpected : ∀ type ∈ expected, type.VariablesBelow allocated.inference.next := by
    rw [allocateExpressionId_inferenceNext_eq allocationEq]
    exact boundary.expectedBelow
  obtain ⟨elementsResult, elementsState, elementsSuccess, recorded⟩ :=
    Detail.inferExprFuel_success_tuple_facts expressionEq allocationEq boundary.accepted
  have properties := Detail.inferExprsFuel_inferenceProperties allocatedInvariant.ready
    (boundary.scope.formation checked) (boundary.scope.functionsCanonical checked) elementsSuccess
  have elementsExpected : ∀ type ∈ expected, type.VariablesBelow elementsState.inference.next := by
    intro type member
    exact (allocatedExpected type member).weaken properties.1.next_le
  have rawBelow : (Ty.productMany (elementsResult.map (·.type))).VariablesBelow elementsState.inference.next :=
    Ty.variablesBelow_productMany (by
      intro type member
      obtain ⟨element, elementMember, rfl⟩ := List.mem_map.mp member
      exact properties.2.2 element elementMember)
  have recording := Detail.recordExpressionWithExpected_inferenceProperties
    properties.2.1 rawBelow elementsExpected recorded
  have elementsExtension := boundary.extension.trans recording.1.substitution_extends
  have allocatedOwner : allocated.owner = initial.owner := by
    have stateEq : initial.allocateExpressionId.2 = allocated := congrArg Prod.snd allocationEq
    rw [← stateEq]
    rfl
  have allocatedToElements := inferExprsFuel_success_typingSourceExtends_under_bound
    elementsSuccess allocatedInvariant.nodesBelow (bodyRoots selected)
  have elementsToParent : TypingSourceExtends (elementsState.toTypedSource (bodyRoots selected))
      (resultState.toTypedSource (bodyRoots selected)) := by
    refine ⟨?_, recordExpressionWithExpected_success_nodesPrefix recorded⟩
    exact (Detail.inferExprFuel_preserves_owner boundary.accepted).trans
      (allocatedOwner.symm.trans allocatedToElements.owner_eq.symm)
  obtain ⟨coercions, contains⟩ := recordExpressionWithExpected_success_containsExpression recorded (bodyRoots selected)
  have edge : ∀ element ∈ elementsResult, DirectChild (resultState.toTypedSource (bodyRoots selected))
      (.expression inferred.id) (.expression element.id) := by
    intro element member
    refine ⟨.expression _, ⟨contains.1, rfl⟩, ?_⟩
    simpa [nodeChildIds, Node.references, ExpressionForm.references] using
      (List.mem_map.mpr ⟨element.id, List.mem_map.mpr ⟨element, member, rfl⟩, rfl⟩ :
        NodeId.expression element.id ∈ (elementsResult.map (·.id)).map NodeId.expression)
  have childPatterns : elementsState.integerPatterns ⊆ selected.body.returned.integerPatterns := by
    rw [← recordExpressionWithExpected_integerPatterns_eq recorded]
    exact boundary.integerPatterns
  have childLiterals : elementsState.integerLiterals ⊆ selected.body.returned.integerLiterals := by
    rw [← Detail.recordExpressionWithExpected_integerLiterals_eq recorded]
    exact boundary.integerLiterals
  have childRequirements := List.Subset.trans
    (Detail.recordExpressionWithExpected_requirements_subset recorded) boundary.requirements
  have elementsHere := descend here
    (ChildStep.expression_tuple boundary.accepted expressionEq allocationEq elementsSuccess)
  have typed := expressionsRooted_for checked descend childFuel
    (fun smaller less => recursive smaller (Nat.lt_trans less (Nat.lt_succ_self childFuel)))
    elementsHere elementsSuccess boundary.interfaces elementsExtension boundary.scope
    allocatedInvariant boundary.actual allocatedOperational
    (fun element member => (boundary.rawProper.childSubtree (edge element member)).monoBefore elementsToParent)
    childPatterns childLiterals childRequirements
    (fun element member => boundary.covered.expressionChild resources.graph_closed
      (boundary.directChildren (edge element member)))
    (fun element member => boundary.actualCovered.directChild (boundary.directChildren (edge element member)))
  have formType : ExpressionFormHasRawType selected.body.finalized.typedSource target
      ((ExpressionForm.tuple (elementsResult.map (·.id))).applySubstitution selected.body.finalized.substitution)
      (selected.body.finalized.substitution.apply (Ty.productMany (elementsResult.map (·.type)))) (.ordinary []) := by
    simpa [ExpressionForm.applySubstitution, FlexibleSubstitution.apply_productMany,
      List.map_map, Function.comp_def] using ExpressionFormHasRawType.tuple typed
  have rawAdmissible : TypeAdmissible target
      (selected.body.finalized.substitution.apply (Ty.productMany (elementsResult.map (·.type)))) := by
    simpa [FlexibleSubstitution.apply_productMany, List.map_map, Function.comp_def] using
      typed.product_type_admissible (boundary.invariant.typeParameterBinders (by
        simpa [boundary.scope.owner, boundary.scope.parameters] using boundary.scope.canonical checked))
  exact recordExpressionWithExpected_success_expressionTypingBase_actual resources boundary.interfaces
    recorded boundary.extension boundary.requirements boundary.expressionRequirements boundary.coercionPrimaries
    (boundary.scope.catalog checked) boundary.scope.signatures boundary.invariant formType rawAdmissible boundary.covered

/-- Compatibility with unrestricted recursive typing. -/
theorem expressionRetained_tuple
    {raw : Workspace.RawWorkspace} {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel childFuel : Nat}
    {selected : BodySelection compiled row fuel}
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    (recursive : ∀ smaller, smaller < childFuel + 1 → ExpressionRetainedSoundness selected smaller)
    {inferenceContext : SourceInference.Context} {expression : Syntax.Expr} {elements : Syntax.DelimitedList Syntax.Expr}
    {expected : Option Ty} {initial resultState : State} {inferred : InferredExpression}
    {frames : List InitializedLetBinding} {target : SourceSemantics.Context}
    (expressionEq : expression.value = .tuple elements)
    (boundary : RetainedExpressionBoundary selected (childFuel + 1) inferenceContext
      expression expected initial inferred resultState frames target) :
    ExpressionTypingBase (resultState.toTypedSource (bodyRoots selected))
      selected.body.finalized.typedSource target selected.body.finalized.substitution inferred := by
  exact expressionRetained_tuple_for (provenance := fun _ => True) checked true_childClosed
    (fun smaller less => by
      intro context source expected initial final value frames target _ boundary
      exact recursive smaller less boundary) trivial expressionEq boundary

end Solcore.SourceSemantics.SourceCompiledGeneralizedSoundness
