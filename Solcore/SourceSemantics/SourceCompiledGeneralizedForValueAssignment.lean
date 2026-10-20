import Solcore.SourceSemantics.SourceCompiledGeneralizedForContracts
import Solcore.SourceSemantics.SourceCompiledGeneralizedAssignedValue

set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledGeneralizedSoundness
open Frontend SourceInference TypeSystem SourceInferenceSoundness
open SourceCompiledLocalFinalization

theorem forItem_assignValue
    {raw : Workspace.RawWorkspace} {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel childFuel : Nat}
    {selected : Selected compiled row fuel}
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
  obtain ⟨typed, operational⟩ := assignedValue_of_actual_children checked placeSound expressionSound ({
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

end Solcore.SourceSemantics.SourceCompiledGeneralizedSoundness
