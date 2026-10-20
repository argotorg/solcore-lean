import Solcore.SourceSemantics.SourceInferenceGeneralizationLifetimeStateSteps
import Solcore.SourceSemantics.SourceInferenceActualAssignmentProperties

/-! Actual assignment places and values retain events across the operator fit. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
open Frontend SourceInference TypeSystem Detail SourceInferenceExecution
namespace GeneralizationLifetime
variable {whole : TypedSource} {finalSubstitution : Substitution}
    {binder : TypedBinder} {initializer : ExpressionId}
    {event : RetainedGeneralization whole finalSubstitution binder initializer}


theorem assignedValue_place
    {fuel : Nat} {context : SourceInference.Context} {target value : Syntax.Expr}
    {operator : Syntax.ValueAssignOp} {initial final targetState : State}
    {assignment : AssignmentResolution} {inferred : InferredExpression} {place : PlaceResolution}
    (ready : initial.InferenceReady) (wellFormed : initial.RequirementsWellFormed)
    (catalog : LifetimeInferenceContext context)
    (placeAccepted : inferPlaceFuel fuel context target initial = .ok (place, targetState))
    (accepted : inferAssignedValueFuel fuel context target operator value initial = .ok (assignment, inferred, final))
    (lifetime : GeneralizationLifetime event initial.inference.next targetState [place.type]) :
    GeneralizationLifetime event initial.inference.next final [assignment.target.type, inferred.type] := by
  obtain ⟨actualPlace, actualState, fitted, actualPlaceAccepted, fitting, valueAccepted, targetEq⟩ :=
    assignedValue_actual_prefix accepted
  cases Except.ok.inj (actualPlaceAccepted.symm.trans placeAccepted)
  have fitting : assignmentFit operator targetState place.type =
      (Except.ok fitted : Except Error State) := by cases operator <;> exact fitting
  have placeProperties := inferPlaceFuel_inferenceProperties ready catalog.formation catalog.canonical placeAccepted
  have fitProperties := assignmentFit_properties placeProperties.2.1 placeProperties.2.2 fitting
  have fittedLife : GeneralizationLifetime event initial.inference.next fitted [place.type] := by
    cases operator <;> simp only [assignmentFit] at fitting
    all_goals first
    | (change Except.ok targetState = Except.ok fitted at fitting
       cases Except.ok.inj fitting
       exact lifetime)
    | exact lifetime.unify placeProperties.2.1 placeProperties.2.2 (Ty.variablesBelow_constructor _ _)
        (lifetime.values _ (by simp)) (safe_closed _ _ (Ty.variablesBelow_constructor _ _)) fitting
  have fittedWF : fitted.RequirementsWellFormed := by
    have placeWF := (inferPlaceFuel_direct_progress placeAccepted).wellFormed wellFormed
    cases operator <;> simp only [assignmentFit] at fitting
    all_goals first
    | (change Except.ok targetState = Except.ok fitted at fitting
       cases Except.ok.inj fitting
       exact placeWF)
    | exact unify_preserves_requirementsWellFormed fitting placeWF
  have expectedSafe : Safe binder.scheme.quantified fitted (assignmentExpected operator fitted place.type) := by
    cases operator <;> simp only [assignmentFit] at fitting
    all_goals first
    | exact safe_resolved fitProperties.2.1 (fittedLife.values _ (by simp))
    | exact safe_closed _ _ (Ty.variablesBelow_constructor _ _)
  have valueProperties := inferExprFuel_inferenceProperties fitProperties.2.1 catalog.formation catalog.canonical
    (by intro type member; cases member; exact fitProperties.2.2) valueAccepted
  have after := fittedLife.inferExpr fitProperties.2.1 fittedWF catalog
    (by intro type member; cases member; exact fitProperties.2.2)
    (by intro type member; cases member; exact expectedSafe) valueAccepted
  apply after.replaceOutputs
  intro type member
  rcases List.mem_cons.mp member with rfl | member
  · rw [targetEq]
    exact safe_resolved valueProperties.2.1 (after.values _ (by simp))
  · exact after.values _ (List.mem_append_right _ member)

theorem assignedValue_value
    {fuel : Nat} {context : SourceInference.Context} {target value : Syntax.Expr}
    {operator : Syntax.ValueAssignOp} {initial final targetState fitted childFinal : State}
    {assignment : AssignmentResolution} {inferred childValue : InferredExpression} {place : PlaceResolution}
    (ready : initial.InferenceReady) (catalog : LifetimeInferenceContext context)
    (placeAccepted : inferPlaceFuel fuel context target initial = .ok (place, targetState))
    (fitting : assignmentFit operator targetState place.type =
      (Except.ok fitted : Except Error State))
    (valueAccepted : inferExprFuel fuel context value (some (assignmentExpected operator fitted place.type)) fitted = .ok (childValue, childFinal))
    (accepted : inferAssignedValueFuel fuel context target operator value initial = .ok (assignment, inferred, final))
    (lifetime : GeneralizationLifetime event fitted.inference.next childFinal [childValue.type]) :
    GeneralizationLifetime event initial.inference.next final [assignment.target.type, inferred.type] := by
  obtain ⟨actualPlace, actualState, actualFitted, actualPlaceAccepted, actualFitting, actualValueAccepted, targetEq⟩ :=
    assignedValue_actual_prefix accepted
  cases Except.ok.inj (actualPlaceAccepted.symm.trans placeAccepted)
  have actualFitting : assignmentFit operator targetState place.type =
      (Except.ok actualFitted : Except Error State) := by cases operator <;> exact actualFitting
  cases Except.ok.inj (actualFitting.symm.trans fitting)
  cases Except.ok.inj (actualValueAccepted.symm.trans valueAccepted)
  have placeProperties := inferPlaceFuel_inferenceProperties ready catalog.formation catalog.canonical placeAccepted
  have fitProperties := assignmentFit_properties placeProperties.2.1 placeProperties.2.2 fitting
  have valueProperties := inferExprFuel_inferenceProperties fitProperties.2.1 catalog.formation catalog.canonical
    (by intro type member; cases member; exact fitProperties.2.2) valueAccepted
  have after := lifetime.weaken_entry (placeProperties.1.trans fitProperties.1).next_le
  apply after.replaceOutputs
  intro type member
  rcases List.mem_cons.mp member with rfl | member
  · rw [targetEq]
    exact safe_resolved valueProperties.2.1 (lifetime.older _ (placeProperties.2.2.weaken fitProperties.1.next_le))
  · exact lifetime.values _ member

end GeneralizationLifetime
end Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
