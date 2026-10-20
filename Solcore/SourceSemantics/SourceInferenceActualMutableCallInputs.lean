import Solcore.SourceSemantics.SourceInferenceActualAssignmentProperties

/-! Actual place, value-assignment and header prefixes supply child inputs. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceExecution
open Frontend SourceInference TypeSystem Detail SourceInferenceSoundness.ProtectedVariables
namespace ChildStep

theorem inputs_forItem
    {fuel : Nat} {context : SourceInference.Context} {source : Syntax.ForItem}
    {initial final : State} {value : ForItemForm} {child : CallIndex}
    (inputs : (CallIndex.forItem fuel context source initial value final).Inputs)
    (step : ChildStep (.forItem fuel context source initial value final) child) : child.Inputs := by
  cases step with
  | forItem_initializer _ _ annotation _ =>
      refine ⟨inputs.ready, inputs.wellFormed, inputs.catalog, ?_⟩
      cases annotation with
      | absent => simp [CallIndex.InputBounds]
      | present accepted =>
          intro type member
          cases member
          exact resolveSourceType_success_variablesBelow accepted _
  | forItem_expression => exact ⟨inputs.ready, inputs.wellFormed, inputs.catalog, by simp [CallIndex.InputBounds]⟩
  | forItem_assignment => exact ⟨inputs.ready, inputs.wellFormed, inputs.catalog, trivial⟩
  | forItem_bitnot => exact ⟨inputs.ready, inputs.wellFormed, inputs.catalog, trivial⟩

theorem inputs_place
    {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Expr}
    {initial final : State} {value : PlaceResolution} {child : CallIndex}
    (inputs : (CallIndex.place fuel context source initial value final).Inputs)
    (step : ChildStep (.place fuel context source initial value final) child) : child.Inputs := by
  cases step with
  | place_group => exact ⟨inputs.ready, inputs.wellFormed, inputs.catalog, trivial⟩
  | place_index_base => exact ⟨inputs.ready, inputs.wellFormed, inputs.catalog, trivial⟩
  | @place_index_key fuel context source initial final result base key brackets baseValue baseState keyState valueState fitted childFinal keyType valueType keyValue _ _ baseAccepted keyFresh valueFresh fitting _ =>
      have baseProperties := inferPlaceFuel_inferenceProperties inputs.ready inputs.catalog.formation inputs.catalog.canonical baseAccepted
      have keyProperties := fresh_eq_inferenceProperties baseProperties.2.1 keyFresh
      have valueProperties := fresh_eq_inferenceProperties keyProperties.2.1 valueFresh
      have baseBelow := baseProperties.2.2.weaken (keyProperties.1.trans valueProperties.1).next_le
      have keyBelow := keyProperties.2.2.weaken valueProperties.1.next_le
      have mappingBelow := (Ty.variablesBelow_mapping_iff _ _ _).mpr ⟨keyBelow, valueProperties.2.2⟩
      have mappingProgress := unify_inferenceProgress valueProperties.2.1.solved baseBelow mappingBelow fitting
      have mappingReady := unify_preserves_inferenceReady valueProperties.2.1 baseBelow mappingBelow fitting
      have baseWF := (inferPlaceFuel_direct_progress baseAccepted).wellFormed inputs.wellFormed
      have valueWF : valueState.RequirementsWellFormed := by
        rw [← show keyState.fresh.2 = valueState from congrArg Prod.snd valueFresh,
          ← show baseState.fresh.2 = keyState from congrArg Prod.snd keyFresh]
        exact baseWF
      refine ⟨mappingReady, unify_preserves_requirementsWellFormed fitting valueWF, inputs.catalog, ?_⟩
      intro type member
      cases member
      exact mappingReady.solved.variablesBelow_apply (keyBelow.weaken mappingProgress.next_le)

theorem inputs_assignedValue
    {fuel : Nat} {context : SourceInference.Context} {target source : Syntax.Expr}
    {operator : Syntax.ValueAssignOp} {initial final : State}
    {assignment : AssignmentResolution} {value : InferredExpression} {child : CallIndex}
    (inputs : (CallIndex.assignedValue fuel context target operator source initial assignment value final).Inputs)
    (step : ChildStep (.assignedValue fuel context target operator source initial assignment value final) child) : child.Inputs := by
  cases step with
  | assignedValue_place => exact ⟨inputs.ready, inputs.wellFormed, inputs.catalog, trivial⟩
  | @assignedValue_value fuel context target source operator initial final targetState assignment value place fitted childFinal childValue _ placeAccepted fitting _ =>
      have fitting : assignmentFit operator targetState place.type = .ok fitted := by cases operator <;> exact fitting
      have placeProperties := inferPlaceFuel_inferenceProperties inputs.ready inputs.catalog.formation inputs.catalog.canonical placeAccepted
      have fitProperties := assignmentFit_properties placeProperties.2.1 placeProperties.2.2 fitting
      have fittedWF : fitted.RequirementsWellFormed := by
        have placeWF := (inferPlaceFuel_direct_progress placeAccepted).wellFormed inputs.wellFormed
        cases operator <;> simp only [assignmentFit] at fitting
        all_goals first
        | (change Except.ok targetState = Except.ok fitted at fitting
           cases Except.ok.inj fitting
           exact placeWF)
        | exact unify_preserves_requirementsWellFormed fitting placeWF
      refine ⟨fitProperties.2.1, fittedWF, inputs.catalog, ?_⟩
      intro type member
      cases member
      exact fitProperties.2.2

end ChildStep
end Solcore.SourceSemantics.SourceInferenceExecution
