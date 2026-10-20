import Solcore.SourceSemantics.SourceInferenceActualTerminalProgress
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceExecution
open Frontend SourceInference TypeSystem Detail SourceInferenceSoundness.ProtectedVariables
namespace ActualSuffixProgress

theorem assignedValue_value
      {fuel : Nat} {context : SourceInference.Context} {target value : Syntax.Expr}
      {operator : Syntax.ValueAssignOp} {initial final targetState : State}
      {assignment : AssignmentResolution} {inferred : InferredExpression} {place : PlaceResolution}
      {fitted childFinal : State} {childValue : InferredExpression}
      (accepted : (CallIndex.assignedValue fuel context target operator value initial assignment inferred final).Accepted)
      (targetAccepted : inferPlaceFuel fuel context target initial = .ok (place, targetState))
      (fitting : (match operator with | .equal => pure targetState | _ => unify targetState place.type .word) = (Except.ok fitted : Except Error State))
      (child : (CallIndex.expression fuel context value (some (assignmentExpected operator fitted place.type)) fitted childValue childFinal).Accepted)
    (inputs : (CallIndex.assignedValue fuel context target operator value initial assignment inferred final).Inputs) :
    (CallIndex.expression fuel context value (some (assignmentExpected operator fitted place.type)) fitted childValue childFinal).final.InferenceProgress (CallIndex.assignedValue fuel context target operator value initial assignment inferred final).final := by
  simp only [CallIndex.Accepted] at accepted child
  dsimp only [CallIndex.final] at ⊢
  have childReady := ((ChildStep.assignedValue_value accepted targetAccepted fitting child).inputs inputs).progress child
  obtain ⟨actualPlace, actualState, actualFitted, actualPlaceAccepted, actualFitting, actualValueAccepted, _⟩ := assignedValue_actual_prefix accepted
  cases Except.ok.inj (actualPlaceAccepted.symm.trans targetAccepted)
  have actualFitting : assignmentFit operator targetState place.type = (Except.ok actualFitted : Except Error State) := by cases operator <;> exact actualFitting
  have fitting : assignmentFit operator targetState place.type = (Except.ok fitted : Except Error State) := by cases operator <;> exact fitting
  cases Except.ok.inj (actualFitting.symm.trans fitting)
  cases Except.ok.inj (actualValueAccepted.symm.trans child)
  exact .refl childReady.2.1.solved

theorem assignedValue_place
      {fuel : Nat} {context : SourceInference.Context} {target value : Syntax.Expr}
      {operator : Syntax.ValueAssignOp} {initial final targetState : State}
      {assignment : AssignmentResolution} {inferred : InferredExpression} {place : PlaceResolution}
      (accepted : (CallIndex.assignedValue fuel context target operator value initial assignment inferred final).Accepted)

      (child : (CallIndex.place fuel context target initial place targetState).Accepted)
    (inputs : (CallIndex.assignedValue fuel context target operator value initial assignment inferred final).Inputs) :
    (CallIndex.place fuel context target initial place targetState).final.InferenceProgress (CallIndex.assignedValue fuel context target operator value initial assignment inferred final).final := by
  simp only [CallIndex.Accepted] at accepted child
  dsimp only [CallIndex.final] at ⊢
  obtain ⟨actualPlace, actualState, fitted, actualPlaceAccepted, fitting, valueAccepted, _⟩ := assignedValue_actual_prefix accepted
  cases Except.ok.inj (actualPlaceAccepted.symm.trans child)
  have fitting : assignmentFit operator targetState place.type = (Except.ok fitted : Except Error State) := by cases operator <;> exact fitting
  have placeProperties := inferPlaceFuel_inferenceProperties inputs.ready inputs.catalog.formation inputs.catalog.canonical child
  have fitProperties := assignmentFit_properties placeProperties.2.1 placeProperties.2.2 fitting
  have valueProperties := inferExprFuel_inferenceProperties fitProperties.2.1 inputs.catalog.formation inputs.catalog.canonical
    (by intro type member; cases member; exact fitProperties.2.2) valueAccepted
  exact fitProperties.1.trans valueProperties.1

theorem place_index_base
      {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Expr}
      {initial final : State} {result : PlaceResolution}
      {base key : Syntax.Expr} {brackets : Syntax.SourceSpan} {value : PlaceResolution} {childFinal : State}
      (accepted : (CallIndex.place (fuel + 1) context source initial result final).Accepted)
      (form : source.value = .index base brackets key)
      (child : (CallIndex.place fuel context base initial value childFinal).Accepted)
    (inputs : (CallIndex.place (fuel + 1) context source initial result final).Inputs) :
    (CallIndex.place fuel context base initial value childFinal).final.InferenceProgress (CallIndex.place (fuel + 1) context source initial result final).final := by
  simp only [CallIndex.Accepted] at accepted child
  dsimp only [CallIndex.final] at ⊢
  cases fitting : Detail.unify childFinal.fresh.2.fresh.2 value.type (.mapping childFinal.fresh.1 childFinal.fresh.2.fresh.1) with
  | error error => simp [inferPlaceFuel, form, child, fitting, bind, Except.bind] at accepted
  | ok fitted =>
    cases keyAccepted : inferExprFuel fuel context key (some (fitted.resolve childFinal.fresh.1)) fitted with
    | error error => simp [inferPlaceFuel, form, child, fitting, keyAccepted, bind, Except.bind] at accepted
    | ok keyResult =>
      have baseProperties := inferPlaceFuel_inferenceProperties inputs.ready inputs.catalog.formation inputs.catalog.canonical child
      have keyProperties := fresh_eq_inferenceProperties baseProperties.2.1 rfl
      have valueProperties := fresh_eq_inferenceProperties keyProperties.2.1 rfl
      have baseBelow := baseProperties.2.2.weaken (keyProperties.1.trans valueProperties.1).next_le
      have keyBelow := keyProperties.2.2.weaken valueProperties.1.next_le
      have mappingBelow := (Ty.variablesBelow_mapping_iff _ _ _).2 ⟨keyBelow, valueProperties.2.2⟩
      have mappingProgress := unify_inferenceProgress valueProperties.2.1.solved baseBelow mappingBelow fitting
      have keyStep := ChildStep.place_index_key accepted form child rfl rfl fitting keyAccepted
      have keyProgress := (keyStep.inputs inputs).progress keyAccepted
      exact keyProperties.1.trans (valueProperties.1.trans (mappingProgress.trans
        (keyProgress.1.trans (place_index_key accepted form child rfl rfl fitting keyAccepted inputs))))

theorem constructorApplication_arguments
      {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Expr} {id : ExpressionId}
      {instantiation : DataConstructorInstantiation} {sources : List Syntax.Expr} {expected : Option Ty}
      {initial fitted final childFinal : State} {value : InferredExpression} {values : List InferredExpression}
      (accepted : (CallIndex.constructorApplication fuel context source id instantiation sources expected initial value final).Accepted)
      (arity : sources.length = instantiation.payloadTypes.length)
      (fitting : (match expected with | none => pure initial | some type => unify initial instantiation.resultType type) = (Except.ok fitted : Except Error State))
      (child : (CallIndex.constructorArguments fuel context sources instantiation.payloadTypes fitted values childFinal).Accepted)
    (inputs : (CallIndex.constructorApplication fuel context source id instantiation sources expected initial value final).Inputs) :
    (CallIndex.constructorArguments fuel context sources instantiation.payloadTypes fitted values childFinal).final.InferenceProgress (CallIndex.constructorApplication fuel context source id instantiation sources expected initial value final).final := by
  simp only [CallIndex.Accepted] at accepted child
  dsimp only [CallIndex.final] at ⊢
  have fitting : (match expected with | none => Except.ok initial | some type => Detail.unify initial instantiation.resultType type) = .ok fitted := by cases expected <;> exact fitting
  have fitProperties : initial.InferenceProgress fitted ∧ fitted.InferenceReady := by
    cases expected with
    | none => cases Except.ok.inj fitting; exact ⟨.refl inputs.ready.solved, inputs.ready⟩
    | some type => exact ⟨unify_inferenceProgress inputs.ready.solved inputs.bounds.2.1 (inputs.bounds.2.2 _ (by simp)) fitting,
        unify_preserves_inferenceReady inputs.ready inputs.bounds.2.1 (inputs.bounds.2.2 _ (by simp)) fitting⟩
  have childProperties := inferConstructorArgumentsFuel_inferenceProperties fitProperties.2 inputs.catalog.formation inputs.catalog.canonical
    (fun type member => (inputs.bounds.1 type member).weaken fitProperties.1.next_le) child
  have recorded : recordExpressionWithExpected context source id (childFinal.resolve instantiation.resultType)
      (.constructor instantiation (values.map (·.id))) [] expected childFinal = .ok (value, final) := by
    unfold inferConstructorApplicationFuel at accepted
    cases expected with
    | none => cases Except.ok.inj fitting; simpa [arity, child, bind, Except.bind, pure, Pure.pure, Except.pure] using accepted
    | some type => simpa [arity, fitting, child, bind, Except.bind] using accepted
  exact (recordExpressionWithExpected_inferenceProperties childProperties.2.1
    (childProperties.2.1.solved.variablesBelow_apply (inputs.bounds.2.1.weaken (fitProperties.1.trans childProperties.1).next_le))
    (fun type member => (inputs.bounds.2.2 type member).weaken (fitProperties.1.trans childProperties.1).next_le) recorded).1

theorem matchCases_body
      {fuel : Nat} {context : SourceInference.Context} {scrutineeType expectedReturn : Ty}
      {saved : LexicalScope} {arm : Syntax.MatchCase} {arms : List Syntax.MatchCase}
      {initial patternState : State} {pattern : TypedMatchPattern} {result : MatchCasesResult}
      {body : BlockResult}
      (accepted : (CallIndex.matchCases (fuel + 1) context scrutineeType expectedReturn saved (arm :: arms) initial result).Accepted)
      (patternAccepted : inferMatchPatternFuel fuel context arm.value.pattern scrutineeType initial = .ok (pattern, patternState))
      (child : (CallIndex.statements fuel context arm.value.body.value expectedReturn patternState body).Accepted)
    (inputs : (CallIndex.matchCases (fuel + 1) context scrutineeType expectedReturn saved (arm :: arms) initial result).Inputs) :
    (CallIndex.statements fuel context arm.value.body.value expectedReturn patternState body).final.InferenceProgress (CallIndex.matchCases (fuel + 1) context scrutineeType expectedReturn saved (arm :: arms) initial result).final := by
  simp only [CallIndex.Accepted] at accepted child
  dsimp only [CallIndex.final] at ⊢
  have bodyProperties := ((ChildStep.matchCases_body accepted patternAccepted child).inputs inputs).progress child
  cases tailAccepted : inferMatchCasesFuel fuel context scrutineeType expectedReturn saved arms (body.state.restoreLexicalScope saved) with
  | error error => simp [inferMatchCasesFuel, patternAccepted, child, tailAccepted, bind, Except.bind] at accepted
  | ok tail =>
    have after := ((ChildStep.matchCases_tail accepted patternAccepted child tailAccepted).inputs inputs).progress tailAccepted
    have restored : body.state.InferenceProgress (body.state.restoreLexicalScope saved) := .of_inference_eq bodyProperties.2.1.solved rfl
    exact restored.trans (after.1.trans (matchCases_tail accepted patternAccepted child tailAccepted inputs))

end ActualSuffixProgress
end Solcore.SourceSemantics.SourceInferenceExecution
