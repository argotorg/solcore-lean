import Solcore.SourceSemantics.SourceInferenceActualTerminalBinderRetention
import Solcore.SourceSemantics.SourceInferenceAssignedValueActualPrefix
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceExecution
open Frontend SourceInference TypeSystem Detail LocalGeneralizationEvents
namespace ActualBinderRetention

theorem assignedValue_value
      {fuel : Nat} {context : SourceInference.Context} {target value : Syntax.Expr}
      {operator : Syntax.ValueAssignOp} {initial final targetState : State}
      {assignment : AssignmentResolution} {inferred : InferredExpression} {place : PlaceResolution}
      {fitted childFinal : State} {childValue : InferredExpression}
      (accepted : (CallIndex.assignedValue fuel context target operator value initial assignment inferred final).Accepted)
      (targetAccepted : inferPlaceFuel fuel context target initial = .ok (place, targetState))
      (fitting : (match operator with | .equal => pure targetState | _ => unify targetState place.type .word) = (Except.ok fitted : Except Error State))
      (child : (CallIndex.expression fuel context value (some (assignmentExpected operator fitted place.type)) fitted childValue childFinal).Accepted)  :
    BindersRetained (CallIndex.expression fuel context value (some (assignmentExpected operator fitted place.type)) fitted childValue childFinal).final.nodes (CallIndex.assignedValue fuel context target operator value initial assignment inferred final).final.nodes := by
  simp only [CallIndex.Accepted] at accepted child
  dsimp only [CallIndex.final] at ⊢
  obtain ⟨actualPlace, actualState, actualFitted, actualPlaceAccepted, actualFitting, actualValueAccepted, _⟩ := assignedValue_actual_prefix accepted
  cases Except.ok.inj (actualPlaceAccepted.symm.trans targetAccepted)
  have actualFitting : assignmentFit operator targetState place.type = (Except.ok actualFitted : Except Error State) := by cases operator <;> exact actualFitting
  have fitting : assignmentFit operator targetState place.type = (Except.ok fitted : Except Error State) := by cases operator <;> exact fitting
  cases Except.ok.inj (actualFitting.symm.trans fitting)
  cases Except.ok.inj (actualValueAccepted.symm.trans child)
  exact .refl _


theorem assignedValue_place
      {fuel : Nat} {context : SourceInference.Context} {target value : Syntax.Expr}
      {operator : Syntax.ValueAssignOp} {initial final targetState : State}
      {assignment : AssignmentResolution} {inferred : InferredExpression} {place : PlaceResolution}
      (accepted : (CallIndex.assignedValue fuel context target operator value initial assignment inferred final).Accepted)

      (child : (CallIndex.place fuel context target initial place targetState).Accepted)  :
    BindersRetained (CallIndex.place fuel context target initial place targetState).final.nodes (CallIndex.assignedValue fuel context target operator value initial assignment inferred final).final.nodes := by
  simp only [CallIndex.Accepted] at accepted child
  dsimp only [CallIndex.final] at ⊢
  obtain ⟨actualPlace, actualState, fitted, actualPlaceAccepted, fitting, valueAccepted, _⟩ := assignedValue_actual_prefix accepted
  cases Except.ok.inj (actualPlaceAccepted.symm.trans child)
  have fitRetained : BindersRetained targetState.nodes fitted.nodes := by
    cases operator <;> simp only [pure, Pure.pure, Except.pure] at fitting
    all_goals first
    | (cases Except.ok.inj fitting; exact .refl _)
    | exact unify_retained fitting
  exact fitRetained.trans (inferExprFuel_origins_progress valueAccepted).retained


theorem place_index_base
      {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Expr}
      {initial final : State} {result : PlaceResolution}
      {base key : Syntax.Expr} {brackets : Syntax.SourceSpan} {value : PlaceResolution} {childFinal : State}
      (accepted : (CallIndex.place (fuel + 1) context source initial result final).Accepted)
      (form : source.value = .index base brackets key)
      (child : (CallIndex.place fuel context base initial value childFinal).Accepted)  :
    BindersRetained (CallIndex.place fuel context base initial value childFinal).final.nodes (CallIndex.place (fuel + 1) context source initial result final).final.nodes := by
  simp only [CallIndex.Accepted] at accepted child
  dsimp only [CallIndex.final] at ⊢
  cases fitting : Detail.unify childFinal.fresh.2.fresh.2 value.type (.mapping childFinal.fresh.1 childFinal.fresh.2.fresh.1) with
  | error error => simp [inferPlaceFuel, form, child, fitting, bind, Except.bind] at accepted
  | ok fitted =>
    cases keyAccepted : inferExprFuel fuel context key (some (fitted.resolve childFinal.fresh.1)) fitted with
    | error error => simp [inferPlaceFuel, form, child, fitting, keyAccepted, bind, Except.bind] at accepted
    | ok keyResult =>
      exact (unify_retained fitting).trans ((inferExprFuel_origins_progress keyAccepted).retained.trans
        (place_index_key accepted form child rfl rfl fitting keyAccepted))


theorem constructorApplication_arguments
      {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Expr} {id : ExpressionId}
      {instantiation : DataConstructorInstantiation} {sources : List Syntax.Expr} {expected : Option Ty}
      {initial fitted final childFinal : State} {value : InferredExpression} {values : List InferredExpression}
      (accepted : (CallIndex.constructorApplication fuel context source id instantiation sources expected initial value final).Accepted)
      (arity : sources.length = instantiation.payloadTypes.length)
      (fitting : (match expected with | none => pure initial | some type => unify initial instantiation.resultType type) = (Except.ok fitted : Except Error State))
      (child : (CallIndex.constructorArguments fuel context sources instantiation.payloadTypes fitted values childFinal).Accepted)  :
    BindersRetained (CallIndex.constructorArguments fuel context sources instantiation.payloadTypes fitted values childFinal).final.nodes (CallIndex.constructorApplication fuel context source id instantiation sources expected initial value final).final.nodes := by
  simp only [CallIndex.Accepted] at accepted child
  dsimp only [CallIndex.final] at ⊢
  have fitting : (match expected with | none => Except.ok initial | some type => Detail.unify initial instantiation.resultType type) = .ok fitted := by cases expected <;> exact fitting
  have recorded : recordExpressionWithExpected context source id (childFinal.resolve instantiation.resultType)
      (.constructor instantiation (values.map (·.id))) [] expected childFinal = .ok (value, final) := by
    unfold inferConstructorApplicationFuel at accepted
    cases expected with
    | none => cases Except.ok.inj fitting; simpa [arity, child, bind, Except.bind, pure, Pure.pure, Except.pure] using accepted
    | some type => simpa [arity, fitting, child, bind, Except.bind] using accepted
  exact BindersRetained.recordExpressionWithExpected recorded


theorem matchCases_body
      {fuel : Nat} {context : SourceInference.Context} {scrutineeType expectedReturn : Ty}
      {saved : LexicalScope} {arm : Syntax.MatchCase} {arms : List Syntax.MatchCase}
      {initial patternState : State} {pattern : TypedMatchPattern} {result : MatchCasesResult}
      {body : BlockResult}
      (accepted : (CallIndex.matchCases (fuel + 1) context scrutineeType expectedReturn saved (arm :: arms) initial result).Accepted)
      (patternAccepted : inferMatchPatternFuel fuel context arm.value.pattern scrutineeType initial = .ok (pattern, patternState))
      (child : (CallIndex.statements fuel context arm.value.body.value expectedReturn patternState body).Accepted)  :
    BindersRetained (CallIndex.statements fuel context arm.value.body.value expectedReturn patternState body).final.nodes (CallIndex.matchCases (fuel + 1) context scrutineeType expectedReturn saved (arm :: arms) initial result).final.nodes := by
  simp only [CallIndex.Accepted] at accepted child
  dsimp only [CallIndex.final] at ⊢
  cases tailAccepted : inferMatchCasesFuel fuel context scrutineeType expectedReturn saved arms (body.state.restoreLexicalScope saved) with
  | error error => simp [inferMatchCasesFuel, patternAccepted, child, tailAccepted, bind, Except.bind] at accepted
  | ok tail =>
    exact (inferMatchCasesFuel_origins_progress tailAccepted).retained.trans
      (matchCases_tail accepted patternAccepted child tailAccepted)

end ActualBinderRetention
end Solcore.SourceSemantics.SourceInferenceExecution
