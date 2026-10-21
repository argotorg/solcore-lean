import Solcore.SourceSemantics.SourceInferenceActualCallInputTraversal
import Solcore.SourceSemantics.SourceInferenceGeneralizationLifetimePlace
import Solcore.SourceSemantics.SourceInferenceGeneralizationLifetimeAssignedValue
import Solcore.SourceSemantics.SourceInferenceGeneralizationLifetimeMatchCases

/-! Place, assigned-value and arm calls keep the exact child result and suffix. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceExecution
open Frontend SourceInference TypeSystem Detail SourceInferenceSoundness.ProtectedVariables
variable {whole : TypedSource} {finalSubstitution : Substitution}
    {binder : TypedBinder} {initializer : ExpressionId}
    {event : RetainedGeneralization whole finalSubstitution binder initializer}

private theorem placeBase
    {fuel : Nat} {context : SourceInference.Context} {source base key : Syntax.Expr}
    {brackets : Syntax.SourceSpan} {initial baseState : State} {baseValue : PlaceResolution}
    {result : PlaceResolution × State}
    (inputs : (CallIndex.place (fuel + 1) context source initial result.1 result.2).Inputs)
    (form : source.value = .index base brackets key)
    (baseAccepted : inferPlaceFuel fuel context base initial = .ok (baseValue, baseState))
    (accepted : inferPlaceFuel (fuel + 1) context source initial = .ok result)
    (lifetime : GeneralizationLifetime event initial.inference.next baseState [baseValue.type]) :
    GeneralizationLifetime event initial.inference.next result.2 [result.1.type] := by
  cases fitting : Detail.unify baseState.fresh.2.fresh.2 baseValue.type
      (.mapping baseState.fresh.1 baseState.fresh.2.fresh.1) with
  | error error => simp [inferPlaceFuel, form, baseAccepted, fitting, bind, Except.bind] at accepted
  | ok fitted =>
    cases keyAccepted : inferExprFuel fuel context key (some (fitted.resolve baseState.fresh.1)) fitted with
    | error error => simp [inferPlaceFuel, form, baseAccepted, fitting, keyAccepted, bind, Except.bind] at accepted
    | ok keyResult => exact lifetime.place_index_base inputs.ready inputs.wellFormed inputs.catalog form baseAccepted rfl rfl fitting keyAccepted accepted

private theorem matchBody
    {fuel : Nat} {context : SourceInference.Context} {scrutinee expected : Ty} {saved : LexicalScope}
    {arm : Syntax.MatchCase} {rest : List Syntax.MatchCase} {initial patternState : State}
    {pattern : TypedMatchPattern} {body : BlockResult} {result : MatchCasesResult}
    (inputs : (CallIndex.matchCases (fuel + 1) context scrutinee expected saved (arm :: rest) initial result).Inputs)
    (patternAccepted : inferMatchPatternFuel fuel context arm.value.pattern scrutinee initial = .ok (pattern, patternState))
    (bodyAccepted : inferStatementsFuel fuel context arm.value.body.value expected patternState = .ok body)
    (accepted : inferMatchCasesFuel (fuel + 1) context scrutinee expected saved (arm :: rest) initial = .ok result)
    (lifetime : GeneralizationLifetime event patternState.inference.next body.state [body.type]) :
    GeneralizationLifetime event initial.inference.next result.state [] := by
  cases tailAccepted : inferMatchCasesFuel fuel context scrutinee expected saved rest (body.state.restoreLexicalScope saved) with
  | error error => simp [inferMatchCasesFuel, patternAccepted, bodyAccepted, tailAccepted, bind, Except.bind] at accepted
  | ok tail => exact lifetime.matchCases_body inputs.ready inputs.wellFormed inputs.catalog inputs.bounds.1 inputs.bounds.2.1 inputs.bounds.2.2 patternAccepted bodyAccepted tailAccepted accepted

namespace ChildStep

theorem lifetime_place
    {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Expr}
    {initial final : State} {value : PlaceResolution} {child : CallIndex}
    (inputs : (CallIndex.place fuel context source initial value final).Inputs)
    (step : ChildStep (.place fuel context source initial value final) child)
    (lifetime : GeneralizationLifetime event child.initial.inference.next child.final child.outputTypes) :
    GeneralizationLifetime event initial.inference.next final [value.type] := by
  cases step with
  | place_group accepted form childAccepted => exact lifetime.place_group form childAccepted accepted
  | place_index_base accepted form childAccepted => exact placeBase inputs form childAccepted accepted lifetime
  | place_index_key accepted form baseAccepted keyFresh valueFresh fitting childAccepted =>
      exact lifetime.place_index_key inputs.ready inputs.catalog form baseAccepted keyFresh valueFresh fitting childAccepted accepted

theorem lifetime_assignedValue
    {fuel : Nat} {context : SourceInference.Context} {target value : Syntax.Expr} {operator : Syntax.ValueAssignOp}
    {initial final : State} {assignment : AssignmentResolution} {inferred : InferredExpression} {child : CallIndex}
    (inputs : (CallIndex.assignedValue fuel context target operator value initial assignment inferred final).Inputs)
    (step : ChildStep (.assignedValue fuel context target operator value initial assignment inferred final) child)
    (lifetime : GeneralizationLifetime event child.initial.inference.next child.final child.outputTypes) :
    GeneralizationLifetime event initial.inference.next final [assignment.target.type, inferred.type] := by
  cases step with
  | assignedValue_place accepted childAccepted =>
      exact lifetime.assignedValue_place inputs.ready inputs.wellFormed inputs.catalog childAccepted accepted
  | assignedValue_value accepted targetAccepted fitting childAccepted =>
      apply GeneralizationLifetime.assignedValue_value (operator := operator) inputs.ready inputs.catalog targetAccepted ?_ childAccepted accepted lifetime
      cases operator <;> exact fitting

theorem lifetime_matchCases
    {fuel : Nat} {context : SourceInference.Context} {scrutinee expected : Ty} {saved : LexicalScope}
    {sources : List Syntax.MatchCase} {initial : State} {result : MatchCasesResult} {child : CallIndex}
    (inputs : (CallIndex.matchCases fuel context scrutinee expected saved sources initial result).Inputs)
    (step : ChildStep (.matchCases fuel context scrutinee expected saved sources initial result) child)
    (lifetime : GeneralizationLifetime event child.initial.inference.next child.final child.outputTypes) :
    GeneralizationLifetime event initial.inference.next result.state [] := by
  cases step with
  | matchCases_body accepted patternAccepted bodyAccepted =>
      exact matchBody inputs patternAccepted bodyAccepted accepted lifetime
  | matchCases_tail accepted patternAccepted bodyAccepted tailAccepted =>
      exact lifetime.matchCases_tail inputs.ready inputs.catalog inputs.bounds.1 inputs.bounds.2.1 inputs.bounds.2.2 patternAccepted bodyAccepted tailAccepted accepted

end ChildStep
end Solcore.SourceSemantics.SourceInferenceExecution
