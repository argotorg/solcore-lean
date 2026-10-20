import Solcore.Frontend.SourceInference.LocalGeneralizationBoundedHelpers

/-! Parameter, pattern, and builtin helper computations preserve the bounded
checker event invariant through their actual successful execution. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.Frontend.SourceInference.LocalGeneralizationBoundaries
open TypeSystem Detail
namespace Progress

theorem bindLambdaParameters {context : Context} {parameters : List Syntax.LambdaParameter}
    {index : Nat} {seen : List String} {state : State} {result : List TypedBinder × List Ty × State}
    (accepted : Detail.bindLambdaParameters context parameters index seen state = .ok result) :
    Progress state result.2.2 := by
  induction parameters generalizing index seen state result with
  | nil =>
      simp only [Detail.bindLambdaParameters, Except.ok.injEq] at accepted
      cases accepted
      exact .refl _
  | cons parameter rest ih =>
      cases form : parameter.value with
      | error => simp [Detail.bindLambdaParameters, form, bind, Except.bind] at accepted
      | inferred name =>
          simp only [Detail.bindLambdaParameters, form, bind, Except.bind] at accepted
          repeat' first | split at accepted
          all_goals try cases accepted
          all_goals try simp_all only [pure, Except.pure, Except.ok.injEq]
          all_goals try subst_vars
          all_goals have tail := ih (by assumption)
          all_goals exact (fresh state).trans ((allocateBinder _ _ _ _ _ _).trans tail)
      | typed marker name syntaxType =>
          simp only [Detail.bindLambdaParameters, form] at accepted
          cases resolved : resolveSourceType context syntaxType with
          | error error => simp [resolved, bind, Except.bind] at accepted
          | ok type =>
              simp only [resolved, bind, Except.bind] at accepted
              repeat' first | split at accepted
              all_goals try cases accepted
              all_goals try simp_all only [pure, Except.pure, Except.ok.injEq]
              all_goals try subst_vars
              all_goals have tail := ih (by assumption)
              all_goals exact (allocateBinder _ _ _ _ _ _).trans tail

theorem inferMatchPatternFuel {fuel : Nat} {context : Context} {pattern : Syntax.Pattern}
    {expected : Ty} {state : State} {result : TypedMatchPattern × State}
    (accepted : Detail.inferMatchPatternFuel fuel context pattern expected state = .ok result) :
    Progress state result.2 := by
  apply of_nodes_eq (inferMatchPatternFuel_occurrenceState_eq accepted).1
    (LocalReadEvents.Progress.inferMatchPatternFuel accepted)
    (LocalReadScopeProgress.Progress.inferMatchPatternFuel accepted)
  intro below
  unfold Detail.inferMatchPatternFuel at accepted
  cases flatRun : inferMatchPatternFlatFuel fuel context pattern expected [] state with
  | error error => simp [flatRun, bind, Except.bind] at accepted
  | ok inferred =>
      simp only [flatRun, bind, Except.bind] at accepted
      change Except.ok ({
        source := inferred.source
        type := inferred.state.resolve expected
        resolution := inferred.resolution
        requirements := inferred.requirements
      }, inferred.state) = Except.ok result at accepted
      cases accepted
      exact inferMatchPatternFlatFuel_preserves_localBindersBelowNextLocal
        fuel context pattern expected [] state inferred below flatRun

private theorem builtinArguments {arguments : List InferredExpression} {parameters : List Ty}
    {state next : State}
    (accepted : unifyBuiltinFunctionArgumentsEqual arguments parameters state = .ok next) :
    Progress state next := by
  induction arguments generalizing parameters state next with
  | nil =>
      simp only [unifyBuiltinFunctionArgumentsEqual, Except.ok.injEq] at accepted
      cases accepted
      exact .refl _
  | cons argument arguments ih =>
      cases parameters with
      | nil =>
          simp only [unifyBuiltinFunctionArgumentsEqual, Except.ok.injEq] at accepted
          cases accepted
          exact .refl _
      | cons parameter parameters =>
          simp only [unifyBuiltinFunctionArgumentsEqual] at accepted
          cases unified : Detail.unify state argument.type parameter with
          | error error => simp [unified, bind, Except.bind] at accepted
          | ok ready =>
              simp only [unified, bind, Except.bind] at accepted
              exact (unify unified).trans (ih accepted)

private theorem builtinCall_binders {source callee : Syntax.Expr} {name : String}
    {function : BuiltinFunctionId} {arguments : List InferredExpression}
    {call : ExpressionId} {expected : Option Ty} {state : State}
    {result : InferredExpression × State}
    (accepted : Detail.recordBuiltinFunctionCall source callee name function arguments call expected state = .ok result)
    (below : state.LocalBindersBelowNextLocal) : result.2.LocalBindersBelowNextLocal := by
  unfold Detail.recordBuiltinFunctionCall at accepted
  simp_all [bind, Except.bind]
  repeat' first | split at accepted
  all_goals try cases accepted
  all_goals try simp_all only [pure, Except.pure, Except.ok.injEq]
  all_goals try subst_vars
  all_goals have argumentsProgress := builtinArguments (by assumption)
  all_goals try have unifiedProgress := unify (by assumption)
  all_goals first
    | exact argumentsProgress.binders below
    | exact unifiedProgress.binders (argumentsProgress.binders below)

theorem recordBuiltinFunctionCall {source callee : Syntax.Expr} {name : String}
    {function : BuiltinFunctionId} {arguments : List InferredExpression}
    {call : ExpressionId} {expected : Option Ty} {state : State}
    {result : InferredExpression × State}
    (accepted : Detail.recordBuiltinFunctionCall source callee name function arguments call expected state = .ok result) :
    Progress state result.2 := by
  apply of_retained ?_ (LocalReadEvents.Progress.recordBuiltinFunctionCall accepted)
    (LocalReadScopeProgress.Progress.recordBuiltinFunctionCall accepted) (builtinCall_binders accepted)
  obtain ⟨calleeId, nodes⟩ := Detail.recordBuiltinFunctionCall_success_nodes accepted
  rw [nodes]
  intro statement present
  rcases List.mem_append.mp present with old | fresh
  · exact ⟨statement, old, rfl, rfl⟩
  · simp at fresh

end Progress
end Solcore.Frontend.SourceInference.LocalGeneralizationBoundaries
