import Solcore.SourceSemantics.SourceInferenceActualCallInputTraversal
import Solcore.Frontend.SourceInference.LocalBinderScopeProgress

/-! Stable local identities stay below the actual allocator in every completed
prefix. This is independent of the inference metavariable allocator. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
namespace Solcore.SourceSemantics.SourceInferenceExecution.ActualLocalAllocator
open Frontend SourceInference TypeSystem Detail

private theorem pure_ok {epsilon alpha : Type} (value result : alpha) :
    ((pure value : Except epsilon alpha) = .ok result) ↔ value = result :=
  by change (Except.ok value = Except.ok result) ↔ value = result; simp
private theorem throw_ne_ok {epsilon alpha : Type} (error : epsilon) (value : alpha) :
    (throw error : Except epsilon alpha) ≠ .ok value := by intro impossible; cases impossible

private theorem expression_binders {fuel : Nat} {context : SourceInference.Context}
    {source : Syntax.Expr} {expected : Option Ty} {initial : State}
    {result : InferredExpression × State}
    (accepted : inferExprFuel fuel context source expected initial = .ok result) :
    result.2.localBinders = initial.localBinders :=
  congrArg LexicalScope.binders (inferExprFuel_success_lexicalScope_eq accepted)
private theorem expressions_binders {fuel : Nat} {context : SourceInference.Context}
    {source : List Syntax.Expr} {initial : State} {result : List InferredExpression × State}
    (accepted : inferExprsFuel fuel context source initial = .ok result) :
    result.2.localBinders = initial.localBinders :=
  congrArg LexicalScope.binders (inferExprsFuel_success_lexicalScope_eq accepted)
private theorem place_binders {fuel : Nat} {context : SourceInference.Context}
    {source : Syntax.Expr} {initial : State} {result : PlaceResolution × State}
    (accepted : inferPlaceFuel fuel context source initial = .ok result) :
    result.2.localBinders = initial.localBinders :=
  congrArg LexicalScope.binders (inferPlaceFuel_success_lexicalScope_eq accepted)
private theorem assigned_binders {fuel : Nat} {context : SourceInference.Context}
    {target source : Syntax.Expr} {operator : Syntax.ValueAssignOp} {initial final : State}
    {assignment : AssignmentResolution} {value : InferredExpression}
    (accepted : inferAssignedValueFuel fuel context target operator source initial = .ok (assignment,value,final)) :
    final.localBinders = initial.localBinders :=
  congrArg LexicalScope.binders (inferAssignedValueFuel_success_lexicalScope_eq accepted)
private theorem unified_binders {initial final : State} {left right : Ty}
    (accepted : unify initial left right = .ok final) : final.localBinders = initial.localBinders :=
  congrArg LexicalScope.binders (unify_preserves_lexicalScope accepted)
private theorem cases_binders {fuel : Nat} {context : SourceInference.Context} {scrutinee expected : Ty}
    {arms : List Syntax.MatchCase} {initial : State} {result : MatchCasesResult}
    (accepted : inferMatchCasesFuel fuel context scrutinee expected initial.lexicalScope arms initial = .ok result) :
    result.state.localBinders = initial.localBinders :=
  congrArg LexicalScope.binders (inferMatchCasesFuel_success_lexicalScope_eq rfl accepted)

private theorem statement_binders (state : State) :
    state.allocateStatementId.2.localBinders = state.localBinders := rfl
private theorem statement_next (state : State) :
    state.allocateStatementId.2.nextLocal = state.nextLocal := rfl
private theorem expressionId_binders (state : State) :
    state.allocateExpressionId.2.localBinders = state.localBinders := rfl
private theorem expressionId_next (state : State) :
    state.allocateExpressionId.2.nextLocal = state.nextLocal := rfl

/-- Only a direct declaration adds a binder to the returned statement scope.
Nested bodies restore the genuine saved scope. -/
theorem statement {fuel : Nat} {context : SourceInference.Context}
    {source : Syntax.Statement} {expected : Ty} {initial : State} {result : StatementResult}
    (below : initial.LocalBindersBelowNextLocal)
    (accepted : inferStatementFuel fuel context source expected initial = .ok result) :
    result.state.LocalBindersBelowNextLocal := by
  have next := inferStatementFuel_nextLocal_le accepted
  cases fuel with
  | zero => simp [inferStatementFuel] at accepted
  | succ fuel =>
    unfold inferStatementFuel at accepted
    cases form : source.value <;> simp only [form, bind, Except.bind] at accepted
    all_goals repeat' first | split at accepted
    all_goals try cases accepted
    all_goals try simp_all only [pure_ok, throw_ne_ok]
    all_goals try subst_vars
    all_goals try have exprBinders := expression_binders (by assumption)
    all_goals try have exprNext := inferExprFuel_nextLocal_le (by assumption)
    all_goals try have exprsBinders := expressions_binders (by assumption)
    all_goals try have exprsNext := inferExprsFuel_nextLocal_le (by assumption)
    all_goals try have placeBinders := place_binders (by assumption)
    all_goals try have assignedBinders := assigned_binders (by assumption)
    all_goals try have unifiedBinders := unified_binders (by assumption)
    all_goals try have casesBinders := cases_binders (by assumption)
    all_goals simp_all only [State.recordNode, State.restoreLexicalScope, State.lexicalScope,
      State.allocateBinder, State.allocateHiddenLocal, statement_binders, statement_next,
      expressionId_binders, expressionId_next]
    all_goals intro binder member
    all_goals dsimp only at *
    all_goals try exact Nat.lt_of_lt_of_le (below binder member) next
    all_goals try (rcases List.mem_cons.mp member with current | old
                   · subst binder; exact Nat.lt_succ_self _
                   · have prior := below binder old; omega)

/-- The source-ordered fold applies the same statement result bound. -/
theorem statements {fuel : Nat} {context : SourceInference.Context}
    {sources : List Syntax.Statement} {expected : Ty} {initial : State} {result : BlockResult}
    (below : initial.LocalBindersBelowNextLocal)
    (accepted : inferStatementsFuel fuel context sources expected initial = .ok result) :
    result.state.LocalBindersBelowNextLocal := by
  induction fuel generalizing sources initial result with
  | zero => simp [inferStatementsFuel] at accepted
  | succ fuel ih =>
    cases sources with
    | nil =>
      simp only [inferStatementsFuel, Except.ok.injEq] at accepted
      cases accepted
      exact below
    | cons head tail =>
      cases first : inferStatementFuel fuel context head expected initial with
      | error error => simp [inferStatementsFuel, first, bind, Except.bind] at accepted
      | ok firstResult =>
        have firstBelow := statement below first
        cases tail with
        | nil =>
          simp only [inferStatementsFuel, first, bind, Except.bind, pure_ok] at accepted
          cases accepted
          exact firstBelow
        | cons next rest =>
          cases remainder : inferStatementsFuel fuel context (next :: rest) expected firstResult.state with
          | error error => simp [inferStatementsFuel, first, remainder, bind, Except.bind] at accepted
          | ok tailResult =>
            simp only [inferStatementsFuel, first, remainder, bind, Except.bind, pure_ok] at accepted
            cases accepted
            exact ih (result := tailResult) firstBelow remainder

theorem parameters {context : SourceInference.Context} {sources : List Syntax.LambdaParameter}
    {index : Nat} {seen : List String} {initial : State} {result : List TypedBinder × List Ty × State}
    (below : initial.LocalBindersBelowNextLocal)
    (accepted : bindLambdaParameters context sources index seen initial = .ok result) :
    result.2.2.LocalBindersBelowNextLocal := by
  induction sources generalizing index seen initial result with
  | nil =>
    simp only [bindLambdaParameters, Except.ok.injEq] at accepted
    cases accepted
    exact below
  | cons head tail ih =>
    unfold bindLambdaParameters at accepted
    cases form : head.value <;> simp only [form, bind, Except.bind] at accepted
    all_goals repeat' first | split at accepted
    all_goals try cases accepted
    all_goals try simp_all only [pure_ok, throw_ne_ok]
    all_goals try subst_vars
    all_goals apply ih (accepted := by assumption)
    all_goals apply State.allocateBinder_preserves_localBindersBelowNextLocal
    all_goals first | exact below | exact State.fresh_preserves_localBindersBelowNextLocal initial below

theorem pattern {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Pattern}
    {expected : Ty} {initial : State} {result : TypedMatchPattern × State}
    (below : initial.LocalBindersBelowNextLocal)
    (accepted : inferMatchPatternFuel fuel context source expected initial = .ok result) :
    result.2.LocalBindersBelowNextLocal := by
  unfold inferMatchPatternFuel at accepted
  cases actual : inferMatchPatternFlatFuel fuel context source expected [] initial with
  | error error => simp [actual, bind, Except.bind] at accepted
  | ok inferred =>
    simp only [actual, bind, Except.bind, pure_ok] at accepted
    cases accepted
    exact inferMatchPatternFlatFuel_preserves_localBindersBelowNextLocal
      fuel context source expected [] initial inferred below actual

theorem lambda_prefix {context : SourceInference.Context} {expected : Option Ty}
    {annotation : Option Syntax.TypeExpr} {types : List Ty} {initial final : State} {result : Ty}
    (below : initial.LocalBindersBelowNextLocal)
    (prefixFacts : LambdaPrefixFacts context expected annotation types initial result final) :
    final.LocalBindersBelowNextLocal := by
  cases prefixFacts with
  | noExpectedPartsAnnotated => exact below
  | noExpectedPartsFresh _ _ allocated =>
    have same : final = initial.fresh.2 := (congrArg Prod.snd allocated).symm
    rw [same]
    exact State.fresh_preserves_localBindersBelowNextLocal _ below
  | expectedPartsAnnotated _ unified => exact unify_preserves_localBindersBelowNextLocal below unified
  | expectedPartsInferred _ unified => exact unify_preserves_localBindersBelowNextLocal below unified

theorem match_scrutinee {fuel : Nat} {context : SourceInference.Context}
    {span : Syntax.SourceSpan} {sources : List Syntax.Expr} {initial : State}
    {result : InferredExpression × State} (below : initial.LocalBindersBelowNextLocal)
    (accepted : matchScrutinee fuel context span sources initial = .ok result) :
    result.2.LocalBindersBelowNextLocal := by
  unfold matchScrutinee at accepted
  split at accepted
  · exact inferExprFuel_preserves_localBindersBelowNextLocal below accepted
  · cases actual : inferExprsFuel fuel context sources initial with
    | error error => simp [actual, bind, Except.bind] at accepted
    | ok inferred =>
      simp only [actual, bind, Except.bind, pure_ok] at accepted
      cases accepted
      apply State.recordNode_preserves_localBindersBelowNextLocal
      apply State.allocateExpressionId_preserves_localBindersBelowNextLocal
      exact inferExprsFuel_preserves_localBindersBelowNextLocal below actual

end Solcore.SourceSemantics.SourceInferenceExecution.ActualLocalAllocator
