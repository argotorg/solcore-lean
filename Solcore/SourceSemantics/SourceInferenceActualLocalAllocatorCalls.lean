import Solcore.SourceSemantics.SourceInferenceActualLocalAllocatorPrefixes

/-! Local-allocation bounds follow actual recursive inference calls. Every
saved scope is the one retained by the parent call, rather than an arbitrary
replacement of the binder stack. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
namespace Solcore.SourceSemantics.SourceInferenceExecution.ActualLocalAllocator
open Frontend SourceInference TypeSystem Detail

private theorem expressionAllocation {initial allocated : State} {id : ExpressionId}
    (allocation : initial.allocateExpressionId = (id, allocated))
    (below : initial.LocalBindersBelowNextLocal) : allocated.LocalBindersBelowNextLocal := by
  have same : allocated = initial.allocateExpressionId.2 := (congrArg Prod.snd allocation).symm
  rw [same]
  exact State.allocateExpressionId_preserves_localBindersBelowNextLocal initial below
private theorem statementAllocation {initial allocated : State} {id : StatementId}
    (allocation : initial.allocateStatementId = (id, allocated))
    (below : initial.LocalBindersBelowNextLocal) : allocated.LocalBindersBelowNextLocal := by
  have same : allocated = initial.allocateStatementId.2 := (congrArg Prod.snd allocation).symm
  rw [same]
  exact State.allocateStatementId_preserves_localBindersBelowNextLocal initial below
private theorem freshAllocation {initial allocated : State} {type : Ty}
    (allocation : initial.fresh = (type, allocated))
    (below : initial.LocalBindersBelowNextLocal) : allocated.LocalBindersBelowNextLocal := by
  have same : allocated = initial.fresh.2 := (congrArg Prod.snd allocation).symm
  rw [same]
  exact State.fresh_preserves_localBindersBelowNextLocal initial below
private theorem hiddenAllocation {initial allocated : State} {id : Resolved.LocalId}
    (allocation : initial.allocateHiddenLocal = (id, allocated))
    (below : initial.LocalBindersBelowNextLocal) : allocated.LocalBindersBelowNextLocal := by
  have same : allocated = initial.allocateHiddenLocal.2 := (congrArg Prod.snd allocation).symm
  rw [same]
  exact State.allocateHiddenLocal_preserves_localBindersBelowNextLocal initial below
private theorem constructorAllocation {initial allocated : State} {value : DataConstructorInstantiation}
    {dataType : ProgramDataSignature} {constructor : ProgramDataConstructorSignature}
    (allocation : freshDataConstructorInstantiation dataType constructor initial = (value, allocated))
    (below : initial.LocalBindersBelowNextLocal) : allocated.LocalBindersBelowNextLocal := by
  have same : allocated = (freshDataConstructorInstantiation dataType constructor initial).2 :=
    (congrArg Prod.snd allocation).symm
  rw [same]
  exact freshDataConstructorInstantiation_preserves_localBindersBelowNextLocal dataType constructor initial below
private theorem optionalFit {initial fitted : State} {expected : Option Ty} {result : Ty}
    (accepted : (match expected with | none => pure initial | some type => unify initial result type) =
      (Except.ok fitted : Except Error State))
    (below : initial.LocalBindersBelowNextLocal) : fitted.LocalBindersBelowNextLocal := by
  cases expected with
  | none => cases Except.ok.inj accepted; exact below
  | some type => exact unify_preserves_localBindersBelowNextLocal below accepted
private theorem assignedFit {initial fitted : State} {operator : Syntax.ValueAssignOp} {target : Ty}
    (accepted : (match operator with | .equal => pure initial | _ => unify initial target .word) =
      (Except.ok fitted : Except Error State))
    (below : initial.LocalBindersBelowNextLocal) : fitted.LocalBindersBelowNextLocal := by
  cases operator
  · cases Except.ok.inj accepted; exact below
  all_goals exact unify_preserves_localBindersBelowNextLocal below accepted

private theorem expressionRun {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Expr}
    {expected : Option Ty} {initial : State} {value : InferredExpression} {final : State}
    (accepted : inferExprFuel fuel context source expected initial = .ok (value, final))
    (below : initial.LocalBindersBelowNextLocal) : final.LocalBindersBelowNextLocal :=
  inferExprFuel_preserves_localBindersBelowNextLocal below accepted
private theorem expressionsRun {fuel : Nat} {context : SourceInference.Context} {sources : List Syntax.Expr}
    {initial : State} {values : List InferredExpression} {final : State}
    (accepted : inferExprsFuel fuel context sources initial = .ok (values, final))
    (below : initial.LocalBindersBelowNextLocal) : final.LocalBindersBelowNextLocal :=
  inferExprsFuel_preserves_localBindersBelowNextLocal below accepted
private theorem placeRun {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Expr}
    {initial : State} {place : PlaceResolution} {final : State}
    (accepted : inferPlaceFuel fuel context source initial = .ok (place, final))
    (below : initial.LocalBindersBelowNextLocal) : final.LocalBindersBelowNextLocal :=
  inferPlaceFuel_preserves_localBindersBelowNextLocal below accepted
private theorem itemsRun {fuel : Nat} {context : SourceInference.Context} {sources : List Syntax.ForItem}
    {initial : State} {result : InferredForItems}
    (accepted : inferForItemsFuel fuel context sources initial = .ok result)
    (below : initial.LocalBindersBelowNextLocal) : result.state.LocalBindersBelowNextLocal :=
  inferForItemsFuel_preserves_localBindersBelowNextLocal below accepted
private theorem itemRun {fuel : Nat} {context : SourceInference.Context} {source : Syntax.ForItem}
    {initial : State} {item : ForItemForm} {final : State}
    (accepted : inferForItemFuel fuel context source initial = .ok (item, final))
    (below : initial.LocalBindersBelowNextLocal) : final.LocalBindersBelowNextLocal :=
  inferForItemFuel_preserves_localBindersBelowNextLocal below accepted
private theorem unifyRun {initial final : State} {left right : Ty}
    (accepted : unify initial left right = .ok final)
    (below : initial.LocalBindersBelowNextLocal) : final.LocalBindersBelowNextLocal :=
  unify_preserves_localBindersBelowNextLocal below accepted
private theorem statementsRun {fuel : Nat} {context : SourceInference.Context} {sources : List Syntax.Statement}
    {expected : Ty} {initial : State} {result : BlockResult}
    (accepted : inferStatementsFuel fuel context sources expected initial = .ok result)
    (below : initial.LocalBindersBelowNextLocal) : result.state.LocalBindersBelowNextLocal :=
  statements below accepted
private theorem statementRun {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Statement}
    {expected : Ty} {initial : State} {result : StatementResult}
    (accepted : inferStatementFuel fuel context source expected initial = .ok result)
    (below : initial.LocalBindersBelowNextLocal) : result.state.LocalBindersBelowNextLocal :=
  statement below accepted
private theorem parametersRun {context : SourceInference.Context} {sources : List Syntax.LambdaParameter}
    {index : Nat} {seen : List String} {initial : State} {bound : List TypedBinder} {types : List Ty} {final : State}
    (accepted : bindLambdaParameters context sources index seen initial = .ok (bound, types, final))
    (below : initial.LocalBindersBelowNextLocal) : final.LocalBindersBelowNextLocal :=
  parameters below accepted
private theorem patternRun {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Pattern}
    {expected : Ty} {initial : State} {checkedPattern : TypedMatchPattern} {final : State}
    (accepted : inferMatchPatternFuel fuel context source expected initial = .ok (checkedPattern, final))
    (below : initial.LocalBindersBelowNextLocal) : final.LocalBindersBelowNextLocal :=
  pattern below accepted
private theorem lambdaPrefixRun {context : SourceInference.Context} {expected : Option Ty}
    {annotation : Option Syntax.TypeExpr} {types : List Ty} {initial final : State} {result : Ty}
    (prefixFacts : LambdaPrefixFacts context expected annotation types initial result final)
    (below : initial.LocalBindersBelowNextLocal) : final.LocalBindersBelowNextLocal :=
  lambda_prefix below prefixFacts
private theorem scrutineesRun {fuel : Nat} {context : SourceInference.Context} {span : Syntax.SourceSpan}
    {sources : List Syntax.Expr} {initial : State} {value : InferredExpression} {final : State}
    (accepted : matchScrutinee fuel context span sources initial = .ok (value, final))
    (below : initial.LocalBindersBelowNextLocal) : final.LocalBindersBelowNextLocal :=
  match_scrutinee below accepted

theorem child_bound {parent child : CallIndex} (inputs : parent.Inputs)
    (below : parent.initial.LocalBindersBelowNextLocal) (step : ChildStep parent child) :
    child.initial.LocalBindersBelowNextLocal := by
  cases step
  all_goals simp only [CallIndex.initial] at below ⊢
  all_goals try solve_by_elim (maxDepth := 10) (transparency := .reducible) [
    expressionAllocation, statementAllocation, freshAllocation, hiddenAllocation,
    constructorAllocation, optionalFit, assignedFit,
    expressionRun, expressionsRun, placeRun, itemsRun, itemRun, unifyRun,
    statementsRun, statementRun, parametersRun, patternRun, lambdaPrefixRun, scrutineesRun]

  case statement_if_else fuel context source expected initial allocated id result condition thenBody elseBody
      conditionValue conditionState body thenResult elseResult accepted form allocation conditionAccepted hasElse thenAccepted child =>
    exact State.restoreLexicalScope_preserves_localBindersBelowNextLocal
      (expressionRun conditionAccepted (statementAllocation allocation below))
      (inferStatementsFuel_nextLocal_le thenAccepted)
  case statement_for_post fuel context source expected initial allocated id result span initializer post condition body
      initialized conditionValue conditionState bodyResult postResult accepted form allocation initializerAccepted conditionAccepted bodyAccepted child =>
    exact State.restoreLexicalScope_preserves_localBindersBelowNextLocal
      (itemsRun initializerAccepted (statementAllocation allocation below))
      (Nat.le_trans (inferExprFuel_nextLocal_le conditionAccepted) (inferStatementsFuel_nextLocal_le bodyAccepted))
  case assignedValue_value fuel context target value operator initial final targetState assignment inferred place
      fitted childFinal childValue accepted targetAccepted fitting child =>
    have targetBelow := placeRun targetAccepted below
    cases operator <;> dsimp only at fitting
    · cases Except.ok.inj fitting; exact targetBelow
    all_goals exact unifyRun fitting targetBelow
  case constructorApplication_arguments fuel context source id instantiation sources expected initial fitted final childFinal
      value values accepted arity fitting child =>
    cases expected with
    | none => cases Except.ok.inj fitting; exact below
    | some type => exact unifyRun fitting below
  case expression_index_key fuel context source expected initial allocated final id value base key brackets baseValue keyValue
      baseState keyState valueState fitted childFinal keyType valueType accepted form allocation baseAccepted keyFresh valueFresh fitting child =>
    exact unifyRun fitting (freshAllocation valueFresh (freshAllocation keyFresh
      (expressionRun baseAccepted (expressionAllocation allocation below))))
  case matchCases_tail fuel context scrutinee expected saved arm arms initial patternState patternValue result body tail
      accepted patternAccepted bodyAccepted child =>
    have same : initial.lexicalScope = saved := inputs.bounds.2.2
    rw [← same]
    exact State.restoreLexicalScope_preserves_localBindersBelowNextLocal below
      (Nat.le_trans (inferMatchPatternFuel_nextLocal_le patternAccepted) (inferStatementsFuel_nextLocal_le bodyAccepted))
  case statement_match_default fuel context source expected initial allocated id result scrutinees arms scrutinee
      scrutineeState hiddenState hidden checked body bodyResult accepted form allocation scrutineeAccepted hiddenAllocated casesAccepted defaultBody child =>
    exact State.LocalBindersBelowNextLocal.transport
      (congrArg LexicalScope.binders (inferMatchCasesFuel_success_lexicalScope_eq rfl casesAccepted))
      (inferMatchCasesFuel_nextLocal_le casesAccepted)
      (hiddenAllocation hiddenAllocated (scrutineesRun scrutineeAccepted (statementAllocation allocation below)))

/-- The actual root initialization supplies the bound at every reached call. -/
theorem occurrence_bound {root call : CallIndex} (inputs : root.Inputs)
    (below : root.initial.LocalBindersBelowNextLocal) (here : CallOccurrence root call) :
    call.initial.LocalBindersBelowNextLocal := by
  induction here with
  | root _ => exact below
  | child path step ih => exact child_bound (path.inputs inputs) ih step

end Solcore.SourceSemantics.SourceInferenceExecution.ActualLocalAllocator
