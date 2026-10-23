import Solcore.SourceSemantics.SourceInferenceActualNodeGraphPrefixes

/-! Closed node tables follow the exact prefixes of actual recursive calls. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000

namespace Solcore.SourceSemantics.SourceInferenceExecution
open Frontend SourceInference TypeSystem Detail
open ActualNodeGraph

private theorem expressionRun {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Expr}
    {expected : Option Ty} {initial : State} {value : InferredExpression} {final : State}
    (accepted : inferExprFuel fuel context source expected initial = .ok (value, final))
    (closed : NodesClosed initial.nodes) : NodesClosed final.nodes :=
  (inferExprFuel_occurrenceGraph accepted).graph.closed closed

private theorem expressionsRun {fuel : Nat} {context : SourceInference.Context} {sources : List Syntax.Expr}
    {initial : State} {values : List InferredExpression} {final : State}
    (accepted : inferExprsFuel fuel context sources initial = .ok (values, final))
    (closed : NodesClosed initial.nodes) : NodesClosed final.nodes :=
  (inferExprsFuel_occurrenceGraph accepted).graph.closed closed

private theorem placeRun {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Expr}
    {initial : State} {place : PlaceResolution} {final : State}
    (accepted : inferPlaceFuel fuel context source initial = .ok (place, final))
    (closed : NodesClosed initial.nodes) : NodesClosed final.nodes :=
  (inferPlaceFuel_occurrenceGraph accepted).graph.closed closed

private theorem itemsRun {fuel : Nat} {context : SourceInference.Context} {sources : List Syntax.ForItem}
    {initial : State} {result : InferredForItems}
    (accepted : inferForItemsFuel fuel context sources initial = .ok result)
    (closed : NodesClosed initial.nodes) : NodesClosed result.state.nodes :=
  (inferForItemsFuel_occurrenceGraph accepted).graph.closed closed

private theorem itemRun {fuel : Nat} {context : SourceInference.Context} {source : Syntax.ForItem}
    {initial : State} {item : ForItemForm} {final : State}
    (accepted : inferForItemFuel fuel context source initial = .ok (item, final))
    (closed : NodesClosed initial.nodes) : NodesClosed final.nodes :=
  (inferForItemFuel_occurrenceGraph accepted).graph.closed closed

private theorem statementsRun {fuel : Nat} {context : SourceInference.Context} {sources : List Syntax.Statement}
    {expected : Ty} {initial : State} {result : BlockResult}
    (accepted : inferStatementsFuel fuel context sources expected initial = .ok result)
    (closed : NodesClosed initial.nodes) : NodesClosed result.state.nodes :=
  (inferStatementsFuel_occurrenceGraph accepted).graph.closed closed

private theorem statementRun {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Statement}
    {expected : Ty} {initial : State} {result : StatementResult}
    (accepted : inferStatementFuel fuel context source expected initial = .ok result)
    (closed : NodesClosed initial.nodes) : NodesClosed result.state.nodes :=
  (inferStatementFuel_occurrenceGraph accepted).graph.closed closed

private theorem casesRun {fuel : Nat} {context : SourceInference.Context} {arms : List Syntax.MatchCase}
    {expected scrutinee : Ty} {saved : LexicalScope} {initial : State} {result : MatchCasesResult}
    (accepted : inferMatchCasesFuel fuel context scrutinee expected saved arms initial = .ok result)
    (closed : NodesClosed initial.nodes) : NodesClosed result.state.nodes :=
  (inferMatchCasesFuel_occurrenceGraph accepted).graph.closed closed

private theorem scrutineesRun {fuel : Nat} {context : SourceInference.Context}
    {span : Syntax.SourceSpan} {sources : List Syntax.Expr} {initial : State}
    {value : InferredExpression} {final : State}
    (accepted : matchScrutinee fuel context span sources initial = .ok (value, final))
    (closed : NodesClosed initial.nodes) : NodesClosed final.nodes := by
  unfold matchScrutinee at accepted
  split at accepted
  · exact expressionRun accepted closed
  · cases actual : inferExprsFuel fuel context sources initial with
    | error error => simp [actual, bind, Except.bind] at accepted
    | ok inferred =>
        simp only [actual, bind, Except.bind, pure, Pure.pure, Except.pure, Except.ok.injEq] at accepted
        cases accepted
        have graph := inferExprsFuel_occurrenceGraph actual
        apply NodesClosed.record (graph.graph.closed closed)
        simpa only [Node.references, ExpressionForm.references, List.map_map, Function.comp_def,
          State.allocateExpressionId_nodes, ReturnedNodeReferences.references] using graph.returned

/-- Only actual prefix runs are used; readiness or semantic typing is unnecessary. -/
theorem ChildStep.nodesClosed {parent child : CallIndex} (step : ChildStep parent child)
    (closed : NodesClosed parent.initial.nodes) : NodesClosed child.initial.nodes := by
  cases step
  all_goals simp only [CallIndex.initial, State.restoreLexicalScope_nodes] at closed ⊢
  all_goals try solve_by_elim (maxDepth := 12) (transparency := .reducible) [
    expressionAllocation, statementAllocation, freshAllocation, hiddenAllocation,
    constructorAllocation, optionalFit, assignedFit, parameters, pattern, lambdaPrefix,
    expressionRun, expressionsRun, placeRun, itemsRun, itemRun, unifyRun,
    statementsRun, statementRun, casesRun, scrutineesRun]

  case expression_lambda_body _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ allocation parametersAccepted prefixFacts _ =>
    exact lambdaPrefix prefixFacts (parameters parametersAccepted (expressionAllocation allocation closed))
  case matchCases_body _ _ _ _ _ _ _ _ _ _ _ _ _ patternAccepted _ =>
    exact ActualNodeGraph.pattern patternAccepted closed
  case matchCases_tail _ _ _ _ _ _ _ _ _ _ _ _ _ _ patternAccepted bodyAccepted _ =>
    exact statementsRun bodyAccepted (ActualNodeGraph.pattern patternAccepted closed)
  case assignedValue_value fuel context target value operator initial final targetState assignment inferred place
      fitted childFinal childValue accepted targetAccepted fitting child =>
    have targetClosed := placeRun targetAccepted closed
    cases operator <;> dsimp only at fitting
    · cases Except.ok.inj fitting; exact targetClosed
    all_goals exact unifyRun fitting targetClosed
  case constructorApplication_arguments fuel context source id instantiation sources expected initial fitted final childFinal
      value values accepted arity fitting child =>
    cases expected with
    | none => cases Except.ok.inj fitting; exact closed
    | some type => exact unifyRun fitting closed

theorem CallOccurrence.nodesClosed {root call : CallIndex}
    (here : CallOccurrence root call) (closed : NodesClosed root.initial.nodes) :
    NodesClosed call.initial.nodes := by
  induction here with
  | root _ => exact closed
  | child _ step ih => exact step.nodesClosed ih

end Solcore.SourceSemantics.SourceInferenceExecution
