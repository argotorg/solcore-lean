import Lean
import Solcore.SourceSemantics.Internal.Execution.CallInputs
import Solcore.SourceSemantics.Internal.Execution.BinderRetention
import Solcore.SourceSemantics.Internal.Privacy.LifetimeMatches
import Solcore.SourceSemantics.Internal.Execution.GeneralizationEvents
import Solcore.SourceSemantics.Internal.Execution.CallGraph
import Solcore.SourceSemantics.Internal.Compiled.Origins

/-!
# Template backing

Raw template witnesses at recursive checker entries.
-/

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceActualBoundaryPrefixes
/-! Genuine child entries inherit bounded generalization progress from the
actual allocation and completed sibling prefixes of the same parent call. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
namespace Solcore.SourceSemantics.SourceInferenceExecution
open Frontend SourceInference TypeSystem Detail
open LocalGeneralizationBoundaries

private theorem allocated_expression {before after : State} {id : ExpressionId}
    (accepted : before.allocateExpressionId = (id, after)) :
    Progress before after := by
  have same : after = before.allocateExpressionId.2 := (congrArg Prod.snd accepted).symm
  rw [same]
  exact Progress.allocateExpressionId _
private theorem allocated_statement {before after : State} {id : StatementId}
    (accepted : before.allocateStatementId = (id, after)) :
    Progress before after := by
  have same : after = before.allocateStatementId.2 := (congrArg Prod.snd accepted).symm
  rw [same]
  exact Progress.allocateStatementId _
private theorem allocated_fresh {before after : State} {type : Ty}
    (accepted : before.fresh = (type, after)) :
    Progress before after := by
  have same : after = before.fresh.2 := (congrArg Prod.snd accepted).symm
  rw [same]
  exact Progress.fresh _
private theorem allocated_hidden {before after : State} {id : Resolved.LocalId}
    (accepted : before.allocateHiddenLocal = (id, after)) :
    Progress before after := by
  have same : after = before.allocateHiddenLocal.2 := (congrArg Prod.snd accepted).symm
  rw [same]
  exact Progress.allocateHiddenLocal _
private theorem allocated_constructor {before after : State}
    {dataType : ProgramDataSignature} {constructor : ProgramDataConstructorSignature}
    {instantiation : DataConstructorInstantiation}
    (accepted : freshDataConstructorInstantiation dataType constructor before = (instantiation, after)) :
    Progress before after := by
  simpa only [accepted] using
    Progress.freshDataConstructorInstantiation dataType constructor before

private theorem lambda_prefix {context : SourceInference.Context}
    {expected : Option Ty} {annotation : Option Syntax.TypeExpr}
    {parameters : List Ty} {before after : State} {resultType : Ty}
    (prefixFacts : LambdaPrefixFacts context expected annotation parameters before resultType after) :
    Progress before after := by
  cases prefixFacts with
  | noExpectedPartsAnnotated => exact .refl _
  | noExpectedPartsFresh _ _ allocated => exact allocated_fresh allocated
  | expectedPartsAnnotated _ unified => exact Progress.unify unified
  | expectedPartsInferred _ unified => exact Progress.unify unified

private theorem scrutinee_prefix {fuel : Nat} {context : SourceInference.Context}
    {span : Syntax.SourceSpan} {sources : List Syntax.Expr} {before : State}
    {result : InferredExpression × State}
    (accepted : matchScrutinee fuel context span sources before = .ok result) :
    Progress before result.2 := by
  unfold matchScrutinee at accepted
  split at accepted
  · exact inferExprFuel_boundaries_progress accepted
  · cases child : inferExprsFuel fuel context sources before with
    | error error => simp [child, bind, Except.bind] at accepted
    | ok value =>
      have progress := inferExprsFuel_boundaries_progress child
      simp only [child, bind, Except.bind, pure, Pure.pure, Except.pure, Except.ok.injEq] at accepted
      cases accepted
      exact progress.trans ((Progress.allocateExpressionId _).trans
        (Progress.recordExpression _ _ (by intro _ _ impossible; cases impossible)))

open Lean Meta Elab Tactic in
elab "collect_boundary_prefix" : tactic => withMainContext do
  let hypotheses := (← getLCtx).getFVarIds
  for theoremName in [
      ``allocated_expression, ``allocated_statement, ``allocated_fresh, ``allocated_hidden,
      ``allocated_constructor, ``lambda_prefix, ``scrutinee_prefix,
      ``inferExprFuel_boundaries_progress, ``inferExprsFuel_boundaries_progress,
      ``inferStatementsFuel_boundaries_progress, ``inferStatementFuel_boundaries_progress,
      ``inferForItemsFuel_boundaries_progress, ``inferForItemFuel_boundaries_progress,
      ``inferPlaceFuel_boundaries_progress,
      ``Progress.inferMatchPatternFuel, ``Progress.bindLambdaParameters,
      ``Progress.unify] do
    for hypothesis in hypotheses do
      let saved ← saveState
      try
        let proof ← mkAppM theoremName #[mkFVar hypothesis]
        let proof ← instantiateMVars proof
        if proof.hasExprMVar then throwError "unresolved direct prefix"
        let (_, next) ← (← getMainGoal).note (Name.mkSimple "boundaries_prefix") proof
        setGoals [next]
      catch _ => saved.restore

theorem ChildStep.boundaries_prefix {parent child : CallIndex} (inputs : parent.Inputs) (step : ChildStep parent child) :
    Progress parent.initial child.initial := by
  cases step
  case assignedValue_value accepted targetAccepted fitting child =>
    split at fitting
    all_goals try cases Except.ok.inj fitting
    all_goals collect_boundary_prefix
    all_goals simp only [CallIndex.initial]
    all_goals try solve_by_elim (maxDepth := 8) (transparency := .reducible)
      [Progress.trans, Progress.refl]
  case constructorApplication_arguments accepted arity fitting child =>
    split at fitting
    all_goals try cases Except.ok.inj fitting
    all_goals collect_boundary_prefix
    all_goals simp only [CallIndex.initial]
    all_goals try solve_by_elim (maxDepth := 8) (transparency := .reducible)
      [Progress.trans, Progress.refl]
  all_goals collect_boundary_prefix
  all_goals simp only [CallIndex.initial]
  all_goals try solve_by_elim (maxDepth := 8) (transparency := .reducible)
    [Progress.trans, Progress.refl]
  case statement_if_else =>
    exact (allocated_statement (by assumption)).trans
      ((inferExprFuel_boundaries_progress (by assumption)).trans
        ((inferStatementsFuel_boundaries_progress (by assumption)).restore _
          (fun _ member => member)))
  case statement_for_post =>
    exact (allocated_statement (by assumption)).trans
      ((inferForItemsFuel_boundaries_progress (by assumption)).trans
        (((inferExprFuel_boundaries_progress (by assumption)).trans
          (inferStatementsFuel_boundaries_progress (by assumption))).restore _
          (fun _ member => member)))
  case expression_index_key =>
    exact (allocated_expression (by assumption)).trans
      ((inferExprFuel_boundaries_progress (by assumption)).trans
        ((allocated_fresh (by assumption)).trans
          ((allocated_fresh (by assumption)).trans (Progress.unify (by assumption)))))
  case matchCases_tail =>
    have scope := inputs.bounds.2.2
    exact ((Progress.inferMatchPatternFuel (by assumption)).trans
      (inferStatementsFuel_boundaries_progress (by assumption))).restore _
      (by rw [← scope]; exact fun _ member => member)
  case statement_match_default =>
    exact (allocated_statement (by assumption)).trans
      ((scrutinee_prefix (by assumption)).trans
        ((allocated_hidden (by assumption)).trans
          (inferMatchCasesFuel_boundaries_progress (fun _ member => member) (by assumption))))

theorem CallOccurrence.boundaries_prefix {root call : CallIndex} (inputs : root.Inputs) (here : CallOccurrence root call) :
    Progress root.initial call.initial := by
  induction here with
  | root _ => exact .refl _
  | child path step ih => exact ih.trans (step.boundaries_prefix (path.inputs inputs))

end Solcore.SourceSemantics.SourceInferenceExecution
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceActualExpressionTemplateBacking
/-! Template backing at the actual expression-family child entries. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceExecution.ActualTemplateBacking
open Frontend SourceInference TypeSystem Detail SourceInferenceSoundness.ProtectedVariables

theorem expression_group
      {fuel : Nat} {context : SourceInference.Context} {source inner : Syntax.Expr}
      {expected : Option Ty} {initial allocated final childFinal : State}
      {id : ExpressionId} {value childValue : InferredExpression}
      (accepted : (CallIndex.expression (fuel + 1) context source expected
        initial value final).Accepted)
      (form : source.value = .group inner)
      (allocation : initial.allocateExpressionId = (id, allocated))
      (child : inferExprFuel fuel context inner expected allocated =
        .ok (childValue, childFinal))
      (inputs : (CallIndex.expression (fuel + 1) context source expected initial value final).Inputs)
      (backed : LiveTemplatesBacked initial) : LiveTemplatesBacked (CallIndex.expression fuel context inner expected allocated childValue childFinal).initial := by
  have step : ChildStep (CallIndex.expression (fuel + 1) context source expected initial value final) (CallIndex.expression fuel context inner expected allocated childValue childFinal) := .expression_group accepted form allocation child
  have childInputs := step.inputs inputs
  have same : allocated = initial.allocateExpressionId.2 := (congrArg Prod.snd allocation).symm
  subst allocated
  exact backed.allocateExpressionId

theorem expression_tuple
      {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Expr}
      {elements : Syntax.DelimitedList Syntax.Expr} {expected : Option Ty}
      {initial allocated final childFinal : State} {id : ExpressionId}
      {value : InferredExpression} {values : List InferredExpression}
      (accepted : (CallIndex.expression (fuel + 1) context source expected
        initial value final).Accepted)
      (form : source.value = .tuple elements)
      (allocation : initial.allocateExpressionId = (id, allocated))
      (child : inferExprsFuel fuel context elements.elements allocated =
        .ok (values, childFinal))
      (inputs : (CallIndex.expression (fuel + 1) context source expected initial value final).Inputs)
      (backed : LiveTemplatesBacked initial) : LiveTemplatesBacked (CallIndex.expressions fuel context elements.elements allocated values childFinal).initial := by
  have step : ChildStep (CallIndex.expression (fuel + 1) context source expected initial value final) (CallIndex.expressions fuel context elements.elements allocated values childFinal) := .expression_tuple accepted form allocation child
  have childInputs := step.inputs inputs
  have same : allocated = initial.allocateExpressionId.2 := (congrArg Prod.snd allocation).symm
  subst allocated
  exact backed.allocateExpressionId

theorem expression_unary
      {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Expr}
      {expected : Option Ty} {initial allocated final : State} {id : ExpressionId}
      {value : InferredExpression}
      {operator : Syntax.Located Syntax.UnaryOp} {operand : Syntax.Expr}
      {inferred : InferredExpression} {childFinal : State}
      (accepted : (CallIndex.expression (fuel + 1) context source expected initial value final).Accepted)
      (form : source.value = .unary operator operand)
      (allocation : initial.allocateExpressionId = (id, allocated))
      (child : (CallIndex.expression fuel context operand none allocated inferred childFinal).Accepted)
      (inputs : (CallIndex.expression (fuel + 1) context source expected initial value final).Inputs)
      (backed : LiveTemplatesBacked initial) : LiveTemplatesBacked (CallIndex.expression fuel context operand none allocated inferred childFinal).initial := by
  have step : ChildStep (CallIndex.expression (fuel + 1) context source expected initial value final) (CallIndex.expression fuel context operand none allocated inferred childFinal) := .expression_unary accepted form allocation child
  have childInputs := step.inputs inputs
  have same : allocated = initial.allocateExpressionId.2 := (congrArg Prod.snd allocation).symm
  subst allocated
  exact backed.allocateExpressionId

theorem expression_binary_left
      {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Expr}
      {expected : Option Ty} {initial allocated final : State} {id : ExpressionId}
      {value : InferredExpression}
      {operator : Syntax.Located Syntax.BinaryOp} {left right : Syntax.Expr}
      {leftValue : InferredExpression} {leftState : State}
      (accepted : (CallIndex.expression (fuel + 1) context source expected initial value final).Accepted)
      (form : source.value = .binary left operator right)
      (allocation : initial.allocateExpressionId = (id, allocated))
      (child : (CallIndex.expression fuel context left none allocated leftValue leftState).Accepted)
      (inputs : (CallIndex.expression (fuel + 1) context source expected initial value final).Inputs)
      (backed : LiveTemplatesBacked initial) : LiveTemplatesBacked (CallIndex.expression fuel context left none allocated leftValue leftState).initial := by
  have step : ChildStep (CallIndex.expression (fuel + 1) context source expected initial value final) (CallIndex.expression fuel context left none allocated leftValue leftState) := .expression_binary_left accepted form allocation child
  have childInputs := step.inputs inputs
  have same : allocated = initial.allocateExpressionId.2 := (congrArg Prod.snd allocation).symm
  subst allocated
  exact backed.allocateExpressionId

theorem expression_conditional_condition
      {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Expr}
      {expected : Option Ty} {initial allocated final : State} {id : ExpressionId}
      {value : InferredExpression}
      {condition thenBranch elseBranch : Syntax.Expr} {question colon : Syntax.SourceSpan}
      {conditionValue : InferredExpression} {conditionState : State}
      (accepted : (CallIndex.expression (fuel + 1) context source expected initial value final).Accepted)
      (form : source.value = .conditional condition question thenBranch colon elseBranch)
      (allocation : initial.allocateExpressionId = (id, allocated))
      (child : (CallIndex.expression fuel context condition (some .bool) allocated conditionValue conditionState).Accepted)
      (inputs : (CallIndex.expression (fuel + 1) context source expected initial value final).Inputs)
      (backed : LiveTemplatesBacked initial) : LiveTemplatesBacked (CallIndex.expression fuel context condition (some .bool) allocated conditionValue conditionState).initial := by
  have step : ChildStep (CallIndex.expression (fuel + 1) context source expected initial value final) (CallIndex.expression fuel context condition (some .bool) allocated conditionValue conditionState) := .expression_conditional_condition accepted form allocation child
  have childInputs := step.inputs inputs
  have same : allocated = initial.allocateExpressionId.2 := (congrArg Prod.snd allocation).symm
  subst allocated
  exact backed.allocateExpressionId

theorem expression_index_base
      {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Expr}
      {expected : Option Ty} {initial allocated final : State} {id : ExpressionId}
      {value : InferredExpression}
      {base key : Syntax.Expr} {brackets : Syntax.SourceSpan}
      {inferred : InferredExpression} {childFinal : State}
      (accepted : (CallIndex.expression (fuel + 1) context source expected initial value final).Accepted)
      (form : source.value = .index base brackets key)
      (allocation : initial.allocateExpressionId = (id, allocated))
      (child : (CallIndex.expression fuel context base none allocated inferred childFinal).Accepted)
      (inputs : (CallIndex.expression (fuel + 1) context source expected initial value final).Inputs)
      (backed : LiveTemplatesBacked initial) : LiveTemplatesBacked (CallIndex.expression fuel context base none allocated inferred childFinal).initial := by
  have step : ChildStep (CallIndex.expression (fuel + 1) context source expected initial value final) (CallIndex.expression fuel context base none allocated inferred childFinal) := .expression_index_base accepted form allocation child
  have childInputs := step.inputs inputs
  have same : allocated = initial.allocateExpressionId.2 := (congrArg Prod.snd allocation).symm
  subst allocated
  exact backed.allocateExpressionId

theorem expression_call_arguments
      {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Expr}
      {expected : Option Ty} {initial allocated final : State} {id : ExpressionId}
      {value : InferredExpression}
      {callee : Syntax.Expr} {arguments : Syntax.DelimitedList Syntax.Expr}
      {values : List InferredExpression} {childFinal : State}
      (accepted : (CallIndex.expression (fuel + 1) context source expected initial value final).Accepted)
      (form : source.value = .call callee arguments)
      (allocation : initial.allocateExpressionId = (id, allocated))
      (nonconstructor : constructorCalleeCandidates context allocated callee = .ok [])
      (child : (CallIndex.expressions fuel context arguments.elements allocated values childFinal).Accepted)
      (inputs : (CallIndex.expression (fuel + 1) context source expected initial value final).Inputs)
      (backed : LiveTemplatesBacked initial) : LiveTemplatesBacked (CallIndex.expressions fuel context arguments.elements allocated values childFinal).initial := by
  have step : ChildStep (CallIndex.expression (fuel + 1) context source expected initial value final) (CallIndex.expressions fuel context arguments.elements allocated values childFinal) := .expression_call_arguments accepted form allocation nonconstructor child
  have childInputs := step.inputs inputs
  have same : allocated = initial.allocateExpressionId.2 := (congrArg Prod.snd allocation).symm
  subst allocated
  exact backed.allocateExpressionId

theorem expression_contextual_constructor
      {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Expr}
      {expected : Option Ty} {initial allocated final : State} {id : ExpressionId}
      {value : InferredExpression}
      {dot : Syntax.SourceSpan} {name : Syntax.Identifier} {arguments : Option (Syntax.DelimitedList Syntax.Expr)}
      {dataType : ProgramDataSignature} {constructor : ProgramDataConstructorSignature} {typeArguments : List Ty}
      {inferred : InferredExpression} {childFinal : State}
      (accepted : (CallIndex.expression (fuel + 1) context source expected initial value final).Accepted)
      (form : source.value = .dotConstructor dot name arguments)
      (allocation : initial.allocateExpressionId = (id, allocated))
      (selected : contextualConstructorCandidate context allocated expected name.value = .ok (dataType, constructor, typeArguments))
      (child : (CallIndex.constructorApplication fuel context source id (instantiateDataConstructor dataType constructor typeArguments) (arguments.map (·.elements) |>.getD []) expected allocated inferred childFinal).Accepted)
      (inputs : (CallIndex.expression (fuel + 1) context source expected initial value final).Inputs)
      (backed : LiveTemplatesBacked initial) : LiveTemplatesBacked (CallIndex.constructorApplication fuel context source id (instantiateDataConstructor dataType constructor typeArguments) (arguments.map (·.elements) |>.getD []) expected allocated inferred childFinal).initial := by
  have step : ChildStep (CallIndex.expression (fuel + 1) context source expected initial value final) (CallIndex.constructorApplication fuel context source id (instantiateDataConstructor dataType constructor typeArguments) (arguments.map (·.elements) |>.getD []) expected allocated inferred childFinal) := .expression_contextual_constructor accepted form allocation selected child
  have childInputs := step.inputs inputs
  have same : allocated = initial.allocateExpressionId.2 := (congrArg Prod.snd allocation).symm
  subst allocated
  exact backed.allocateExpressionId

theorem expression_binary_right
      {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Expr}
      {expected : Option Ty} {initial allocated final : State} {id : ExpressionId}
      {value : InferredExpression}
      {operator : Syntax.Located Syntax.BinaryOp} {left right : Syntax.Expr}
      {leftValue : InferredExpression} {leftState : State}
      {rightValue : InferredExpression} {rightState : State}
      (accepted : (CallIndex.expression (fuel + 1) context source expected initial value final).Accepted)
      (form : source.value = .binary left operator right)
      (allocation : initial.allocateExpressionId = (id, allocated))
      (leftAccepted : inferExprFuel fuel context left none allocated = .ok (leftValue, leftState))
      (child : (CallIndex.expression fuel context right none leftState rightValue rightState).Accepted)
      (inputs : (CallIndex.expression (fuel + 1) context source expected initial value final).Inputs)
      (backed : LiveTemplatesBacked initial) : LiveTemplatesBacked (CallIndex.expression fuel context right none leftState rightValue rightState).initial := by
  have step : ChildStep (CallIndex.expression (fuel + 1) context source expected initial value final) (CallIndex.expression fuel context right none leftState rightValue rightState) := .expression_binary_right accepted form allocation leftAccepted child
  have childInputs := step.inputs inputs
  have same : allocated = initial.allocateExpressionId.2 := (congrArg Prod.snd allocation).symm
  subst allocated
  have before := ChildStep.inputs inputs (.expression_binary_left accepted form allocation leftAccepted)
  exact expression before backed.allocateExpressionId leftAccepted

theorem expression_conditional_then
      {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Expr}
      {expected : Option Ty} {initial allocated final : State} {id : ExpressionId}
      {value : InferredExpression}
      {condition thenBranch elseBranch : Syntax.Expr} {question colon : Syntax.SourceSpan}
      {conditionValue : InferredExpression} {conditionState : State}
      {thenValue : InferredExpression} {thenState : State}
      (accepted : (CallIndex.expression (fuel + 1) context source expected initial value final).Accepted)
      (form : source.value = .conditional condition question thenBranch colon elseBranch)
      (allocation : initial.allocateExpressionId = (id, allocated))
      (conditionAccepted : inferExprFuel fuel context condition (some .bool) allocated = .ok (conditionValue, conditionState))
      (child : (CallIndex.expression fuel context thenBranch expected conditionState thenValue thenState).Accepted)
      (inputs : (CallIndex.expression (fuel + 1) context source expected initial value final).Inputs)
      (backed : LiveTemplatesBacked initial) : LiveTemplatesBacked (CallIndex.expression fuel context thenBranch expected conditionState thenValue thenState).initial := by
  have step : ChildStep (CallIndex.expression (fuel + 1) context source expected initial value final) (CallIndex.expression fuel context thenBranch expected conditionState thenValue thenState) := .expression_conditional_then accepted form allocation conditionAccepted child
  have childInputs := step.inputs inputs
  have same : allocated = initial.allocateExpressionId.2 := (congrArg Prod.snd allocation).symm
  subst allocated
  have before := ChildStep.inputs inputs (.expression_conditional_condition accepted form allocation conditionAccepted)
  exact expression before backed.allocateExpressionId conditionAccepted

theorem expression_conditional_else
      {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Expr}
      {expected : Option Ty} {initial allocated final : State} {id : ExpressionId}
      {value : InferredExpression}
      {condition thenBranch elseBranch : Syntax.Expr} {question colon : Syntax.SourceSpan}
      {conditionValue : InferredExpression} {conditionState : State}
      {thenValue elseValue : InferredExpression} {thenState elseState : State}
      (accepted : (CallIndex.expression (fuel + 1) context source expected initial value final).Accepted)
      (form : source.value = .conditional condition question thenBranch colon elseBranch)
      (allocation : initial.allocateExpressionId = (id, allocated))
      (conditionAccepted : inferExprFuel fuel context condition (some .bool) allocated = .ok (conditionValue, conditionState))
      (thenAccepted : inferExprFuel fuel context thenBranch expected conditionState = .ok (thenValue, thenState))
      (child : (CallIndex.expression fuel context elseBranch expected thenState elseValue elseState).Accepted)
      (inputs : (CallIndex.expression (fuel + 1) context source expected initial value final).Inputs)
      (backed : LiveTemplatesBacked initial) : LiveTemplatesBacked (CallIndex.expression fuel context elseBranch expected thenState elseValue elseState).initial := by
  have step : ChildStep (CallIndex.expression (fuel + 1) context source expected initial value final) (CallIndex.expression fuel context elseBranch expected thenState elseValue elseState) := .expression_conditional_else accepted form allocation conditionAccepted thenAccepted child
  have childInputs := step.inputs inputs
  have same : allocated = initial.allocateExpressionId.2 := (congrArg Prod.snd allocation).symm
  subst allocated
  have first := ChildStep.inputs inputs (.expression_conditional_condition accepted form allocation conditionAccepted)
  have second := ChildStep.inputs inputs (.expression_conditional_then accepted form allocation conditionAccepted thenAccepted)
  exact expression second (expression first backed.allocateExpressionId conditionAccepted) thenAccepted

theorem expression_call_callee
      {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Expr}
      {expected : Option Ty} {initial allocated final : State} {id : ExpressionId}
      {value : InferredExpression}
      {callee : Syntax.Expr} {arguments : Syntax.DelimitedList Syntax.Expr}
      {values : List InferredExpression} {argumentState childFinal : State} {inferred : InferredExpression}
      (accepted : (CallIndex.expression (fuel + 1) context source expected initial value final).Accepted)
      (form : source.value = .call callee arguments)
      (allocation : initial.allocateExpressionId = (id, allocated))
      (nonconstructor : constructorCalleeCandidates context allocated callee = .ok [])
      (argumentsAccepted : inferExprsFuel fuel context arguments.elements allocated = .ok (values, argumentState))
      (indirect : IndirectCalleeAt context callee argumentState)
      (child : (CallIndex.expression fuel context callee none argumentState inferred childFinal).Accepted)
      (inputs : (CallIndex.expression (fuel + 1) context source expected initial value final).Inputs)
      (backed : LiveTemplatesBacked initial) : LiveTemplatesBacked (CallIndex.expression fuel context callee none argumentState inferred childFinal).initial := by
  have step : ChildStep (CallIndex.expression (fuel + 1) context source expected initial value final) (CallIndex.expression fuel context callee none argumentState inferred childFinal) := .expression_call_callee accepted form allocation nonconstructor argumentsAccepted indirect child
  have childInputs := step.inputs inputs
  have same : allocated = initial.allocateExpressionId.2 := (congrArg Prod.snd allocation).symm
  subst allocated
  have before := ChildStep.inputs inputs (.expression_call_arguments accepted form allocation nonconstructor argumentsAccepted)
  exact expressions before backed.allocateExpressionId argumentsAccepted

theorem expression_lambda_body
      {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Expr}
      {expected : Option Ty} {initial allocated final : State} {id : ExpressionId}
      {value : InferredExpression}
      {keyword : Syntax.SourceSpan} {parameters : Syntax.DelimitedList Syntax.LambdaParameter}
      {annotation : Option Syntax.TypeExpr} {body : Syntax.Block}
      {boundParameters : List TypedBinder} {parameterTypes : List Ty}
      {parameterState bodyState : State} {resultType : Ty} {bodyResult : BlockResult}
      (accepted : (CallIndex.expression (fuel + 1) context source expected initial value final).Accepted)
      (form : source.value = .lambda keyword parameters annotation body)
      (allocation : initial.allocateExpressionId = (id, allocated))
      (parametersAccepted : bindLambdaParameters context parameters.elements 0 [] allocated = .ok (boundParameters, parameterTypes, parameterState))
      (prefixFacts : LambdaPrefixFacts context expected annotation parameterTypes parameterState resultType bodyState)
      (child : (CallIndex.statements fuel { context with loopDepth := 0 } body.value resultType bodyState bodyResult).Accepted)
      (inputs : (CallIndex.expression (fuel + 1) context source expected initial value final).Inputs)
      (backed : LiveTemplatesBacked initial) : LiveTemplatesBacked (CallIndex.statements fuel { context with loopDepth := 0 } body.value resultType bodyState bodyResult).initial := by
  have step : ChildStep (CallIndex.expression (fuel + 1) context source expected initial value final) (CallIndex.statements fuel { context with loopDepth := 0 } body.value resultType bodyState bodyResult) := .expression_lambda_body accepted form allocation parametersAccepted prefixFacts child
  have childInputs := step.inputs inputs
  have same : allocated = initial.allocateExpressionId.2 := (congrArg Prod.snd allocation).symm
  subst allocated
  have parameters := bindLambdaParameters_inferenceProperties inputs.ready.allocateExpressionId parametersAccepted
  exact (backed.allocateExpressionId.bindLambdaParameters parametersAccepted).lambdaPrefix parameters.2.1 prefixFacts

theorem expression_index_key
      {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Expr}
      {expected : Option Ty} {initial allocated final : State} {id : ExpressionId}
      {value : InferredExpression}
      {base key : Syntax.Expr} {brackets : Syntax.SourceSpan} {baseValue keyValue : InferredExpression}
      {baseState keyState valueState fitted childFinal : State} {keyType valueType : Ty}
      (accepted : (CallIndex.expression (fuel + 1) context source expected initial value final).Accepted)
      (form : source.value = .index base brackets key)
      (allocation : initial.allocateExpressionId = (id, allocated))
      (baseAccepted : inferExprFuel fuel context base none allocated = .ok (baseValue, baseState))
      (keyFresh : baseState.fresh = (keyType, keyState))
      (valueFresh : keyState.fresh = (valueType, valueState))
      (fitting : unify valueState baseValue.type (.mapping keyType valueType) = .ok fitted)
      (child : (CallIndex.expression fuel context key (some (fitted.resolve keyType)) fitted keyValue childFinal).Accepted)
      (inputs : (CallIndex.expression (fuel + 1) context source expected initial value final).Inputs)
      (backed : LiveTemplatesBacked initial) : LiveTemplatesBacked (CallIndex.expression fuel context key (some (fitted.resolve keyType)) fitted keyValue childFinal).initial := by
  have step : ChildStep (CallIndex.expression (fuel + 1) context source expected initial value final) (CallIndex.expression fuel context key (some (fitted.resolve keyType)) fitted keyValue childFinal) := .expression_index_key accepted form allocation baseAccepted keyFresh valueFresh fitting child
  have childInputs := step.inputs inputs
  have same : allocated = initial.allocateExpressionId.2 := (congrArg Prod.snd allocation).symm
  subst allocated
  have before := ChildStep.inputs inputs (.expression_index_base accepted form allocation baseAccepted)
  have baseBacked := expression before backed.allocateExpressionId baseAccepted
  have baseReady := (before.progress baseAccepted).2.1
  have sameKey : keyState = baseState.fresh.2 := (congrArg Prod.snd keyFresh).symm
  subst keyState
  have sameValue : valueState = baseState.fresh.2.fresh.2 := (congrArg Prod.snd valueFresh).symm
  subst valueState
  exact baseBacked.fresh.fresh.unify baseReady.fresh.fresh.solved fitting

theorem expression_call_constructor
      {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Expr}
      {expected : Option Ty} {initial allocated final : State} {id : ExpressionId}
      {value : InferredExpression}
      {callee : Syntax.Expr} {arguments : Syntax.DelimitedList Syntax.Expr}
      {dataType : ProgramDataSignature} {constructor : ProgramDataConstructorSignature}
      {instantiation : DataConstructorInstantiation} {instantiated childFinal : State}
      {inferred : InferredExpression}
      (accepted : (CallIndex.expression (fuel + 1) context source expected initial value final).Accepted)
      (form : source.value = .call callee arguments)
      (allocation : initial.allocateExpressionId = (id, allocated))
      (selected : constructorCalleeCandidates context allocated callee = .ok [(dataType, constructor)])
      (fresh : freshDataConstructorInstantiation dataType constructor allocated = (instantiation, instantiated))
      (child : (CallIndex.constructorApplication fuel context source id instantiation arguments.elements expected instantiated inferred childFinal).Accepted)
      (inputs : (CallIndex.expression (fuel + 1) context source expected initial value final).Inputs)
      (backed : LiveTemplatesBacked initial) : LiveTemplatesBacked (CallIndex.constructorApplication fuel context source id instantiation arguments.elements expected instantiated inferred childFinal).initial := by
  have step : ChildStep (CallIndex.expression (fuel + 1) context source expected initial value final) (CallIndex.constructorApplication fuel context source id instantiation arguments.elements expected instantiated inferred childFinal) := .expression_call_constructor accepted form allocation selected fresh child
  have childInputs := step.inputs inputs
  have same : allocated = initial.allocateExpressionId.2 := (congrArg Prod.snd allocation).symm
  subst allocated
  have sameFresh : instantiated = (freshDataConstructorInstantiation dataType constructor initial.allocateExpressionId.2).2 :=
    (congrArg Prod.snd fresh).symm
  subst instantiated
  exact backed.allocateExpressionId.freshConstructor dataType constructor

theorem expression_field_constructor
      {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Expr}
      {expected : Option Ty} {initial allocated final : State} {id : ExpressionId}
      {value : InferredExpression}
      {base : Syntax.Expr} {dot : Syntax.SourceSpan} {name : Syntax.Identifier}
      {dataType : ProgramDataSignature} {constructor : ProgramDataConstructorSignature}
      {instantiation : DataConstructorInstantiation} {instantiated childFinal : State}
      {inferred : InferredExpression}
      (accepted : (CallIndex.expression (fuel + 1) context source expected initial value final).Accepted)
      (form : source.value = .field base dot name)
      (allocation : initial.allocateExpressionId = (id, allocated))
      (selected : constructorCalleeCandidates context allocated source = .ok [(dataType, constructor)])
      (fresh : freshDataConstructorInstantiation dataType constructor allocated = (instantiation, instantiated))
      (child : (CallIndex.constructorApplication fuel context source id instantiation [] expected instantiated inferred childFinal).Accepted)
      (inputs : (CallIndex.expression (fuel + 1) context source expected initial value final).Inputs)
      (backed : LiveTemplatesBacked initial) : LiveTemplatesBacked (CallIndex.constructorApplication fuel context source id instantiation [] expected instantiated inferred childFinal).initial := by
  have step : ChildStep (CallIndex.expression (fuel + 1) context source expected initial value final) (CallIndex.constructorApplication fuel context source id instantiation [] expected instantiated inferred childFinal) := .expression_field_constructor accepted form allocation selected fresh child
  have childInputs := step.inputs inputs
  have same : allocated = initial.allocateExpressionId.2 := (congrArg Prod.snd allocation).symm
  subst allocated
  have sameFresh : instantiated = (freshDataConstructorInstantiation dataType constructor initial.allocateExpressionId.2).2 :=
    (congrArg Prod.snd fresh).symm
  subst instantiated
  exact backed.allocateExpressionId.freshConstructor dataType constructor

end Solcore.SourceSemantics.SourceInferenceExecution.ActualTemplateBacking
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceActualGeneralizationSites
/-! A site identifies an actual initialized declaration call. Its only child
is the exact initializer whose result supplied the generalized quantifiers. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceExecution.ActualGeneralization
open Frontend SourceInference TypeSystem Detail

inductive Site : CallIndex → TypedBinder → ExpressionId → Prop where
  | statement {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Statement}
      {expected : Ty} {initial : State} {result : StatementResult}
      (receipt : LocalLetRequirementTiming.Receipt fuel context source initial result) :
      Site (.statement (fuel + 1) context source expected initial result)
        receipt.binding.1 receipt.value.id
  | header {fuel : Nat} {context : SourceInference.Context} {source : Syntax.ForItem}
      {initial final : State} {result : ForItemForm}
      (receipt : LocalHeaderRequirementTiming.Receipt fuel context source initial (result, final)) :
      Site (.forItem (fuel + 1) context source initial result final)
        receipt.binding.1 receipt.value.id

theorem Origin.site {root : CallIndex} {binder : TypedBinder} {initializer : ExpressionId}
    (origin : Origin root binder initializer) :
    ∃ call, CallOccurrence root call ∧ Site call binder initializer := by
  cases origin with
  | statement receipt here => exact ⟨_, here, .statement receipt⟩
  | @header fuel context source initial result receipt here =>
      rcases result with ⟨inferred, final⟩
      exact ⟨_, here, .header receipt⟩

theorem Site.unique {call : CallIndex} {left right : TypedBinder}
    {leftId rightId : ExpressionId} (first : Site call left leftId) (second : Site call right rightId) :
    left = right ∧ leftId = rightId := by
  cases first with
  | statement receipt =>
      cases second with
      | statement other =>
          have same := LocalLetRequirementTiming.Receipt.unique receipt other
          cases same
          exact ⟨rfl, rfl⟩
  | header receipt =>
      cases second with
      | header other =>
          have same := LocalHeaderRequirementTiming.Receipt.unique receipt other
          cases same
          exact ⟨rfl, rfl⟩

private theorem annotation_unique {context : SourceInference.Context}
    {source : Option Syntax.TypeExpr} {left right : Option Ty}
    (first : AnnotationExpected context source left)
    (second : AnnotationExpected context source right) : left = right := by
  cases first <;> cases second <;> simp_all

private theorem statement_child_unique
    {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Statement}
    {expected : Ty} {initial : State} {result : StatementResult}
    (receipt : LocalLetRequirementTiming.Receipt fuel context source initial result)
    {child : CallIndex}
    (step : ChildStep (.statement (fuel + 1) context source expected initial result) child) :
    child = .expression fuel context receipt.initializer receipt.expected
      initial.allocateStatementId.2 receipt.value receipt.ready := by
  cases step
  all_goals have syntaxForm := receipt.form
  all_goals try solve | simp_all
  rename_i allocated id name sourceType initializer childExpected value final annotated child form allocation accepted
  have parts : receipt.name = name ∧ receipt.annotation = sourceType ∧ receipt.initializer = initializer := by
    simpa only [receipt.form, Syntax.StatementValue.letDecl.injEq, Option.some.injEq] using form
  have actualAnnotation := annotationExpected_of_receipt receipt.annotationAccepted
  rw [← parts.2.1] at annotated
  have expectedEq := annotation_unique actualAnnotation annotated
  have actualChild := receipt.child
  rw [allocation, expectedEq, parts.2.2] at actualChild
  cases Except.ok.inj (actualChild.symm.trans child)
  simp only [allocation, expectedEq, parts.2.2]

private theorem header_child_unique
    {fuel : Nat} {context : SourceInference.Context} {source : Syntax.ForItem}
    {initial : State} {result : ForItemForm × State}
    (receipt : LocalHeaderRequirementTiming.Receipt fuel context source initial result)
    {child : CallIndex}
    (step : ChildStep (.forItem (fuel + 1) context source initial result.1 result.2) child) :
    child = .expression fuel context receipt.initializer receipt.expected initial receipt.value receipt.ready := by
  cases step
  all_goals have syntaxForm := receipt.form
  all_goals try solve | simp_all
  rename_i name sourceType initializer childExpected value childFinal annotated form child accepted
  have parts : receipt.name = name ∧ receipt.annotation = sourceType ∧ receipt.initializer = initializer := by
    simpa only [receipt.form, Syntax.ForItemValue.letDecl.injEq, Option.some.injEq] using form
  have actualAnnotation := annotationExpected_of_receipt receipt.annotationAccepted
  rw [← parts.2.1] at annotated
  have expectedEq := annotation_unique actualAnnotation annotated
  have actualChild := receipt.child
  rw [expectedEq, parts.2.2] at actualChild
  cases Except.ok.inj (actualChild.symm.trans child)
  simp only [expectedEq, parts.2.2]

theorem Site.initializer_child {call : CallIndex} {binder : TypedBinder} {initializer : ExpressionId}
    (site : Site call binder initializer) (accepted : call.Accepted) :
    ∃ child, ChildStep call child ∧
      (∀ other, ChildStep call other → other = child) ∧
      ∀ q ∈ binder.scheme.quantified,
        ∃ type ∈ child.outputTypes, q ∈ (child.final.resolve type).freeVariables := by
  cases site with
  | statement receipt =>
      refine ⟨_, statement_initializer_child receipt accepted, ?_, ?_⟩
      · intro other step
        exact statement_child_unique receipt step
      · intro q member
        exact ⟨receipt.value.type, List.mem_singleton_self _, (List.mem_filter.mp member).1⟩
  | header receipt =>
      refine ⟨_, header_initializer_child receipt accepted, ?_, ?_⟩
      · intro other step
        exact header_child_unique receipt step
      · intro q member
        exact ⟨receipt.value.type, List.mem_singleton_self _, (List.mem_filter.mp member).1⟩

end Solcore.SourceSemantics.SourceInferenceExecution.ActualGeneralization
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceActualOtherTemplateBacking
/-! Raw template witnesses at actual recursive checker entries. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceExecution.ActualTemplateBacking
open Frontend SourceInference TypeSystem Detail SourceInferenceSoundness.ProtectedVariables

theorem expressions_head
      {fuel : Nat} {context : SourceInference.Context}
      {source : Syntax.Expr} {sources : List Syntax.Expr}
      {initial middle final : State} {value : InferredExpression}
      {values : List InferredExpression}
      (accepted : (CallIndex.expressions (fuel + 1) context (source :: sources)
        initial values final).Accepted)
      (head : inferExprFuel fuel context source none initial = .ok (value, middle))
      (inputs : (CallIndex.expressions (fuel + 1) context (source :: sources) initial values final).Inputs)
      (backed : LiveTemplatesBacked initial) : LiveTemplatesBacked (CallIndex.expression fuel context source none initial value middle).initial := by
  have step : ChildStep (CallIndex.expressions (fuel + 1) context (source :: sources) initial values final) (CallIndex.expression fuel context source none initial value middle) := .expressions_head accepted head
  have childInputs := step.inputs inputs
  exact backed

theorem statements_head
      {fuel : Nat} {context : SourceInference.Context}
      {source : Syntax.Statement} {sources : List Syntax.Statement} {expectedReturn : Ty}
      {initial : State} {result : BlockResult} {head : StatementResult}
      (accepted : (CallIndex.statements (fuel + 1) context (source :: sources) expectedReturn initial result).Accepted)

      (child : (CallIndex.statement fuel context source expectedReturn initial head).Accepted)
      (inputs : (CallIndex.statements (fuel + 1) context (source :: sources) expectedReturn initial result).Inputs)
      (backed : LiveTemplatesBacked initial) : LiveTemplatesBacked (CallIndex.statement fuel context source expectedReturn initial head).initial := by
  have step : ChildStep (CallIndex.statements (fuel + 1) context (source :: sources) expectedReturn initial result) (CallIndex.statement fuel context source expectedReturn initial head) := .statements_head accepted child
  have childInputs := step.inputs inputs
  exact backed

theorem forItems_head
      {fuel : Nat} {context : SourceInference.Context}
      {source : Syntax.ForItem} {sources : List Syntax.ForItem} {initial final : State}
      {result : InferredForItems} {value : ForItemForm}
      (accepted : (CallIndex.forItems fuel context (source :: sources) initial result).Accepted)

      (child : (CallIndex.forItem fuel context source initial value final).Accepted)
      (inputs : (CallIndex.forItems fuel context (source :: sources) initial result).Inputs)
      (backed : LiveTemplatesBacked initial) : LiveTemplatesBacked (CallIndex.forItem fuel context source initial value final).initial := by
  have step : ChildStep (CallIndex.forItems fuel context (source :: sources) initial result) (CallIndex.forItem fuel context source initial value final) := .forItems_head accepted child
  have childInputs := step.inputs inputs
  exact backed

theorem forItem_initializer
      {fuel : Nat} {context : SourceInference.Context} {source : Syntax.ForItem}
      {initial final : State} {result : ForItemForm}
      {name : Syntax.Identifier} {sourceType : Option Syntax.TypeExpr} {initializer : Syntax.Expr}
      {expected : Option Ty} {value : InferredExpression} {childFinal : State}
      (accepted : (CallIndex.forItem (fuel + 1) context source initial result final).Accepted)
      (form : source.value = .letDecl name sourceType (some initializer))
      (annotation : AnnotationExpected context sourceType expected)
      (child : (CallIndex.expression fuel context initializer expected initial value childFinal).Accepted)
      (inputs : (CallIndex.forItem (fuel + 1) context source initial result final).Inputs)
      (backed : LiveTemplatesBacked initial) : LiveTemplatesBacked (CallIndex.expression fuel context initializer expected initial value childFinal).initial := by
  have step : ChildStep (CallIndex.forItem (fuel + 1) context source initial result final) (CallIndex.expression fuel context initializer expected initial value childFinal) := .forItem_initializer accepted form annotation child
  have childInputs := step.inputs inputs
  exact backed

theorem forItem_expression
      {fuel : Nat} {context : SourceInference.Context} {source : Syntax.ForItem}
      {initial final : State} {result : ForItemForm}
      {value : Syntax.Expr} {inferred : InferredExpression} {childFinal : State}
      (accepted : (CallIndex.forItem (fuel + 1) context source initial result final).Accepted)
      (form : source.value = .expression value)
      (child : (CallIndex.expression fuel context value none initial inferred childFinal).Accepted)
      (inputs : (CallIndex.forItem (fuel + 1) context source initial result final).Inputs)
      (backed : LiveTemplatesBacked initial) : LiveTemplatesBacked (CallIndex.expression fuel context value none initial inferred childFinal).initial := by
  have step : ChildStep (CallIndex.forItem (fuel + 1) context source initial result final) (CallIndex.expression fuel context value none initial inferred childFinal) := .forItem_expression accepted form child
  have childInputs := step.inputs inputs
  exact backed

theorem forItem_assignment
      {fuel : Nat} {context : SourceInference.Context} {source : Syntax.ForItem}
      {initial final : State} {result : ForItemForm}
      {target value : Syntax.Expr} {operator : Syntax.Located Syntax.ValueAssignOp}
      {assignment : AssignmentResolution} {inferred : InferredExpression} {childFinal : State}
      (accepted : (CallIndex.forItem (fuel + 1) context source initial result final).Accepted)
      (form : source.value = .assignValue target operator value)
      (child : (CallIndex.assignedValue fuel context target operator.value value initial assignment inferred childFinal).Accepted)
      (inputs : (CallIndex.forItem (fuel + 1) context source initial result final).Inputs)
      (backed : LiveTemplatesBacked initial) : LiveTemplatesBacked (CallIndex.assignedValue fuel context target operator.value value initial assignment inferred childFinal).initial := by
  have step : ChildStep (CallIndex.forItem (fuel + 1) context source initial result final) (CallIndex.assignedValue fuel context target operator.value value initial assignment inferred childFinal) := .forItem_assignment accepted form child
  have childInputs := step.inputs inputs
  exact backed

theorem forItem_bitnot
      {fuel : Nat} {context : SourceInference.Context} {source : Syntax.ForItem}
      {initial final : State} {result : ForItemForm}
      {target : Syntax.Expr} {operator : Syntax.SourceSpan} {place : PlaceResolution} {childFinal : State}
      (accepted : (CallIndex.forItem (fuel + 1) context source initial result final).Accepted)
      (form : source.value = .assignBitNot target operator)
      (child : (CallIndex.place fuel context target initial place childFinal).Accepted)
      (inputs : (CallIndex.forItem (fuel + 1) context source initial result final).Inputs)
      (backed : LiveTemplatesBacked initial) : LiveTemplatesBacked (CallIndex.place fuel context target initial place childFinal).initial := by
  have step : ChildStep (CallIndex.forItem (fuel + 1) context source initial result final) (CallIndex.place fuel context target initial place childFinal) := .forItem_bitnot accepted form child
  have childInputs := step.inputs inputs
  exact backed

theorem assignedValue_place
      {fuel : Nat} {context : SourceInference.Context} {target value : Syntax.Expr}
      {operator : Syntax.ValueAssignOp} {initial final targetState : State}
      {assignment : AssignmentResolution} {inferred : InferredExpression} {place : PlaceResolution}
      (accepted : (CallIndex.assignedValue fuel context target operator value initial assignment inferred final).Accepted)

      (child : (CallIndex.place fuel context target initial place targetState).Accepted)
      (inputs : (CallIndex.assignedValue fuel context target operator value initial assignment inferred final).Inputs)
      (backed : LiveTemplatesBacked initial) : LiveTemplatesBacked (CallIndex.place fuel context target initial place targetState).initial := by
  have step : ChildStep (CallIndex.assignedValue fuel context target operator value initial assignment inferred final) (CallIndex.place fuel context target initial place targetState) := .assignedValue_place accepted child
  have childInputs := step.inputs inputs
  exact backed

theorem place_group
      {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Expr}
      {initial final : State} {result : PlaceResolution}
      {inner : Syntax.Expr} {value : PlaceResolution} {childFinal : State}
      (accepted : (CallIndex.place (fuel + 1) context source initial result final).Accepted)
      (form : source.value = .group inner)
      (child : (CallIndex.place fuel context inner initial value childFinal).Accepted)
      (inputs : (CallIndex.place (fuel + 1) context source initial result final).Inputs)
      (backed : LiveTemplatesBacked initial) : LiveTemplatesBacked (CallIndex.place fuel context inner initial value childFinal).initial := by
  have step : ChildStep (CallIndex.place (fuel + 1) context source initial result final) (CallIndex.place fuel context inner initial value childFinal) := .place_group accepted form child
  have childInputs := step.inputs inputs
  exact backed

theorem place_index_base
      {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Expr}
      {initial final : State} {result : PlaceResolution}
      {base key : Syntax.Expr} {brackets : Syntax.SourceSpan} {value : PlaceResolution} {childFinal : State}
      (accepted : (CallIndex.place (fuel + 1) context source initial result final).Accepted)
      (form : source.value = .index base brackets key)
      (child : (CallIndex.place fuel context base initial value childFinal).Accepted)
      (inputs : (CallIndex.place (fuel + 1) context source initial result final).Inputs)
      (backed : LiveTemplatesBacked initial) : LiveTemplatesBacked (CallIndex.place fuel context base initial value childFinal).initial := by
  have step : ChildStep (CallIndex.place (fuel + 1) context source initial result final) (CallIndex.place fuel context base initial value childFinal) := .place_index_base accepted form child
  have childInputs := step.inputs inputs
  exact backed

theorem constructorArguments_head
      {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Expr} {sources : List Syntax.Expr}
      {expected : Ty} {expectedTypes : List Ty} {initial middle final : State}
      {values : List InferredExpression} {value : InferredExpression}
      (accepted : (CallIndex.constructorArguments fuel context (source :: sources) (expected :: expectedTypes) initial values final).Accepted)

      (child : (CallIndex.expression fuel context source (some (initial.resolve expected)) initial value middle).Accepted)
      (inputs : (CallIndex.constructorArguments fuel context (source :: sources) (expected :: expectedTypes) initial values final).Inputs)
      (backed : LiveTemplatesBacked initial) : LiveTemplatesBacked (CallIndex.expression fuel context source (some (initial.resolve expected)) initial value middle).initial := by
  have step : ChildStep (CallIndex.constructorArguments fuel context (source :: sources) (expected :: expectedTypes) initial values final) (CallIndex.expression fuel context source (some (initial.resolve expected)) initial value middle) := .constructorArguments_head accepted child
  have childInputs := step.inputs inputs
  exact backed

theorem expressions_tail
      {fuel : Nat} {context : SourceInference.Context}
      {source : Syntax.Expr} {sources : List Syntax.Expr}
      {initial middle final tailFinal : State} {value : InferredExpression}
      {values tailValues : List InferredExpression}
      (accepted : (CallIndex.expressions (fuel + 1) context (source :: sources)
        initial values final).Accepted)
      (head : inferExprFuel fuel context source none initial = .ok (value, middle))
      (tail : inferExprsFuel fuel context sources middle = .ok (tailValues, tailFinal))
      (inputs : (CallIndex.expressions (fuel + 1) context (source :: sources) initial values final).Inputs)
      (backed : LiveTemplatesBacked initial) : LiveTemplatesBacked (CallIndex.expressions fuel context sources middle tailValues tailFinal).initial := by
  have step : ChildStep (CallIndex.expressions (fuel + 1) context (source :: sources) initial values final) (CallIndex.expressions fuel context sources middle tailValues tailFinal) := .expressions_tail accepted head tail
  have childInputs := step.inputs inputs
  have before := ChildStep.inputs inputs (.expressions_head accepted head)
  exact expression before backed head

theorem statements_tail
      {fuel : Nat} {context : SourceInference.Context}
      {source : Syntax.Statement} {sources : List Syntax.Statement} {expectedReturn : Ty}
      {initial : State} {result tail : BlockResult} {head : StatementResult}
      (accepted : (CallIndex.statements (fuel + 1) context (source :: sources) expectedReturn initial result).Accepted)
      (nonempty : sources ≠ [])
      (headAccepted : inferStatementFuel fuel context source expectedReturn initial = .ok head)
      (child : (CallIndex.statements fuel context sources expectedReturn head.state tail).Accepted)
      (inputs : (CallIndex.statements (fuel + 1) context (source :: sources) expectedReturn initial result).Inputs)
      (backed : LiveTemplatesBacked initial) : LiveTemplatesBacked (CallIndex.statements fuel context sources expectedReturn head.state tail).initial := by
  have step : ChildStep (CallIndex.statements (fuel + 1) context (source :: sources) expectedReturn initial result) (CallIndex.statements fuel context sources expectedReturn head.state tail) := .statements_tail accepted nonempty headAccepted child
  have childInputs := step.inputs inputs
  have before := ChildStep.inputs inputs (.statements_head accepted headAccepted)
  exact statement before backed headAccepted

theorem forItems_tail
      {fuel : Nat} {context : SourceInference.Context}
      {source : Syntax.ForItem} {sources : List Syntax.ForItem} {initial middle : State}
      {result tail : InferredForItems} {head : ForItemForm}
      (accepted : (CallIndex.forItems fuel context (source :: sources) initial result).Accepted)
      (headAccepted : inferForItemFuel fuel context source initial = .ok (head, middle))
      (child : (CallIndex.forItems fuel context sources middle tail).Accepted)
      (inputs : (CallIndex.forItems fuel context (source :: sources) initial result).Inputs)
      (backed : LiveTemplatesBacked initial) : LiveTemplatesBacked (CallIndex.forItems fuel context sources middle tail).initial := by
  have step : ChildStep (CallIndex.forItems fuel context (source :: sources) initial result) (CallIndex.forItems fuel context sources middle tail) := .forItems_tail accepted headAccepted child
  have childInputs := step.inputs inputs
  have before := ChildStep.inputs inputs (.forItems_head accepted headAccepted)
  exact forItem before backed headAccepted

theorem constructorArguments_tail
      {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Expr} {sources : List Syntax.Expr}
      {expected : Ty} {expectedTypes : List Ty} {initial middle final : State}
      {values : List InferredExpression} {value : InferredExpression}
      {tailValues : List InferredExpression} {tailFinal : State}
      (accepted : (CallIndex.constructorArguments fuel context (source :: sources) (expected :: expectedTypes) initial values final).Accepted)
      (headAccepted : inferExprFuel fuel context source (some (initial.resolve expected)) initial = .ok (value, middle))
      (child : (CallIndex.constructorArguments fuel context sources expectedTypes middle tailValues tailFinal).Accepted)
      (inputs : (CallIndex.constructorArguments fuel context (source :: sources) (expected :: expectedTypes) initial values final).Inputs)
      (backed : LiveTemplatesBacked initial) : LiveTemplatesBacked (CallIndex.constructorArguments fuel context sources expectedTypes middle tailValues tailFinal).initial := by
  have step : ChildStep (CallIndex.constructorArguments fuel context (source :: sources) (expected :: expectedTypes) initial values final) (CallIndex.constructorArguments fuel context sources expectedTypes middle tailValues tailFinal) := .constructorArguments_tail accepted headAccepted child
  have childInputs := step.inputs inputs
  have before := ChildStep.inputs inputs (.constructorArguments_head accepted headAccepted)
  exact expression before backed headAccepted

theorem assignedValue_value
      {fuel : Nat} {context : SourceInference.Context} {target value : Syntax.Expr}
      {operator : Syntax.ValueAssignOp} {initial final targetState : State}
      {assignment : AssignmentResolution} {inferred : InferredExpression} {place : PlaceResolution}
      {fitted childFinal : State} {childValue : InferredExpression}
      (accepted : (CallIndex.assignedValue fuel context target operator value initial assignment inferred final).Accepted)
      (targetAccepted : inferPlaceFuel fuel context target initial = .ok (place, targetState))
      (fitting : (match operator with | .equal => pure targetState | _ => unify targetState place.type .word) = (Except.ok fitted : Except Error State))
      (child : (CallIndex.expression fuel context value (some (assignmentExpected operator fitted place.type)) fitted childValue childFinal).Accepted)
      (inputs : (CallIndex.assignedValue fuel context target operator value initial assignment inferred final).Inputs)
      (backed : LiveTemplatesBacked initial) : LiveTemplatesBacked (CallIndex.expression fuel context value (some (assignmentExpected operator fitted place.type)) fitted childValue childFinal).initial := by
  have step : ChildStep (CallIndex.assignedValue fuel context target operator value initial assignment inferred final) (CallIndex.expression fuel context value (some (assignmentExpected operator fitted place.type)) fitted childValue childFinal) := .assignedValue_value accepted targetAccepted fitting child
  have childInputs := step.inputs inputs
  have before := ChildStep.inputs inputs (.assignedValue_place accepted targetAccepted)
  have targetBacked := ActualTemplateBacking.place before backed targetAccepted
  have targetReady := (before.progress targetAccepted).2.1
  cases operator <;> first
  | (change Except.ok targetState = Except.ok fitted at fitting
     cases Except.ok.inj fitting
     exact targetBacked)
  | exact targetBacked.unify targetReady.solved fitting

theorem place_index_key
      {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Expr}
      {initial final : State} {result : PlaceResolution}
      {base key : Syntax.Expr} {brackets : Syntax.SourceSpan} {baseValue : PlaceResolution}
      {baseState keyState valueState fitted childFinal : State} {keyType valueType : Ty}
      {keyValue : InferredExpression}
      (accepted : (CallIndex.place (fuel + 1) context source initial result final).Accepted)
      (form : source.value = .index base brackets key)
      (baseAccepted : inferPlaceFuel fuel context base initial = .ok (baseValue, baseState))
      (keyFresh : baseState.fresh = (keyType, keyState))
      (valueFresh : keyState.fresh = (valueType, valueState))
      (fitting : unify valueState baseValue.type (.mapping keyType valueType) = .ok fitted)
      (child : (CallIndex.expression fuel context key (some (fitted.resolve keyType)) fitted keyValue childFinal).Accepted)
      (inputs : (CallIndex.place (fuel + 1) context source initial result final).Inputs)
      (backed : LiveTemplatesBacked initial) : LiveTemplatesBacked (CallIndex.expression fuel context key (some (fitted.resolve keyType)) fitted keyValue childFinal).initial := by
  have step : ChildStep (CallIndex.place (fuel + 1) context source initial result final) (CallIndex.expression fuel context key (some (fitted.resolve keyType)) fitted keyValue childFinal) := .place_index_key accepted form baseAccepted keyFresh valueFresh fitting child
  have childInputs := step.inputs inputs
  have before := ChildStep.inputs inputs (.place_index_base accepted form baseAccepted)
  have baseBacked := place before backed baseAccepted
  have baseReady := (before.progress baseAccepted).2.1
  have sameKey : keyState = baseState.fresh.2 := (congrArg Prod.snd keyFresh).symm
  subst keyState
  have sameValue : valueState = baseState.fresh.2.fresh.2 := (congrArg Prod.snd valueFresh).symm
  subst valueState
  exact baseBacked.fresh.fresh.unify baseReady.fresh.fresh.solved fitting

theorem constructorApplication_arguments
      {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Expr} {id : ExpressionId}
      {instantiation : DataConstructorInstantiation} {sources : List Syntax.Expr} {expected : Option Ty}
      {initial fitted final childFinal : State} {value : InferredExpression} {values : List InferredExpression}
      (accepted : (CallIndex.constructorApplication fuel context source id instantiation sources expected initial value final).Accepted)
      (arity : sources.length = instantiation.payloadTypes.length)
      (fitting : (match expected with | none => pure initial | some type => unify initial instantiation.resultType type) = (Except.ok fitted : Except Error State))
      (child : (CallIndex.constructorArguments fuel context sources instantiation.payloadTypes fitted values childFinal).Accepted)
      (inputs : (CallIndex.constructorApplication fuel context source id instantiation sources expected initial value final).Inputs)
      (backed : LiveTemplatesBacked initial) : LiveTemplatesBacked (CallIndex.constructorArguments fuel context sources instantiation.payloadTypes fitted values childFinal).initial := by
  have step : ChildStep (CallIndex.constructorApplication fuel context source id instantiation sources expected initial value final) (CallIndex.constructorArguments fuel context sources instantiation.payloadTypes fitted values childFinal) := .constructorApplication_arguments accepted arity fitting child
  have childInputs := step.inputs inputs
  cases expected with
  | none =>
    change Except.ok initial = Except.ok fitted at fitting
    cases Except.ok.inj fitting
    exact backed
  | some type => exact backed.unify inputs.ready.solved fitting

theorem matchCases_body
      {fuel : Nat} {context : SourceInference.Context} {scrutineeType expectedReturn : Ty}
      {saved : LexicalScope} {arm : Syntax.MatchCase} {arms : List Syntax.MatchCase}
      {initial patternState : State} {pattern : TypedMatchPattern} {result : MatchCasesResult}
      {body : BlockResult}
      (accepted : (CallIndex.matchCases (fuel + 1) context scrutineeType expectedReturn saved (arm :: arms) initial result).Accepted)
      (patternAccepted : inferMatchPatternFuel fuel context arm.value.pattern scrutineeType initial = .ok (pattern, patternState))
      (child : (CallIndex.statements fuel context arm.value.body.value expectedReturn patternState body).Accepted)
      (inputs : (CallIndex.matchCases (fuel + 1) context scrutineeType expectedReturn saved (arm :: arms) initial result).Inputs)
      (backed : LiveTemplatesBacked initial) : LiveTemplatesBacked (CallIndex.statements fuel context arm.value.body.value expectedReturn patternState body).initial := by
  have step : ChildStep (CallIndex.matchCases (fuel + 1) context scrutineeType expectedReturn saved (arm :: arms) initial result) (CallIndex.statements fuel context arm.value.body.value expectedReturn patternState body) := .matchCases_body accepted patternAccepted child
  have childInputs := step.inputs inputs
  have progress := inferMatchPatternFuel_inferenceProperties inputs.ready inputs.bounds.1 inputs.catalog.formation patternAccepted
  exact (inferMatchPatternFuel_scope patternAccepted).templates backed
    (inferMatchPatternFuel_requirements_subset patternAccepted) progress.1.substitution_extends

theorem matchCases_tail
      {fuel : Nat} {context : SourceInference.Context} {scrutineeType expectedReturn : Ty}
      {saved : LexicalScope} {arm : Syntax.MatchCase} {arms : List Syntax.MatchCase}
      {initial patternState : State} {pattern : TypedMatchPattern} {result : MatchCasesResult}
      {body : BlockResult}
      {tail : MatchCasesResult}
      (accepted : (CallIndex.matchCases (fuel + 1) context scrutineeType expectedReturn saved (arm :: arms) initial result).Accepted)
      (patternAccepted : inferMatchPatternFuel fuel context arm.value.pattern scrutineeType initial = .ok (pattern, patternState))
      (bodyAccepted : inferStatementsFuel fuel context arm.value.body.value expectedReturn patternState = .ok body)
      (child : (CallIndex.matchCases fuel context scrutineeType expectedReturn saved arms (body.state.restoreLexicalScope saved) tail).Accepted)
      (inputs : (CallIndex.matchCases (fuel + 1) context scrutineeType expectedReturn saved (arm :: arms) initial result).Inputs)
      (backed : LiveTemplatesBacked initial) : LiveTemplatesBacked (CallIndex.matchCases fuel context scrutineeType expectedReturn saved arms (body.state.restoreLexicalScope saved) tail).initial := by
  have step : ChildStep (CallIndex.matchCases (fuel + 1) context scrutineeType expectedReturn saved (arm :: arms) initial result) (CallIndex.matchCases fuel context scrutineeType expectedReturn saved arms (body.state.restoreLexicalScope saved) tail) := .matchCases_tail accepted patternAccepted bodyAccepted child
  have childInputs := step.inputs inputs
  have patternProperties := inferMatchPatternFuel_inferenceProperties inputs.ready inputs.bounds.1 inputs.catalog.formation patternAccepted
  have bodyInputs := ChildStep.inputs inputs (.matchCases_body accepted patternAccepted bodyAccepted)
  have bodyProperties := bodyInputs.progress bodyAccepted
  have rows := List.Subset.trans (inferMatchPatternFuel_requirements_subset patternAccepted)
    (inferStatementsFuel_requirements_subset bodyAccepted)
  have result := backed.restore rows (patternProperties.1.trans bodyProperties.1).substitution_extends
  change LiveTemplatesBacked (body.state.restoreLexicalScope initial.lexicalScope) at result
  rw [inputs.bounds.2.2] at result
  exact result

end Solcore.SourceSemantics.SourceInferenceExecution.ActualTemplateBacking
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceActualStatementTemplateBacking
/-! Raw template witnesses at actual recursive checker entries. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceExecution.ActualTemplateBacking
open Frontend SourceInference TypeSystem Detail SourceInferenceSoundness.ProtectedVariables

theorem matchScrutinee_backed
    {fuel : Nat} {context : SourceInference.Context} {span : Syntax.SourceSpan}
    {sources : List Syntax.Expr} {initial : State} {result : InferredExpression × State}
    (backed : LiveTemplatesBacked initial) (ready : initial.InferenceReady)
    (catalog : LifetimeInferenceContext context)
    (accepted : matchScrutinee fuel context span sources initial = .ok result) :
    LiveTemplatesBacked result.2 := by
  unfold matchScrutinee at accepted
  split at accepted
  · exact backed.inferExprFuel ready catalog.formation catalog.canonical (by simp) accepted
  · cases run : inferExprsFuel fuel context sources initial with
    | error error => simp [run, bind, Except.bind] at accepted
    | ok pair =>
      obtain ⟨values, state⟩ := pair
      simp only [run, bind, Except.bind, pure, Pure.pure, Except.pure, Except.ok.injEq] at accepted
      cases accepted
      exact (backed.inferExprsFuel ready catalog run).allocateExpressionId.recordNode _

theorem statement_initializer
      {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Statement}
      {expectedReturn : Ty} {initial allocated : State} {id : StatementId}
      {result : StatementResult}
      {name : Syntax.Identifier} {sourceType : Option Syntax.TypeExpr} {initializer : Syntax.Expr}
      {expected : Option Ty} {value : InferredExpression} {final : State}
      (accepted : (CallIndex.statement (fuel + 1) context source expectedReturn initial result).Accepted)
      (form : source.value = .letDecl name sourceType (some initializer))
      (allocation : initial.allocateStatementId = (id, allocated))
      (annotation : AnnotationExpected context sourceType expected)
      (child : (CallIndex.expression fuel context initializer expected allocated value final).Accepted)
      (inputs : (CallIndex.statement (fuel + 1) context source expectedReturn initial result).Inputs)
      (backed : LiveTemplatesBacked initial) : LiveTemplatesBacked (CallIndex.expression fuel context initializer expected allocated value final).initial := by
  have step : ChildStep (CallIndex.statement (fuel + 1) context source expectedReturn initial result) (CallIndex.expression fuel context initializer expected allocated value final) := .statement_initializer accepted form allocation annotation child
  have childInputs := step.inputs inputs
  have same : allocated = initial.allocateStatementId.2 := (congrArg Prod.snd allocation).symm
  subst allocated
  exact backed.allocateStatementId

theorem statement_return
      {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Statement}
      {expectedReturn : Ty} {initial allocated : State} {id : StatementId}
      {result : StatementResult}
      {value : Syntax.Expr} {inferred : InferredExpression} {final : State}
      (accepted : (CallIndex.statement (fuel + 1) context source expectedReturn initial result).Accepted)
      (form : source.value = .returnStmt (some value))
      (allocation : initial.allocateStatementId = (id, allocated))
      (child : (CallIndex.expression fuel context value (some expectedReturn) allocated inferred final).Accepted)
      (inputs : (CallIndex.statement (fuel + 1) context source expectedReturn initial result).Inputs)
      (backed : LiveTemplatesBacked initial) : LiveTemplatesBacked (CallIndex.expression fuel context value (some expectedReturn) allocated inferred final).initial := by
  have step : ChildStep (CallIndex.statement (fuel + 1) context source expectedReturn initial result) (CallIndex.expression fuel context value (some expectedReturn) allocated inferred final) := .statement_return accepted form allocation child
  have childInputs := step.inputs inputs
  have same : allocated = initial.allocateStatementId.2 := (congrArg Prod.snd allocation).symm
  subst allocated
  exact backed.allocateStatementId

theorem statement_expression
      {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Statement}
      {expectedReturn : Ty} {initial allocated : State} {id : StatementId}
      {result : StatementResult}
      {value : Syntax.Expr} {semicolon : Bool} {inferred : InferredExpression} {final : State}
      (accepted : (CallIndex.statement (fuel + 1) context source expectedReturn initial result).Accepted)
      (form : source.value = .expression value semicolon)
      (allocation : initial.allocateStatementId = (id, allocated))
      (child : (CallIndex.expression fuel context value none allocated inferred final).Accepted)
      (inputs : (CallIndex.statement (fuel + 1) context source expectedReturn initial result).Inputs)
      (backed : LiveTemplatesBacked initial) : LiveTemplatesBacked (CallIndex.expression fuel context value none allocated inferred final).initial := by
  have step : ChildStep (CallIndex.statement (fuel + 1) context source expectedReturn initial result) (CallIndex.expression fuel context value none allocated inferred final) := .statement_expression accepted form allocation child
  have childInputs := step.inputs inputs
  have same : allocated = initial.allocateStatementId.2 := (congrArg Prod.snd allocation).symm
  subst allocated
  exact backed.allocateStatementId

theorem statement_block
      {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Statement}
      {expectedReturn : Ty} {initial allocated : State} {id : StatementId}
      {result : StatementResult}
      {body : List Syntax.Statement} {bodyResult : BlockResult}
      (accepted : (CallIndex.statement (fuel + 1) context source expectedReturn initial result).Accepted)
      (form : source.value = .block body)
      (allocation : initial.allocateStatementId = (id, allocated))
      (child : (CallIndex.statements fuel context body expectedReturn allocated bodyResult).Accepted)
      (inputs : (CallIndex.statement (fuel + 1) context source expectedReturn initial result).Inputs)
      (backed : LiveTemplatesBacked initial) : LiveTemplatesBacked (CallIndex.statements fuel context body expectedReturn allocated bodyResult).initial := by
  have step : ChildStep (CallIndex.statement (fuel + 1) context source expectedReturn initial result) (CallIndex.statements fuel context body expectedReturn allocated bodyResult) := .statement_block accepted form allocation child
  have childInputs := step.inputs inputs
  have same : allocated = initial.allocateStatementId.2 := (congrArg Prod.snd allocation).symm
  subst allocated
  exact backed.allocateStatementId

theorem statement_if_condition
      {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Statement}
      {expectedReturn : Ty} {initial allocated : State} {id : StatementId}
      {result : StatementResult}
      {condition : Syntax.Expr} {thenBody : Syntax.Block} {elseBody : Option Syntax.Block}
      {conditionValue : InferredExpression} {conditionState : State}
      (accepted : (CallIndex.statement (fuel + 1) context source expectedReturn initial result).Accepted)
      (form : source.value = .ifThen condition thenBody elseBody)
      (allocation : initial.allocateStatementId = (id, allocated))
      (child : (CallIndex.expression fuel context condition (some .bool) allocated conditionValue conditionState).Accepted)
      (inputs : (CallIndex.statement (fuel + 1) context source expectedReturn initial result).Inputs)
      (backed : LiveTemplatesBacked initial) : LiveTemplatesBacked (CallIndex.expression fuel context condition (some .bool) allocated conditionValue conditionState).initial := by
  have step : ChildStep (CallIndex.statement (fuel + 1) context source expectedReturn initial result) (CallIndex.expression fuel context condition (some .bool) allocated conditionValue conditionState) := .statement_if_condition accepted form allocation child
  have childInputs := step.inputs inputs
  have same : allocated = initial.allocateStatementId.2 := (congrArg Prod.snd allocation).symm
  subst allocated
  exact backed.allocateStatementId

theorem statement_assignment
      {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Statement}
      {expectedReturn : Ty} {initial allocated : State} {id : StatementId}
      {result : StatementResult}
      {target value : Syntax.Expr} {operator : Syntax.Located Syntax.ValueAssignOp}
      {assignment : AssignmentResolution} {inferred : InferredExpression} {final : State}
      (accepted : (CallIndex.statement (fuel + 1) context source expectedReturn initial result).Accepted)
      (form : source.value = .assignValue target operator value)
      (allocation : initial.allocateStatementId = (id, allocated))
      (child : (CallIndex.assignedValue fuel context target operator.value value allocated assignment inferred final).Accepted)
      (inputs : (CallIndex.statement (fuel + 1) context source expectedReturn initial result).Inputs)
      (backed : LiveTemplatesBacked initial) : LiveTemplatesBacked (CallIndex.assignedValue fuel context target operator.value value allocated assignment inferred final).initial := by
  have step : ChildStep (CallIndex.statement (fuel + 1) context source expectedReturn initial result) (CallIndex.assignedValue fuel context target operator.value value allocated assignment inferred final) := .statement_assignment accepted form allocation child
  have childInputs := step.inputs inputs
  have same : allocated = initial.allocateStatementId.2 := (congrArg Prod.snd allocation).symm
  subst allocated
  exact backed.allocateStatementId

theorem statement_bitnot
      {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Statement}
      {expectedReturn : Ty} {initial allocated : State} {id : StatementId}
      {result : StatementResult}
      {target : Syntax.Expr} {operator : Syntax.SourceSpan}
      {place : PlaceResolution} {final : State}
      (accepted : (CallIndex.statement (fuel + 1) context source expectedReturn initial result).Accepted)
      (form : source.value = .assignBitNot target operator)
      (allocation : initial.allocateStatementId = (id, allocated))
      (child : (CallIndex.place fuel context target allocated place final).Accepted)
      (inputs : (CallIndex.statement (fuel + 1) context source expectedReturn initial result).Inputs)
      (backed : LiveTemplatesBacked initial) : LiveTemplatesBacked (CallIndex.place fuel context target allocated place final).initial := by
  have step : ChildStep (CallIndex.statement (fuel + 1) context source expectedReturn initial result) (CallIndex.place fuel context target allocated place final) := .statement_bitnot accepted form allocation child
  have childInputs := step.inputs inputs
  have same : allocated = initial.allocateStatementId.2 := (congrArg Prod.snd allocation).symm
  subst allocated
  exact backed.allocateStatementId

theorem statement_while_condition
      {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Statement}
      {expectedReturn : Ty} {initial allocated : State} {id : StatementId}
      {result : StatementResult}
      {condition : Syntax.Expr} {body : Syntax.Block}
      {conditionValue : InferredExpression} {conditionState : State}
      (accepted : (CallIndex.statement (fuel + 1) context source expectedReturn initial result).Accepted)
      (form : source.value = .whileLoop condition body)
      (allocation : initial.allocateStatementId = (id, allocated))
      (child : (CallIndex.expression fuel context condition (some .bool) allocated conditionValue conditionState).Accepted)
      (inputs : (CallIndex.statement (fuel + 1) context source expectedReturn initial result).Inputs)
      (backed : LiveTemplatesBacked initial) : LiveTemplatesBacked (CallIndex.expression fuel context condition (some .bool) allocated conditionValue conditionState).initial := by
  have step : ChildStep (CallIndex.statement (fuel + 1) context source expectedReturn initial result) (CallIndex.expression fuel context condition (some .bool) allocated conditionValue conditionState) := .statement_while_condition accepted form allocation child
  have childInputs := step.inputs inputs
  have same : allocated = initial.allocateStatementId.2 := (congrArg Prod.snd allocation).symm
  subst allocated
  exact backed.allocateStatementId

theorem statement_for_initializer
      {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Statement}
      {expectedReturn : Ty} {initial allocated : State} {id : StatementId}
      {result : StatementResult}
      {span : Syntax.SourceSpan} {initializer post : List Syntax.ForItem}
      {condition : Syntax.Expr} {body : Syntax.Block} {initialized : InferredForItems}
      (accepted : (CallIndex.statement (fuel + 1) context source expectedReturn initial result).Accepted)
      (form : source.value = .forLoop span initializer condition post body)
      (allocation : initial.allocateStatementId = (id, allocated))
      (child : (CallIndex.forItems fuel context initializer allocated initialized).Accepted)
      (inputs : (CallIndex.statement (fuel + 1) context source expectedReturn initial result).Inputs)
      (backed : LiveTemplatesBacked initial) : LiveTemplatesBacked (CallIndex.forItems fuel context initializer allocated initialized).initial := by
  have step : ChildStep (CallIndex.statement (fuel + 1) context source expectedReturn initial result) (CallIndex.forItems fuel context initializer allocated initialized) := .statement_for_initializer accepted form allocation child
  have childInputs := step.inputs inputs
  have same : allocated = initial.allocateStatementId.2 := (congrArg Prod.snd allocation).symm
  subst allocated
  exact backed.allocateStatementId

theorem statement_match_single
      {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Statement}
      {expectedReturn : Ty} {initial allocated : State} {id : StatementId}
      {result : StatementResult} {scrutinees : Syntax.NonemptyDelimitedList Syntax.Expr}
      {arms : Syntax.MatchArms}
      {scrutinee : Syntax.Expr} {value : InferredExpression} {childFinal : State}
      (accepted : (CallIndex.statement (fuel + 1) context source expectedReturn initial result).Accepted)
      (form : source.value = .matchWith scrutinees arms)
      (allocation : initial.allocateStatementId = (id, allocated))
      (single : scrutinees.elements.toList = [scrutinee])
      (child : (CallIndex.expression fuel context scrutinee none allocated value childFinal).Accepted)
      (inputs : (CallIndex.statement (fuel + 1) context source expectedReturn initial result).Inputs)
      (backed : LiveTemplatesBacked initial) : LiveTemplatesBacked (CallIndex.expression fuel context scrutinee none allocated value childFinal).initial := by
  have step : ChildStep (CallIndex.statement (fuel + 1) context source expectedReturn initial result) (CallIndex.expression fuel context scrutinee none allocated value childFinal) := .statement_match_single accepted form allocation single child
  have childInputs := step.inputs inputs
  have same : allocated = initial.allocateStatementId.2 := (congrArg Prod.snd allocation).symm
  subst allocated
  exact backed.allocateStatementId

theorem statement_match_many
      {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Statement}
      {expectedReturn : Ty} {initial allocated : State} {id : StatementId}
      {result : StatementResult} {scrutinees : Syntax.NonemptyDelimitedList Syntax.Expr}
      {arms : Syntax.MatchArms}
      {values : List InferredExpression} {childFinal : State}
      (accepted : (CallIndex.statement (fuel + 1) context source expectedReturn initial result).Accepted)
      (form : source.value = .matchWith scrutinees arms)
      (allocation : initial.allocateStatementId = (id, allocated))
      (multiple : ∀ scrutinee, scrutinees.elements.toList ≠ [scrutinee])
      (child : (CallIndex.expressions fuel context scrutinees.elements.toList allocated values childFinal).Accepted)
      (inputs : (CallIndex.statement (fuel + 1) context source expectedReturn initial result).Inputs)
      (backed : LiveTemplatesBacked initial) : LiveTemplatesBacked (CallIndex.expressions fuel context scrutinees.elements.toList allocated values childFinal).initial := by
  have step : ChildStep (CallIndex.statement (fuel + 1) context source expectedReturn initial result) (CallIndex.expressions fuel context scrutinees.elements.toList allocated values childFinal) := .statement_match_many accepted form allocation multiple child
  have childInputs := step.inputs inputs
  have same : allocated = initial.allocateStatementId.2 := (congrArg Prod.snd allocation).symm
  subst allocated
  exact backed.allocateStatementId

theorem statement_if_then
      {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Statement}
      {expectedReturn : Ty} {initial allocated : State} {id : StatementId}
      {result : StatementResult}
      {condition : Syntax.Expr} {thenBody : Syntax.Block} {elseBody : Option Syntax.Block}
      {conditionValue : InferredExpression} {conditionState : State}
      {thenResult : BlockResult}
      (accepted : (CallIndex.statement (fuel + 1) context source expectedReturn initial result).Accepted)
      (form : source.value = .ifThen condition thenBody elseBody)
      (allocation : initial.allocateStatementId = (id, allocated))
      (conditionAccepted : inferExprFuel fuel context condition (some .bool) allocated = .ok (conditionValue, conditionState))
      (child : (CallIndex.statements fuel context thenBody.value expectedReturn conditionState thenResult).Accepted)
      (inputs : (CallIndex.statement (fuel + 1) context source expectedReturn initial result).Inputs)
      (backed : LiveTemplatesBacked initial) : LiveTemplatesBacked (CallIndex.statements fuel context thenBody.value expectedReturn conditionState thenResult).initial := by
  have step : ChildStep (CallIndex.statement (fuel + 1) context source expectedReturn initial result) (CallIndex.statements fuel context thenBody.value expectedReturn conditionState thenResult) := .statement_if_then accepted form allocation conditionAccepted child
  have childInputs := step.inputs inputs
  have same : allocated = initial.allocateStatementId.2 := (congrArg Prod.snd allocation).symm
  subst allocated
  have before := ChildStep.inputs inputs (.statement_if_condition accepted form allocation conditionAccepted)
  exact expression before backed.allocateStatementId conditionAccepted

theorem statement_if_else
      {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Statement}
      {expectedReturn : Ty} {initial allocated : State} {id : StatementId}
      {result : StatementResult}
      {condition : Syntax.Expr} {thenBody : Syntax.Block} {elseBody : Option Syntax.Block}
      {conditionValue : InferredExpression} {conditionState : State}
      {body : Syntax.Block} {thenResult elseResult : BlockResult}
      (accepted : (CallIndex.statement (fuel + 1) context source expectedReturn initial result).Accepted)
      (form : source.value = .ifThen condition thenBody elseBody)
      (allocation : initial.allocateStatementId = (id, allocated))
      (conditionAccepted : inferExprFuel fuel context condition (some .bool) allocated = .ok (conditionValue, conditionState))
      (hasElse : elseBody = some body)
      (thenAccepted : inferStatementsFuel fuel context thenBody.value expectedReturn conditionState = .ok thenResult)
      (child : (CallIndex.statements fuel context body.value expectedReturn (thenResult.state.restoreLexicalScope conditionState.lexicalScope) elseResult).Accepted)
      (inputs : (CallIndex.statement (fuel + 1) context source expectedReturn initial result).Inputs)
      (backed : LiveTemplatesBacked initial) : LiveTemplatesBacked (CallIndex.statements fuel context body.value expectedReturn (thenResult.state.restoreLexicalScope conditionState.lexicalScope) elseResult).initial := by
  have step : ChildStep (CallIndex.statement (fuel + 1) context source expectedReturn initial result) (CallIndex.statements fuel context body.value expectedReturn (thenResult.state.restoreLexicalScope conditionState.lexicalScope) elseResult) := .statement_if_else accepted form allocation conditionAccepted hasElse thenAccepted child
  have childInputs := step.inputs inputs
  have same : allocated = initial.allocateStatementId.2 := (congrArg Prod.snd allocation).symm
  subst allocated
  have before := ChildStep.inputs inputs (.statement_if_condition accepted form allocation conditionAccepted)
  have conditionBacked := expression before backed.allocateStatementId conditionAccepted
  have thenInputs := ChildStep.inputs inputs (.statement_if_then accepted form allocation conditionAccepted thenAccepted)
  exact conditionBacked.restore (inferStatementsFuel_requirements_subset thenAccepted)
    (thenInputs.progress thenAccepted).1.substitution_extends

theorem statement_while_body
      {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Statement}
      {expectedReturn : Ty} {initial allocated : State} {id : StatementId}
      {result : StatementResult}
      {condition : Syntax.Expr} {body : Syntax.Block}
      {conditionValue : InferredExpression} {conditionState : State}
      {bodyResult : BlockResult}
      (accepted : (CallIndex.statement (fuel + 1) context source expectedReturn initial result).Accepted)
      (form : source.value = .whileLoop condition body)
      (allocation : initial.allocateStatementId = (id, allocated))
      (conditionAccepted : inferExprFuel fuel context condition (some .bool) allocated = .ok (conditionValue, conditionState))
      (child : (CallIndex.statements fuel { context with loopDepth := context.loopDepth + 1 } body.value expectedReturn conditionState bodyResult).Accepted)
      (inputs : (CallIndex.statement (fuel + 1) context source expectedReturn initial result).Inputs)
      (backed : LiveTemplatesBacked initial) : LiveTemplatesBacked (CallIndex.statements fuel { context with loopDepth := context.loopDepth + 1 } body.value expectedReturn conditionState bodyResult).initial := by
  have step : ChildStep (CallIndex.statement (fuel + 1) context source expectedReturn initial result) (CallIndex.statements fuel { context with loopDepth := context.loopDepth + 1 } body.value expectedReturn conditionState bodyResult) := .statement_while_body accepted form allocation conditionAccepted child
  have childInputs := step.inputs inputs
  have same : allocated = initial.allocateStatementId.2 := (congrArg Prod.snd allocation).symm
  subst allocated
  have before := ChildStep.inputs inputs (.statement_while_condition accepted form allocation conditionAccepted)
  exact expression before backed.allocateStatementId conditionAccepted

theorem statement_for_condition
      {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Statement}
      {expectedReturn : Ty} {initial allocated : State} {id : StatementId}
      {result : StatementResult}
      {span : Syntax.SourceSpan} {initializer post : List Syntax.ForItem}
      {condition : Syntax.Expr} {body : Syntax.Block} {initialized : InferredForItems}
      {conditionValue : InferredExpression} {conditionState : State}
      (accepted : (CallIndex.statement (fuel + 1) context source expectedReturn initial result).Accepted)
      (form : source.value = .forLoop span initializer condition post body)
      (allocation : initial.allocateStatementId = (id, allocated))
      (initializerAccepted : inferForItemsFuel fuel context initializer allocated = .ok initialized)
      (child : (CallIndex.expression fuel context condition (some .bool) initialized.state conditionValue conditionState).Accepted)
      (inputs : (CallIndex.statement (fuel + 1) context source expectedReturn initial result).Inputs)
      (backed : LiveTemplatesBacked initial) : LiveTemplatesBacked (CallIndex.expression fuel context condition (some .bool) initialized.state conditionValue conditionState).initial := by
  have step : ChildStep (CallIndex.statement (fuel + 1) context source expectedReturn initial result) (CallIndex.expression fuel context condition (some .bool) initialized.state conditionValue conditionState) := .statement_for_condition accepted form allocation initializerAccepted child
  have childInputs := step.inputs inputs
  have same : allocated = initial.allocateStatementId.2 := (congrArg Prod.snd allocation).symm
  subst allocated
  have before := ChildStep.inputs inputs (.statement_for_initializer accepted form allocation initializerAccepted)
  exact forItems before backed.allocateStatementId initializerAccepted

theorem statement_for_body
      {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Statement}
      {expectedReturn : Ty} {initial allocated : State} {id : StatementId}
      {result : StatementResult}
      {span : Syntax.SourceSpan} {initializer post : List Syntax.ForItem}
      {condition : Syntax.Expr} {body : Syntax.Block} {initialized : InferredForItems}
      {conditionValue : InferredExpression} {conditionState : State} {bodyResult : BlockResult}
      (accepted : (CallIndex.statement (fuel + 1) context source expectedReturn initial result).Accepted)
      (form : source.value = .forLoop span initializer condition post body)
      (allocation : initial.allocateStatementId = (id, allocated))
      (initializerAccepted : inferForItemsFuel fuel context initializer allocated = .ok initialized)
      (conditionAccepted : inferExprFuel fuel context condition (some .bool) initialized.state = .ok (conditionValue, conditionState))
      (child : (CallIndex.statements fuel { context with loopDepth := context.loopDepth + 1 } body.value expectedReturn conditionState bodyResult).Accepted)
      (inputs : (CallIndex.statement (fuel + 1) context source expectedReturn initial result).Inputs)
      (backed : LiveTemplatesBacked initial) : LiveTemplatesBacked (CallIndex.statements fuel { context with loopDepth := context.loopDepth + 1 } body.value expectedReturn conditionState bodyResult).initial := by
  have step : ChildStep (CallIndex.statement (fuel + 1) context source expectedReturn initial result) (CallIndex.statements fuel { context with loopDepth := context.loopDepth + 1 } body.value expectedReturn conditionState bodyResult) := .statement_for_body accepted form allocation initializerAccepted conditionAccepted child
  have childInputs := step.inputs inputs
  have same : allocated = initial.allocateStatementId.2 := (congrArg Prod.snd allocation).symm
  subst allocated
  have first := ChildStep.inputs inputs (.statement_for_initializer accepted form allocation initializerAccepted)
  have second := ChildStep.inputs inputs (.statement_for_condition accepted form allocation initializerAccepted conditionAccepted)
  exact expression second (forItems first backed.allocateStatementId initializerAccepted) conditionAccepted

theorem statement_for_post
      {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Statement}
      {expectedReturn : Ty} {initial allocated : State} {id : StatementId}
      {result : StatementResult}
      {span : Syntax.SourceSpan} {initializer post : List Syntax.ForItem}
      {condition : Syntax.Expr} {body : Syntax.Block} {initialized : InferredForItems}
      {conditionValue : InferredExpression} {conditionState : State} {bodyResult : BlockResult}
      {postResult : InferredForItems}
      (accepted : (CallIndex.statement (fuel + 1) context source expectedReturn initial result).Accepted)
      (form : source.value = .forLoop span initializer condition post body)
      (allocation : initial.allocateStatementId = (id, allocated))
      (initializerAccepted : inferForItemsFuel fuel context initializer allocated = .ok initialized)
      (conditionAccepted : inferExprFuel fuel context condition (some .bool) initialized.state = .ok (conditionValue, conditionState))
      (bodyAccepted : inferStatementsFuel fuel { context with loopDepth := context.loopDepth + 1 } body.value expectedReturn conditionState = .ok bodyResult)
      (child : (CallIndex.forItems fuel { context with loopDepth := context.loopDepth + 1 } post (bodyResult.state.restoreLexicalScope initialized.state.lexicalScope) postResult).Accepted)
      (inputs : (CallIndex.statement (fuel + 1) context source expectedReturn initial result).Inputs)
      (backed : LiveTemplatesBacked initial) : LiveTemplatesBacked (CallIndex.forItems fuel { context with loopDepth := context.loopDepth + 1 } post (bodyResult.state.restoreLexicalScope initialized.state.lexicalScope) postResult).initial := by
  have step : ChildStep (CallIndex.statement (fuel + 1) context source expectedReturn initial result) (CallIndex.forItems fuel { context with loopDepth := context.loopDepth + 1 } post (bodyResult.state.restoreLexicalScope initialized.state.lexicalScope) postResult) := .statement_for_post accepted form allocation initializerAccepted conditionAccepted bodyAccepted child
  have childInputs := step.inputs inputs
  have same : allocated = initial.allocateStatementId.2 := (congrArg Prod.snd allocation).symm
  subst allocated
  have first := ChildStep.inputs inputs (.statement_for_initializer accepted form allocation initializerAccepted)
  have second := ChildStep.inputs inputs (.statement_for_condition accepted form allocation initializerAccepted conditionAccepted)
  have third := ChildStep.inputs inputs (.statement_for_body accepted form allocation initializerAccepted conditionAccepted bodyAccepted)
  have initializerBacked := forItems first backed.allocateStatementId initializerAccepted
  have through := (second.progress conditionAccepted).1.trans (third.progress bodyAccepted).1
  exact initializerBacked.restore
    (List.Subset.trans (inferExprFuel_requirements_subset conditionAccepted) (inferStatementsFuel_requirements_subset bodyAccepted))
    through.substitution_extends

theorem statement_match_cases
      {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Statement}
      {expectedReturn : Ty} {initial allocated : State} {id : StatementId}
      {result : StatementResult} {scrutinees : Syntax.NonemptyDelimitedList Syntax.Expr}
      {arms : Syntax.MatchArms}
      {scrutinee : InferredExpression} {scrutineeState hiddenState : State} {hidden : Resolved.LocalId}
      {checked : MatchCasesResult}
      (accepted : (CallIndex.statement (fuel + 1) context source expectedReturn initial result).Accepted)
      (form : source.value = .matchWith scrutinees arms)
      (allocation : initial.allocateStatementId = (id, allocated))
      (scrutineeAccepted : matchScrutinee fuel context source.span scrutinees.elements.toList allocated = .ok (scrutinee, scrutineeState))
      (hiddenAllocation : scrutineeState.allocateHiddenLocal = (hidden, hiddenState))
      (child : (CallIndex.matchCases fuel context scrutinee.type expectedReturn hiddenState.lexicalScope arms.value.cases hiddenState checked).Accepted)
      (inputs : (CallIndex.statement (fuel + 1) context source expectedReturn initial result).Inputs)
      (backed : LiveTemplatesBacked initial) : LiveTemplatesBacked (CallIndex.matchCases fuel context scrutinee.type expectedReturn hiddenState.lexicalScope arms.value.cases hiddenState checked).initial := by
  have step : ChildStep (CallIndex.statement (fuel + 1) context source expectedReturn initial result) (CallIndex.matchCases fuel context scrutinee.type expectedReturn hiddenState.lexicalScope arms.value.cases hiddenState checked) := .statement_match_cases accepted form allocation scrutineeAccepted hiddenAllocation child
  have childInputs := step.inputs inputs
  have same : allocated = initial.allocateStatementId.2 := (congrArg Prod.snd allocation).symm
  subst allocated
  have scrutineeBacked := matchScrutinee_backed backed.allocateStatementId inputs.ready.allocateStatementId inputs.catalog scrutineeAccepted
  have sameHidden : hiddenState = scrutineeState.allocateHiddenLocal.2 := (congrArg Prod.snd hiddenAllocation).symm
  subst hiddenState
  exact scrutineeBacked.allocateHiddenLocal

theorem statement_match_default
      {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Statement}
      {expectedReturn : Ty} {initial allocated : State} {id : StatementId}
      {result : StatementResult} {scrutinees : Syntax.NonemptyDelimitedList Syntax.Expr}
      {arms : Syntax.MatchArms}
      {scrutinee : InferredExpression} {scrutineeState hiddenState : State} {hidden : Resolved.LocalId}
      {checked : MatchCasesResult}
      {body : Syntax.Block} {bodyResult : BlockResult}
      (accepted : (CallIndex.statement (fuel + 1) context source expectedReturn initial result).Accepted)
      (form : source.value = .matchWith scrutinees arms)
      (allocation : initial.allocateStatementId = (id, allocated))
      (scrutineeAccepted : matchScrutinee fuel context source.span scrutinees.elements.toList allocated = .ok (scrutinee, scrutineeState))
      (hiddenAllocation : scrutineeState.allocateHiddenLocal = (hidden, hiddenState))
      (casesAccepted : inferMatchCasesFuel fuel context scrutinee.type expectedReturn hiddenState.lexicalScope arms.value.cases hiddenState = .ok checked)
      (default : arms.value.defaultBody = some body)
      (child : (CallIndex.statements fuel context body.value expectedReturn checked.state bodyResult).Accepted)
      (inputs : (CallIndex.statement (fuel + 1) context source expectedReturn initial result).Inputs)
      (backed : LiveTemplatesBacked initial) : LiveTemplatesBacked (CallIndex.statements fuel context body.value expectedReturn checked.state bodyResult).initial := by
  have step : ChildStep (CallIndex.statement (fuel + 1) context source expectedReturn initial result) (CallIndex.statements fuel context body.value expectedReturn checked.state bodyResult) := .statement_match_default accepted form allocation scrutineeAccepted hiddenAllocation casesAccepted default child
  have childInputs := step.inputs inputs
  have same : allocated = initial.allocateStatementId.2 := (congrArg Prod.snd allocation).symm
  subst allocated
  have scrutineeBacked := matchScrutinee_backed backed.allocateStatementId inputs.ready.allocateStatementId inputs.catalog scrutineeAccepted
  have sameHidden : hiddenState = scrutineeState.allocateHiddenLocal.2 := (congrArg Prod.snd hiddenAllocation).symm
  subst hiddenState
  have before := ChildStep.inputs inputs (.statement_match_cases accepted form allocation scrutineeAccepted hiddenAllocation casesAccepted)
  exact matchCases before scrutineeBacked.allocateHiddenLocal casesAccepted

end Solcore.SourceSemantics.SourceInferenceExecution.ActualTemplateBacking
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceActualTemplateBacking
/-! Actual child calls inherit raw witnesses for their active local templates.
The root-to-child theorem follows the original accepted call graph. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceExecution
open SourceInferenceSoundness.ProtectedVariables

theorem ChildStep.liveTemplatesBacked {parent child : CallIndex}
    (step : ChildStep parent child) (inputs : parent.Inputs)
    (backed : LiveTemplatesBacked parent.initial) :
    LiveTemplatesBacked child.initial := by
  cases step
  all_goals first
  | solve | apply ActualTemplateBacking.expression_group <;> assumption
  | solve | apply ActualTemplateBacking.expression_tuple <;> assumption
  | solve | apply ActualTemplateBacking.expressions_head <;> assumption
  | solve | apply ActualTemplateBacking.expressions_tail <;> assumption
  | solve | apply ActualTemplateBacking.statements_head <;> assumption
  | solve | apply ActualTemplateBacking.statements_tail <;> assumption
  | solve | apply ActualTemplateBacking.statement_initializer <;> assumption
  | solve | apply ActualTemplateBacking.statement_return <;> assumption
  | solve | apply ActualTemplateBacking.statement_expression <;> assumption
  | solve | apply ActualTemplateBacking.statement_block <;> assumption
  | solve | apply ActualTemplateBacking.statement_if_condition <;> assumption
  | solve | apply ActualTemplateBacking.statement_if_then <;> assumption
  | solve | apply ActualTemplateBacking.statement_if_else <;> assumption
  | solve | apply ActualTemplateBacking.statement_assignment <;> assumption
  | solve | apply ActualTemplateBacking.statement_bitnot <;> assumption
  | solve | apply ActualTemplateBacking.statement_while_condition <;> assumption
  | solve | apply ActualTemplateBacking.statement_while_body <;> assumption
  | solve | apply ActualTemplateBacking.statement_for_initializer <;> assumption
  | solve | apply ActualTemplateBacking.statement_for_condition <;> assumption
  | solve | apply ActualTemplateBacking.statement_for_body <;> assumption
  | solve | apply ActualTemplateBacking.statement_for_post <;> assumption
  | solve | apply ActualTemplateBacking.forItems_head <;> assumption
  | solve | apply ActualTemplateBacking.forItems_tail <;> assumption
  | solve | apply ActualTemplateBacking.forItem_initializer <;> assumption
  | solve | apply ActualTemplateBacking.forItem_expression <;> assumption
  | solve | apply ActualTemplateBacking.forItem_assignment <;> assumption
  | solve | apply ActualTemplateBacking.forItem_bitnot <;> assumption
  | solve | apply ActualTemplateBacking.assignedValue_place <;> assumption
  | solve | apply ActualTemplateBacking.assignedValue_value <;> assumption
  | solve | apply ActualTemplateBacking.place_group <;> assumption
  | solve | apply ActualTemplateBacking.place_index_base <;> assumption
  | solve | apply ActualTemplateBacking.place_index_key <;> assumption
  | solve | apply ActualTemplateBacking.constructorApplication_arguments <;> assumption
  | solve | apply ActualTemplateBacking.constructorArguments_head <;> assumption
  | solve | apply ActualTemplateBacking.constructorArguments_tail <;> assumption
  | solve | apply ActualTemplateBacking.expression_unary <;> assumption
  | solve | apply ActualTemplateBacking.expression_binary_left <;> assumption
  | solve | apply ActualTemplateBacking.expression_binary_right <;> assumption
  | solve | apply ActualTemplateBacking.expression_conditional_condition <;> assumption
  | solve | apply ActualTemplateBacking.expression_conditional_then <;> assumption
  | solve | apply ActualTemplateBacking.expression_conditional_else <;> assumption
  | solve | apply ActualTemplateBacking.expression_lambda_body <;> assumption
  | solve | apply ActualTemplateBacking.expression_index_base <;> assumption
  | solve | apply ActualTemplateBacking.expression_index_key <;> assumption
  | solve | apply ActualTemplateBacking.expression_call_constructor <;> assumption
  | solve | apply ActualTemplateBacking.expression_call_arguments <;> assumption
  | solve | apply ActualTemplateBacking.expression_call_callee <;> assumption
  | solve | apply ActualTemplateBacking.expression_contextual_constructor <;> assumption
  | solve | apply ActualTemplateBacking.expression_field_constructor <;> assumption
  | solve | apply ActualTemplateBacking.matchCases_body <;> assumption
  | solve | apply ActualTemplateBacking.matchCases_tail <;> assumption
  | solve | apply ActualTemplateBacking.statement_match_single <;> assumption
  | solve | apply ActualTemplateBacking.statement_match_many <;> assumption
  | solve | apply ActualTemplateBacking.statement_match_cases <;> assumption
  | solve | apply ActualTemplateBacking.statement_match_default <;> assumption

theorem CallOccurrence.liveTemplatesBacked {root call : CallIndex}
    (inputs : root.Inputs) (backed : LiveTemplatesBacked root.initial)
    (here : CallOccurrence root call) : LiveTemplatesBacked call.initial := by
  induction here with
  | root _ => exact backed
  | child parent step ih => exact step.liveTemplatesBacked (parent.inputs inputs) ih

end Solcore.SourceSemantics.SourceInferenceExecution
end
