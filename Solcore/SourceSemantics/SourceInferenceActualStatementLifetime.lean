import Solcore.SourceSemantics.SourceInferenceActualCallInputTraversal
import Solcore.SourceSemantics.SourceInferenceGeneralizationLifetimeIfSteps
import Solcore.SourceSemantics.SourceInferenceGeneralizationLifetimeMatchScrutinee
import Solcore.SourceSemantics.SourceInferenceGeneralizationLifetimeForSteps

/-! Statement and header child edges retain the actual suffix and result. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceExecution
open Frontend SourceInference TypeSystem Detail SourceInferenceSoundness.ProtectedVariables
namespace ActualStatementLifetime
variable {whole : TypedSource} {finalSubstitution : Substitution}
    {binder : TypedBinder} {initializer : ExpressionId}
    {event : RetainedGeneralization whole finalSubstitution binder initializer}

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
    (lifetime : GeneralizationLifetime event (CallIndex.expression fuel context value (some expectedReturn) allocated inferred final).initial.inference.next (CallIndex.expression fuel context value (some expectedReturn) allocated inferred final).final (CallIndex.expression fuel context value (some expectedReturn) allocated inferred final).outputTypes) :
    GeneralizationLifetime event (CallIndex.statement (fuel + 1) context source expectedReturn initial result).initial.inference.next (CallIndex.statement (fuel + 1) context source expectedReturn initial result).final (CallIndex.statement (fuel + 1) context source expectedReturn initial result).outputTypes := by
  simp only [CallIndex.Accepted] at accepted child
  dsimp only [CallIndex.initial, CallIndex.final, CallIndex.outputTypes] at lifetime ⊢
  exact lifetime.statement_return inputs.ready inputs.catalog inputs.bounds form allocation child accepted

theorem statement_expression
      {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Statement}
      {expectedReturn : Ty} {initial allocated : State} {id : StatementId}
      {result : StatementResult}
      {value : Syntax.Expr} {semicolon : Bool} {inferred : InferredExpression} {final : State}
      (accepted : (CallIndex.statement (fuel + 1) context source expectedReturn initial result).Accepted)
      (form : source.value = .expression value semicolon)
      (allocation : initial.allocateStatementId = (id, allocated))
      (child : (CallIndex.expression fuel context value none allocated inferred final).Accepted)
    (_inputs : (CallIndex.statement (fuel + 1) context source expectedReturn initial result).Inputs)
    (lifetime : GeneralizationLifetime event (CallIndex.expression fuel context value none allocated inferred final).initial.inference.next (CallIndex.expression fuel context value none allocated inferred final).final (CallIndex.expression fuel context value none allocated inferred final).outputTypes) :
    GeneralizationLifetime event (CallIndex.statement (fuel + 1) context source expectedReturn initial result).initial.inference.next (CallIndex.statement (fuel + 1) context source expectedReturn initial result).final (CallIndex.statement (fuel + 1) context source expectedReturn initial result).outputTypes := by
  simp only [CallIndex.Accepted] at accepted child
  dsimp only [CallIndex.initial, CallIndex.final, CallIndex.outputTypes] at lifetime ⊢
  exact lifetime.statement_expression form allocation child accepted

theorem statement_block
      {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Statement}
      {expectedReturn : Ty} {initial allocated : State} {id : StatementId}
      {result : StatementResult}
      {body : List Syntax.Statement} {bodyResult : BlockResult}
      (accepted : (CallIndex.statement (fuel + 1) context source expectedReturn initial result).Accepted)
      (form : source.value = .block body)
      (allocation : initial.allocateStatementId = (id, allocated))
      (child : (CallIndex.statements fuel context body expectedReturn allocated bodyResult).Accepted)
    (_inputs : (CallIndex.statement (fuel + 1) context source expectedReturn initial result).Inputs)
    (lifetime : GeneralizationLifetime event (CallIndex.statements fuel context body expectedReturn allocated bodyResult).initial.inference.next (CallIndex.statements fuel context body expectedReturn allocated bodyResult).final (CallIndex.statements fuel context body expectedReturn allocated bodyResult).outputTypes) :
    GeneralizationLifetime event (CallIndex.statement (fuel + 1) context source expectedReturn initial result).initial.inference.next (CallIndex.statement (fuel + 1) context source expectedReturn initial result).final (CallIndex.statement (fuel + 1) context source expectedReturn initial result).outputTypes := by
  simp only [CallIndex.Accepted] at accepted child
  dsimp only [CallIndex.initial, CallIndex.final, CallIndex.outputTypes] at lifetime ⊢
  exact lifetime.statement_block form allocation child accepted

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
    (_inputs : (CallIndex.statement (fuel + 1) context source expectedReturn initial result).Inputs)
    (lifetime : GeneralizationLifetime event (CallIndex.assignedValue fuel context target operator.value value allocated assignment inferred final).initial.inference.next (CallIndex.assignedValue fuel context target operator.value value allocated assignment inferred final).final (CallIndex.assignedValue fuel context target operator.value value allocated assignment inferred final).outputTypes) :
    GeneralizationLifetime event (CallIndex.statement (fuel + 1) context source expectedReturn initial result).initial.inference.next (CallIndex.statement (fuel + 1) context source expectedReturn initial result).final (CallIndex.statement (fuel + 1) context source expectedReturn initial result).outputTypes := by
  simp only [CallIndex.Accepted] at accepted child
  dsimp only [CallIndex.initial, CallIndex.final, CallIndex.outputTypes] at lifetime ⊢
  unfold inferStatementFuel at accepted
  simp only [allocation, form, child, bind, Except.bind, pure, Pure.pure, Except.pure, Except.ok.injEq] at accepted
  cases accepted
  have sameNext : allocated.inference.next = initial.inference.next := by
    rw [← show initial.allocateStatementId.2 = allocated from congrArg Prod.snd allocation]; rfl
  simpa only [sameNext] using lifetime.recordUnit id source.span (.assignValue assignment operator.value inferred.id)

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
    (lifetime : GeneralizationLifetime event (CallIndex.place fuel context target allocated place final).initial.inference.next (CallIndex.place fuel context target allocated place final).final (CallIndex.place fuel context target allocated place final).outputTypes) :
    GeneralizationLifetime event (CallIndex.statement (fuel + 1) context source expectedReturn initial result).initial.inference.next (CallIndex.statement (fuel + 1) context source expectedReturn initial result).final (CallIndex.statement (fuel + 1) context source expectedReturn initial result).outputTypes := by
  simp only [CallIndex.Accepted] at accepted child
  dsimp only [CallIndex.initial, CallIndex.final, CallIndex.outputTypes] at lifetime ⊢
  cases fitting : Detail.unify final place.type .word with
  | error error => simp [inferStatementFuel, allocation, form, child, fitting, bind, Except.bind] at accepted
  | ok fitted =>
    have childInputs := (ChildStep.statement_bitnot accepted form allocation child).inputs inputs
    have properties := childInputs.progress child
    have after := lifetime.unify properties.2.1 (properties.2.2 _ (List.mem_singleton_self _))
      (Ty.variablesBelow_constructor _ _) (lifetime.values _ (List.mem_singleton_self _))
      (safe_closed _ _ (Ty.variablesBelow_constructor _ _)) fitting
    unfold inferStatementFuel at accepted
    simp only [allocation, form, child, fitting, bind, Except.bind, pure, Pure.pure, Except.pure, Except.ok.injEq] at accepted
    cases accepted
    have sameNext : allocated.inference.next = initial.inference.next := by
      rw [← show initial.allocateStatementId.2 = allocated from congrArg Prod.snd allocation]; rfl
    simpa only [sameNext] using after.recordUnit id source.span (.assignBitNot {target := {place with type := fitted.resolve place.type}})

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
    (lifetime : GeneralizationLifetime event (CallIndex.expression fuel context condition (some .bool) allocated conditionValue conditionState).initial.inference.next (CallIndex.expression fuel context condition (some .bool) allocated conditionValue conditionState).final (CallIndex.expression fuel context condition (some .bool) allocated conditionValue conditionState).outputTypes) :
    GeneralizationLifetime event (CallIndex.statement (fuel + 1) context source expectedReturn initial result).initial.inference.next (CallIndex.statement (fuel + 1) context source expectedReturn initial result).final (CallIndex.statement (fuel + 1) context source expectedReturn initial result).outputTypes := by
  simp only [CallIndex.Accepted] at accepted child
  dsimp only [CallIndex.initial, CallIndex.final, CallIndex.outputTypes] at lifetime ⊢
  cases bodyAccepted : inferStatementsFuel fuel {context with loopDepth := context.loopDepth + 1} body.value expectedReturn conditionState with
  | error error => simp [inferStatementFuel, allocation, form, child, bodyAccepted, bind, Except.bind] at accepted
  | ok bodyResult => exact lifetime.while_condition inputs.ready inputs.wellFormed inputs.catalog inputs.bounds form allocation child bodyAccepted accepted

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
    (lifetime : GeneralizationLifetime event (CallIndex.statements fuel { context with loopDepth := context.loopDepth + 1 } body.value expectedReturn conditionState bodyResult).initial.inference.next (CallIndex.statements fuel { context with loopDepth := context.loopDepth + 1 } body.value expectedReturn conditionState bodyResult).final (CallIndex.statements fuel { context with loopDepth := context.loopDepth + 1 } body.value expectedReturn conditionState bodyResult).outputTypes) :
    GeneralizationLifetime event (CallIndex.statement (fuel + 1) context source expectedReturn initial result).initial.inference.next (CallIndex.statement (fuel + 1) context source expectedReturn initial result).final (CallIndex.statement (fuel + 1) context source expectedReturn initial result).outputTypes := by
  simp only [CallIndex.Accepted] at accepted child
  dsimp only [CallIndex.initial, CallIndex.final, CallIndex.outputTypes] at lifetime ⊢
  exact lifetime.while_body inputs.ready inputs.catalog form allocation conditionAccepted child accepted

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
    (lifetime : GeneralizationLifetime event (CallIndex.expression fuel context condition (some .bool) allocated conditionValue conditionState).initial.inference.next (CallIndex.expression fuel context condition (some .bool) allocated conditionValue conditionState).final (CallIndex.expression fuel context condition (some .bool) allocated conditionValue conditionState).outputTypes) :
    GeneralizationLifetime event (CallIndex.statement (fuel + 1) context source expectedReturn initial result).initial.inference.next (CallIndex.statement (fuel + 1) context source expectedReturn initial result).final (CallIndex.statement (fuel + 1) context source expectedReturn initial result).outputTypes := by
  simp only [CallIndex.Accepted] at accepted child
  dsimp only [CallIndex.initial, CallIndex.final, CallIndex.outputTypes] at lifetime ⊢
  cases thenAccepted : inferStatementsFuel fuel context thenBody.value expectedReturn conditionState with
  | error error => simp [inferStatementFuel, allocation, form, child, thenAccepted, bind, Except.bind] at accepted
  | ok thenResult =>
    cases elseBody with
    | none => exact lifetime.if_without_else_condition inputs.ready inputs.wellFormed inputs.catalog inputs.bounds form allocation child thenAccepted accepted
    | some elseBody =>
      cases elseAccepted : inferStatementsFuel fuel context elseBody.value expectedReturn (thenResult.state.restoreLexicalScope conditionState.lexicalScope) with
      | error error => simp [inferStatementFuel, allocation, form, child, thenAccepted, elseAccepted, bind, Except.bind] at accepted
      | ok elseResult => exact lifetime.if_with_else_condition inputs.ready inputs.wellFormed inputs.catalog inputs.bounds form allocation child thenAccepted elseAccepted accepted

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
    (lifetime : GeneralizationLifetime event (CallIndex.statements fuel context thenBody.value expectedReturn conditionState thenResult).initial.inference.next (CallIndex.statements fuel context thenBody.value expectedReturn conditionState thenResult).final (CallIndex.statements fuel context thenBody.value expectedReturn conditionState thenResult).outputTypes) :
    GeneralizationLifetime event (CallIndex.statement (fuel + 1) context source expectedReturn initial result).initial.inference.next (CallIndex.statement (fuel + 1) context source expectedReturn initial result).final (CallIndex.statement (fuel + 1) context source expectedReturn initial result).outputTypes := by
  simp only [CallIndex.Accepted] at accepted child
  dsimp only [CallIndex.initial, CallIndex.final, CallIndex.outputTypes] at lifetime ⊢
  cases elseBody with
  | none => exact lifetime.if_without_else_body inputs.ready inputs.catalog form allocation conditionAccepted child accepted
  | some elseBody =>
    cases elseAccepted : inferStatementsFuel fuel context elseBody.value expectedReturn (thenResult.state.restoreLexicalScope conditionState.lexicalScope) with
    | error error => simp [inferStatementFuel, allocation, form, conditionAccepted, child, elseAccepted, bind, Except.bind] at accepted
    | ok elseResult => exact lifetime.if_with_else_then inputs.ready inputs.wellFormed inputs.catalog inputs.bounds form allocation conditionAccepted child elseAccepted accepted

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
    (lifetime : GeneralizationLifetime event (CallIndex.statements fuel context body.value expectedReturn (thenResult.state.restoreLexicalScope conditionState.lexicalScope) elseResult).initial.inference.next (CallIndex.statements fuel context body.value expectedReturn (thenResult.state.restoreLexicalScope conditionState.lexicalScope) elseResult).final (CallIndex.statements fuel context body.value expectedReturn (thenResult.state.restoreLexicalScope conditionState.lexicalScope) elseResult).outputTypes) :
    GeneralizationLifetime event (CallIndex.statement (fuel + 1) context source expectedReturn initial result).initial.inference.next (CallIndex.statement (fuel + 1) context source expectedReturn initial result).final (CallIndex.statement (fuel + 1) context source expectedReturn initial result).outputTypes := by
  simp only [CallIndex.Accepted] at accepted child
  dsimp only [CallIndex.initial, CallIndex.final, CallIndex.outputTypes] at lifetime ⊢
  subst elseBody
  exact lifetime.if_with_else_else inputs.ready inputs.catalog inputs.bounds form allocation conditionAccepted thenAccepted child accepted

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
    (lifetime : GeneralizationLifetime event (CallIndex.expression fuel context scrutinee none allocated value childFinal).initial.inference.next (CallIndex.expression fuel context scrutinee none allocated value childFinal).final (CallIndex.expression fuel context scrutinee none allocated value childFinal).outputTypes) :
    GeneralizationLifetime event (CallIndex.statement (fuel + 1) context source expectedReturn initial result).initial.inference.next (CallIndex.statement (fuel + 1) context source expectedReturn initial result).final (CallIndex.statement (fuel + 1) context source expectedReturn initial result).outputTypes := by
  simp only [CallIndex.Accepted] at accepted child
  dsimp only [CallIndex.initial, CallIndex.final, CallIndex.outputTypes] at lifetime ⊢
  exact lifetime.statement_match_single inputs.ready inputs.wellFormed inputs.catalog inputs.bounds form allocation single child accepted

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
    (lifetime : GeneralizationLifetime event (CallIndex.expressions fuel context scrutinees.elements.toList allocated values childFinal).initial.inference.next (CallIndex.expressions fuel context scrutinees.elements.toList allocated values childFinal).final (CallIndex.expressions fuel context scrutinees.elements.toList allocated values childFinal).outputTypes) :
    GeneralizationLifetime event (CallIndex.statement (fuel + 1) context source expectedReturn initial result).initial.inference.next (CallIndex.statement (fuel + 1) context source expectedReturn initial result).final (CallIndex.statement (fuel + 1) context source expectedReturn initial result).outputTypes := by
  simp only [CallIndex.Accepted] at accepted child
  dsimp only [CallIndex.initial, CallIndex.final, CallIndex.outputTypes] at lifetime ⊢
  exact lifetime.statement_match_many inputs.ready inputs.wellFormed inputs.catalog inputs.bounds form allocation multiple child accepted

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
    (lifetime : GeneralizationLifetime event (CallIndex.matchCases fuel context scrutinee.type expectedReturn hiddenState.lexicalScope arms.value.cases hiddenState checked).initial.inference.next (CallIndex.matchCases fuel context scrutinee.type expectedReturn hiddenState.lexicalScope arms.value.cases hiddenState checked).final (CallIndex.matchCases fuel context scrutinee.type expectedReturn hiddenState.lexicalScope arms.value.cases hiddenState checked).outputTypes) :
    GeneralizationLifetime event (CallIndex.statement (fuel + 1) context source expectedReturn initial result).initial.inference.next (CallIndex.statement (fuel + 1) context source expectedReturn initial result).final (CallIndex.statement (fuel + 1) context source expectedReturn initial result).outputTypes := by
  simp only [CallIndex.Accepted] at accepted child
  dsimp only [CallIndex.initial, CallIndex.final, CallIndex.outputTypes] at lifetime ⊢
  exact lifetime.statement_match_cases inputs.ready inputs.wellFormed inputs.catalog inputs.bounds form allocation scrutineeAccepted hiddenAllocation child accepted

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
    (lifetime : GeneralizationLifetime event (CallIndex.statements fuel context body.value expectedReturn checked.state bodyResult).initial.inference.next (CallIndex.statements fuel context body.value expectedReturn checked.state bodyResult).final (CallIndex.statements fuel context body.value expectedReturn checked.state bodyResult).outputTypes) :
    GeneralizationLifetime event (CallIndex.statement (fuel + 1) context source expectedReturn initial result).initial.inference.next (CallIndex.statement (fuel + 1) context source expectedReturn initial result).final (CallIndex.statement (fuel + 1) context source expectedReturn initial result).outputTypes := by
  simp only [CallIndex.Accepted] at accepted child
  dsimp only [CallIndex.initial, CallIndex.final, CallIndex.outputTypes] at lifetime ⊢
  exact lifetime.statement_match_default inputs.ready inputs.wellFormed inputs.catalog inputs.bounds form allocation scrutineeAccepted hiddenAllocation casesAccepted default child accepted

theorem forItem_expression
      {fuel : Nat} {context : SourceInference.Context} {source : Syntax.ForItem}
      {initial final : State} {result : ForItemForm}
      {value : Syntax.Expr} {inferred : InferredExpression} {childFinal : State}
      (accepted : (CallIndex.forItem (fuel + 1) context source initial result final).Accepted)
      (form : source.value = .expression value)
      (child : (CallIndex.expression fuel context value none initial inferred childFinal).Accepted)
    (_inputs : (CallIndex.forItem (fuel + 1) context source initial result final).Inputs)
    (lifetime : GeneralizationLifetime event (CallIndex.expression fuel context value none initial inferred childFinal).initial.inference.next (CallIndex.expression fuel context value none initial inferred childFinal).final (CallIndex.expression fuel context value none initial inferred childFinal).outputTypes) :
    GeneralizationLifetime event (CallIndex.forItem (fuel + 1) context source initial result final).initial.inference.next (CallIndex.forItem (fuel + 1) context source initial result final).final (CallIndex.forItem (fuel + 1) context source initial result final).outputTypes := by
  simp only [CallIndex.Accepted] at accepted child
  dsimp only [CallIndex.initial, CallIndex.final, CallIndex.outputTypes] at lifetime ⊢
  exact lifetime.forItem_expression form child accepted

theorem forItem_assignment
      {fuel : Nat} {context : SourceInference.Context} {source : Syntax.ForItem}
      {initial final : State} {result : ForItemForm}
      {target value : Syntax.Expr} {operator : Syntax.Located Syntax.ValueAssignOp}
      {assignment : AssignmentResolution} {inferred : InferredExpression} {childFinal : State}
      (accepted : (CallIndex.forItem (fuel + 1) context source initial result final).Accepted)
      (form : source.value = .assignValue target operator value)
      (child : (CallIndex.assignedValue fuel context target operator.value value initial assignment inferred childFinal).Accepted)
    (_inputs : (CallIndex.forItem (fuel + 1) context source initial result final).Inputs)
    (lifetime : GeneralizationLifetime event (CallIndex.assignedValue fuel context target operator.value value initial assignment inferred childFinal).initial.inference.next (CallIndex.assignedValue fuel context target operator.value value initial assignment inferred childFinal).final (CallIndex.assignedValue fuel context target operator.value value initial assignment inferred childFinal).outputTypes) :
    GeneralizationLifetime event (CallIndex.forItem (fuel + 1) context source initial result final).initial.inference.next (CallIndex.forItem (fuel + 1) context source initial result final).final (CallIndex.forItem (fuel + 1) context source initial result final).outputTypes := by
  simp only [CallIndex.Accepted] at accepted child
  dsimp only [CallIndex.initial, CallIndex.final, CallIndex.outputTypes] at lifetime ⊢
  exact lifetime.forItem_assignment form child accepted

theorem forItem_bitnot
      {fuel : Nat} {context : SourceInference.Context} {source : Syntax.ForItem}
      {initial final : State} {result : ForItemForm}
      {target : Syntax.Expr} {operator : Syntax.SourceSpan} {place : PlaceResolution} {childFinal : State}
      (accepted : (CallIndex.forItem (fuel + 1) context source initial result final).Accepted)
      (form : source.value = .assignBitNot target operator)
      (child : (CallIndex.place fuel context target initial place childFinal).Accepted)
    (inputs : (CallIndex.forItem (fuel + 1) context source initial result final).Inputs)
    (lifetime : GeneralizationLifetime event (CallIndex.place fuel context target initial place childFinal).initial.inference.next (CallIndex.place fuel context target initial place childFinal).final (CallIndex.place fuel context target initial place childFinal).outputTypes) :
    GeneralizationLifetime event (CallIndex.forItem (fuel + 1) context source initial result final).initial.inference.next (CallIndex.forItem (fuel + 1) context source initial result final).final (CallIndex.forItem (fuel + 1) context source initial result final).outputTypes := by
  simp only [CallIndex.Accepted] at accepted child
  dsimp only [CallIndex.initial, CallIndex.final, CallIndex.outputTypes] at lifetime ⊢
  cases fitting : Detail.unify childFinal place.type .word with
  | error error => simp [inferForItemFuel, form, child, fitting, bind, Except.bind] at accepted
  | ok fitted => exact lifetime.forItem_bitnot inputs.ready inputs.catalog form child fitting accepted

end ActualStatementLifetime
end Solcore.SourceSemantics.SourceInferenceExecution
