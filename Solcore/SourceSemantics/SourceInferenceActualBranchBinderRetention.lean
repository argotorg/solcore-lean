import Solcore.SourceSemantics.SourceInferenceActualTerminalBinderRetention
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceExecution
open Frontend SourceInference TypeSystem Detail LocalGeneralizationEvents
namespace ActualBinderRetention

theorem statement_bitnot
      {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Statement}
      {expectedReturn : Ty} {initial allocated : State} {id : StatementId}
      {result : StatementResult}
      {target : Syntax.Expr} {operator : Syntax.SourceSpan}
      {place : PlaceResolution} {final : State}
      (accepted : (CallIndex.statement (fuel + 1) context source expectedReturn initial result).Accepted)
      (form : source.value = .assignBitNot target operator)
      (allocation : initial.allocateStatementId = (id, allocated))
      (child : (CallIndex.place fuel context target allocated place final).Accepted)  :
    BindersRetained (CallIndex.place fuel context target allocated place final).final.nodes (CallIndex.statement (fuel + 1) context source expectedReturn initial result).final.nodes := by
  simp only [CallIndex.Accepted] at accepted child
  dsimp only [CallIndex.final] at ⊢
  cases fitting : Detail.unify final place.type .word with
  | error error => simp [inferStatementFuel, allocation, form, child, fitting, bind, Except.bind] at accepted
  | ok fitted =>
    unfold inferStatementFuel at accepted
    simp only [allocation, form, child, fitting, bind, Except.bind, pure, Pure.pure, Except.pure, Except.ok.injEq] at accepted
    cases accepted
    exact (unify_retained fitting).trans (.append _ _)


theorem forItem_bitnot
      {fuel : Nat} {context : SourceInference.Context} {source : Syntax.ForItem}
      {initial final : State} {result : ForItemForm}
      {target : Syntax.Expr} {operator : Syntax.SourceSpan} {place : PlaceResolution} {childFinal : State}
      (accepted : (CallIndex.forItem (fuel + 1) context source initial result final).Accepted)
      (form : source.value = .assignBitNot target operator)
      (child : (CallIndex.place fuel context target initial place childFinal).Accepted)  :
    BindersRetained (CallIndex.place fuel context target initial place childFinal).final.nodes (CallIndex.forItem (fuel + 1) context source initial result final).final.nodes := by
  simp only [CallIndex.Accepted] at accepted child
  dsimp only [CallIndex.final] at ⊢
  cases fitting : Detail.unify childFinal place.type .word with
  | error error => simp [inferForItemFuel, form, child, fitting, bind, Except.bind] at accepted
  | ok fitted =>
    unfold inferForItemFuel at accepted
    simp only [form, child, fitting, bind, Except.bind, pure, Pure.pure, Except.pure, Except.ok.injEq] at accepted
    cases accepted
    exact unify_retained fitting


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
      (child : (CallIndex.statements fuel context thenBody.value expectedReturn conditionState thenResult).Accepted)  :
    BindersRetained (CallIndex.statements fuel context thenBody.value expectedReturn conditionState thenResult).final.nodes (CallIndex.statement (fuel + 1) context source expectedReturn initial result).final.nodes := by
  simp only [CallIndex.Accepted] at accepted child
  dsimp only [CallIndex.final] at ⊢
  cases elseBody with
  | none =>
    unfold inferStatementFuel at accepted
    simp only [form, allocation, conditionAccepted, child, bind, Except.bind, pure, Pure.pure, Except.pure, Except.ok.injEq] at accepted
    cases accepted
    exact .append _ _
  | some elseBody =>
    cases elseAccepted : inferStatementsFuel fuel context elseBody.value expectedReturn (thenResult.state.restoreLexicalScope conditionState.lexicalScope) with
    | error error => simp [inferStatementFuel, allocation, form, conditionAccepted, child, elseAccepted, bind, Except.bind] at accepted
    | ok elseResult =>
      exact (inferStatementsFuel_origins_progress elseAccepted).retained.trans
        (statement_if_else accepted form allocation conditionAccepted rfl child elseAccepted)


theorem statement_if_condition
      {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Statement}
      {expectedReturn : Ty} {initial allocated : State} {id : StatementId}
      {result : StatementResult}
      {condition : Syntax.Expr} {thenBody : Syntax.Block} {elseBody : Option Syntax.Block}
      {conditionValue : InferredExpression} {conditionState : State}
      (accepted : (CallIndex.statement (fuel + 1) context source expectedReturn initial result).Accepted)
      (form : source.value = .ifThen condition thenBody elseBody)
      (allocation : initial.allocateStatementId = (id, allocated))
      (child : (CallIndex.expression fuel context condition (some .bool) allocated conditionValue conditionState).Accepted)  :
    BindersRetained (CallIndex.expression fuel context condition (some .bool) allocated conditionValue conditionState).final.nodes (CallIndex.statement (fuel + 1) context source expectedReturn initial result).final.nodes := by
  simp only [CallIndex.Accepted] at accepted child
  dsimp only [CallIndex.final] at ⊢
  cases thenAccepted : inferStatementsFuel fuel context thenBody.value expectedReturn conditionState with
  | error error => simp [inferStatementFuel, allocation, form, child, thenAccepted, bind, Except.bind] at accepted
  | ok thenResult =>
    exact (inferStatementsFuel_origins_progress thenAccepted).retained.trans
      (statement_if_then accepted form allocation child thenAccepted)


theorem statement_while_condition
      {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Statement}
      {expectedReturn : Ty} {initial allocated : State} {id : StatementId}
      {result : StatementResult}
      {condition : Syntax.Expr} {body : Syntax.Block}
      {conditionValue : InferredExpression} {conditionState : State}
      (accepted : (CallIndex.statement (fuel + 1) context source expectedReturn initial result).Accepted)
      (form : source.value = .whileLoop condition body)
      (allocation : initial.allocateStatementId = (id, allocated))
      (child : (CallIndex.expression fuel context condition (some .bool) allocated conditionValue conditionState).Accepted)  :
    BindersRetained (CallIndex.expression fuel context condition (some .bool) allocated conditionValue conditionState).final.nodes (CallIndex.statement (fuel + 1) context source expectedReturn initial result).final.nodes := by
  simp only [CallIndex.Accepted] at accepted child
  dsimp only [CallIndex.final] at ⊢
  cases bodyAccepted : inferStatementsFuel fuel {context with loopDepth := context.loopDepth + 1} body.value expectedReturn conditionState with
  | error error => simp [inferStatementFuel, allocation, form, child, bodyAccepted, bind, Except.bind] at accepted
  | ok bodyResult =>
    exact (inferStatementsFuel_origins_progress bodyAccepted).retained.trans
      (statement_while_body accepted form allocation child bodyAccepted)

end ActualBinderRetention
end Solcore.SourceSemantics.SourceInferenceExecution
