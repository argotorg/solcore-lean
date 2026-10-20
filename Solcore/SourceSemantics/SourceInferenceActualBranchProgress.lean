import Solcore.SourceSemantics.SourceInferenceActualTerminalProgress
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceExecution
open Frontend SourceInference TypeSystem Detail SourceInferenceSoundness.ProtectedVariables
namespace ActualSuffixProgress

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
    (inputs : (CallIndex.statement (fuel + 1) context source expectedReturn initial result).Inputs) :
    (CallIndex.place fuel context target allocated place final).final.InferenceProgress (CallIndex.statement (fuel + 1) context source expectedReturn initial result).final := by
  simp only [CallIndex.Accepted] at accepted child
  dsimp only [CallIndex.final] at ⊢
  have properties := ((ChildStep.statement_bitnot accepted form allocation child).inputs inputs).progress child
  cases fitting : Detail.unify final place.type .word with
  | error error => simp [inferStatementFuel, allocation, form, child, fitting, bind, Except.bind] at accepted
  | ok fitted =>
    have after := unify_inferenceProgress properties.2.1.solved (properties.2.2 _ (List.mem_singleton_self _)) (Ty.variablesBelow_constructor _ _) fitting
    have ready := unify_preserves_inferenceReady properties.2.1 (properties.2.2 _ (List.mem_singleton_self _)) (Ty.variablesBelow_constructor _ _) fitting
    unfold inferStatementFuel at accepted
    simp only [allocation, form, child, fitting, bind, Except.bind, pure, Pure.pure, Except.pure, Except.ok.injEq] at accepted
    cases accepted
    exact after.trans (.of_inference_eq ready.solved rfl)

theorem forItem_bitnot
      {fuel : Nat} {context : SourceInference.Context} {source : Syntax.ForItem}
      {initial final : State} {result : ForItemForm}
      {target : Syntax.Expr} {operator : Syntax.SourceSpan} {place : PlaceResolution} {childFinal : State}
      (accepted : (CallIndex.forItem (fuel + 1) context source initial result final).Accepted)
      (form : source.value = .assignBitNot target operator)
      (child : (CallIndex.place fuel context target initial place childFinal).Accepted)
    (inputs : (CallIndex.forItem (fuel + 1) context source initial result final).Inputs) :
    (CallIndex.place fuel context target initial place childFinal).final.InferenceProgress (CallIndex.forItem (fuel + 1) context source initial result final).final := by
  simp only [CallIndex.Accepted] at accepted child
  dsimp only [CallIndex.final] at ⊢
  have properties := ((ChildStep.forItem_bitnot accepted form child).inputs inputs).progress child
  cases fitting : Detail.unify childFinal place.type .word with
  | error error => simp [inferForItemFuel, form, child, fitting, bind, Except.bind] at accepted
  | ok fitted =>
    have after := unify_inferenceProgress properties.2.1.solved (properties.2.2 _ (List.mem_singleton_self _)) (Ty.variablesBelow_constructor _ _) fitting
    have ready := unify_preserves_inferenceReady properties.2.1 (properties.2.2 _ (List.mem_singleton_self _)) (Ty.variablesBelow_constructor _ _) fitting
    unfold inferForItemFuel at accepted
    simp only [form, child, fitting, bind, Except.bind, pure, Pure.pure, Except.pure, Except.ok.injEq] at accepted
    cases accepted
    exact after.trans (.of_inference_eq ready.solved rfl)

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
    (inputs : (CallIndex.statement (fuel + 1) context source expectedReturn initial result).Inputs) :
    (CallIndex.statements fuel context thenBody.value expectedReturn conditionState thenResult).final.InferenceProgress (CallIndex.statement (fuel + 1) context source expectedReturn initial result).final := by
  simp only [CallIndex.Accepted] at accepted child
  dsimp only [CallIndex.final] at ⊢
  have properties := ((ChildStep.statement_if_then accepted form allocation conditionAccepted child).inputs inputs).progress child
  cases elseBody with
  | none =>
    unfold inferStatementFuel at accepted
    simp only [form, allocation, conditionAccepted, child, bind, Except.bind, pure, Pure.pure, Except.pure, Except.ok.injEq] at accepted
    cases accepted
    exact .of_inference_eq properties.2.1.solved rfl
  | some elseBody =>
    cases elseAccepted : inferStatementsFuel fuel context elseBody.value expectedReturn (thenResult.state.restoreLexicalScope conditionState.lexicalScope) with
    | error error => simp [inferStatementFuel, allocation, form, conditionAccepted, child, elseAccepted, bind, Except.bind] at accepted
    | ok elseResult =>
      have step := ChildStep.statement_if_else accepted form allocation conditionAccepted rfl child elseAccepted
      have after := (step.inputs inputs).progress elseAccepted
      have restored : thenResult.state.InferenceProgress (thenResult.state.restoreLexicalScope conditionState.lexicalScope) := .of_inference_eq properties.2.1.solved rfl
      exact restored.trans (after.1.trans (statement_if_else accepted form allocation conditionAccepted rfl child elseAccepted inputs))

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
    (inputs : (CallIndex.statement (fuel + 1) context source expectedReturn initial result).Inputs) :
    (CallIndex.expression fuel context condition (some .bool) allocated conditionValue conditionState).final.InferenceProgress (CallIndex.statement (fuel + 1) context source expectedReturn initial result).final := by
  simp only [CallIndex.Accepted] at accepted child
  dsimp only [CallIndex.final] at ⊢
  cases thenAccepted : inferStatementsFuel fuel context thenBody.value expectedReturn conditionState with
  | error error => simp [inferStatementFuel, allocation, form, child, thenAccepted, bind, Except.bind] at accepted
  | ok thenResult =>
    have after := ((ChildStep.statement_if_then accepted form allocation child thenAccepted).inputs inputs).progress thenAccepted
    exact after.1.trans (statement_if_then accepted form allocation child thenAccepted inputs)

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
    (inputs : (CallIndex.statement (fuel + 1) context source expectedReturn initial result).Inputs) :
    (CallIndex.expression fuel context condition (some .bool) allocated conditionValue conditionState).final.InferenceProgress (CallIndex.statement (fuel + 1) context source expectedReturn initial result).final := by
  simp only [CallIndex.Accepted] at accepted child
  dsimp only [CallIndex.final] at ⊢
  cases bodyAccepted : inferStatementsFuel fuel {context with loopDepth := context.loopDepth + 1} body.value expectedReturn conditionState with
  | error error => simp [inferStatementFuel, allocation, form, child, bodyAccepted, bind, Except.bind] at accepted
  | ok bodyResult =>
    have after := ((ChildStep.statement_while_body accepted form allocation child bodyAccepted).inputs inputs).progress bodyAccepted
    exact after.1.trans (statement_while_body accepted form allocation child bodyAccepted inputs)

end ActualSuffixProgress
end Solcore.SourceSemantics.SourceInferenceExecution
