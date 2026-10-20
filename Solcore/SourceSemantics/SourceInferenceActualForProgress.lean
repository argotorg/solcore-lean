import Solcore.SourceSemantics.SourceInferenceActualCallInputTraversal
import Solcore.Frontend.SourceInference.ForStatementInferenceContinuation
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceExecution
open Frontend SourceInference TypeSystem Detail SourceInferenceSoundness.ProtectedVariables
namespace ActualSuffixProgress

private theorem forProgress
    {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Statement}
    {initializers post : List Syntax.ForItem} {condition : Syntax.Expr} {body : Syntax.Block}
    {expected : Ty} {initial : State} {result : StatementResult}
    (receipt : SourceInference.ForStatementInferenceContinuation.Receipt fuel context source initializers condition post body expected initial result)
    (inputs : (CallIndex.statement (fuel+1) context source expected initial result).Inputs) :
    receipt.initialized.state.InferenceProgress result.state ∧
    receipt.testState.InferenceProgress result.state ∧
    receipt.bodyResult.state.InferenceProgress result.state ∧
    receipt.postResult.state.InferenceProgress result.state := by
  have facts := receipt.inference inputs.ready inputs.catalog.formation inputs.catalog.canonical inputs.bounds
  have initialized := inferForItemsFuel_inferenceProperties inputs.ready.allocateStatementId
    inputs.catalog.formation inputs.catalog.canonical receipt.initialization
  have tested := inferExprFuel_inferenceProperties initialized.2 inputs.catalog.formation inputs.catalog.canonical
    (by intro type member; cases member; exact Ty.variablesBelow_constructor _ _) receipt.tested
  have before := (State.InferenceProgress.allocateStatementId initial inputs.ready.solved).trans (initialized.1.trans tested.1)
  have expectedBelow : expected.VariablesBelow initial.inference.next := inputs.bounds
  have bodyProps := inferStatementsFuel_inferenceProperties (context := SourceInference.ForStatementInferenceContinuation.loopContext context) tested.2.1 inputs.catalog.formation inputs.catalog.canonical
    (expectedBelow.weaken before.next_le) receipt.bodyAccepted
  have postProps := inferForItemsFuel_inferenceProperties (context := SourceInference.ForStatementInferenceContinuation.loopContext context) facts.2.1 inputs.catalog.formation inputs.catalog.canonical receipt.postAccepted
  have restored : receipt.bodyResult.state.InferenceProgress
      (receipt.bodyResult.state.restoreLexicalScope receipt.initialized.state.lexicalScope) :=
    .of_inference_eq bodyProps.2.1.solved rfl
  have afterBody := restored.trans (postProps.1.trans facts.2.2.2)
  exact ⟨facts.2.2.1, bodyProps.1.trans afterBody, afterBody, facts.2.2.2⟩

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
    (inputs : (CallIndex.statement (fuel + 1) context source expectedReturn initial result).Inputs) :
    (CallIndex.forItems fuel context initializer allocated initialized).final.InferenceProgress (CallIndex.statement (fuel + 1) context source expectedReturn initial result).final := by
  simp only [CallIndex.Accepted] at accepted child
  dsimp only [CallIndex.final] at ⊢
  obtain ⟨receipt⟩ := SourceInference.ForStatementInferenceContinuation.of_accepted form accepted
  have actualInit := receipt.initialization
  rw [allocation] at actualInit
  have sameInit := Except.ok.inj (actualInit.symm.trans child)
  simpa only [sameInit] using (forProgress receipt inputs).1

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
    (inputs : (CallIndex.statement (fuel + 1) context source expectedReturn initial result).Inputs) :
    (CallIndex.expression fuel context condition (some .bool) initialized.state conditionValue conditionState).final.InferenceProgress (CallIndex.statement (fuel + 1) context source expectedReturn initial result).final := by
  simp only [CallIndex.Accepted] at accepted child
  dsimp only [CallIndex.final] at ⊢
  obtain ⟨receipt⟩ := SourceInference.ForStatementInferenceContinuation.of_accepted form accepted
  have actualInit := receipt.initialization
  rw [allocation] at actualInit
  have sameInit := Except.ok.inj (actualInit.symm.trans initializerAccepted)
  have actualTest := receipt.tested
  rw [sameInit] at actualTest
  have sameTest := Except.ok.inj (actualTest.symm.trans child)
  have sameTestState : receipt.testState = conditionState := congrArg Prod.snd sameTest
  have sameTestValue : receipt.test = conditionValue := congrArg Prod.fst sameTest
  simpa only [sameTestState] using (forProgress receipt inputs).2.1

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
    (inputs : (CallIndex.statement (fuel + 1) context source expectedReturn initial result).Inputs) :
    (CallIndex.statements fuel { context with loopDepth := context.loopDepth + 1 } body.value expectedReturn conditionState bodyResult).final.InferenceProgress (CallIndex.statement (fuel + 1) context source expectedReturn initial result).final := by
  simp only [CallIndex.Accepted] at accepted child
  dsimp only [CallIndex.final] at ⊢
  obtain ⟨receipt⟩ := SourceInference.ForStatementInferenceContinuation.of_accepted form accepted
  have actualInit := receipt.initialization
  rw [allocation] at actualInit
  have sameInit := Except.ok.inj (actualInit.symm.trans initializerAccepted)
  have actualTest := receipt.tested
  rw [sameInit] at actualTest
  have sameTest := Except.ok.inj (actualTest.symm.trans conditionAccepted)
  have sameTestState : receipt.testState = conditionState := congrArg Prod.snd sameTest
  have sameTestValue : receipt.test = conditionValue := congrArg Prod.fst sameTest
  have actualBody := receipt.bodyAccepted
  rw [sameTestState] at actualBody
  have sameBody := Except.ok.inj (actualBody.symm.trans child)
  simpa only [sameBody] using (forProgress receipt inputs).2.2.1

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
    (inputs : (CallIndex.statement (fuel + 1) context source expectedReturn initial result).Inputs) :
    (CallIndex.forItems fuel { context with loopDepth := context.loopDepth + 1 } post (bodyResult.state.restoreLexicalScope initialized.state.lexicalScope) postResult).final.InferenceProgress (CallIndex.statement (fuel + 1) context source expectedReturn initial result).final := by
  simp only [CallIndex.Accepted] at accepted child
  dsimp only [CallIndex.final] at ⊢
  obtain ⟨receipt⟩ := SourceInference.ForStatementInferenceContinuation.of_accepted form accepted
  have actualInit := receipt.initialization
  rw [allocation] at actualInit
  have sameInit := Except.ok.inj (actualInit.symm.trans initializerAccepted)
  have actualTest := receipt.tested
  rw [sameInit] at actualTest
  have sameTest := Except.ok.inj (actualTest.symm.trans conditionAccepted)
  have sameTestState : receipt.testState = conditionState := congrArg Prod.snd sameTest
  have sameTestValue : receipt.test = conditionValue := congrArg Prod.fst sameTest
  have actualBody := receipt.bodyAccepted
  rw [sameTestState] at actualBody
  have sameBody := Except.ok.inj (actualBody.symm.trans bodyAccepted)
  have actualPost := receipt.postAccepted
  rw [sameInit, sameBody] at actualPost
  have samePost := Except.ok.inj (actualPost.symm.trans child)
  simpa only [samePost] using (forProgress receipt inputs).2.2.2

end ActualSuffixProgress
end Solcore.SourceSemantics.SourceInferenceExecution
