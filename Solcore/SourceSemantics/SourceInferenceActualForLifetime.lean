import Solcore.SourceSemantics.SourceInferenceActualCallInputTraversal
import Solcore.SourceSemantics.SourceInferenceGeneralizationLifetimeForLoopSteps

/-! The real for receipt identifies all four indexed child results. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceExecution
open Frontend SourceInference TypeSystem Detail SourceInferenceSoundness.ProtectedVariables
namespace ActualStatementLifetime
variable {whole : TypedSource} {finalSubstitution : Substitution}
    {binder : TypedBinder} {initializerId : ExpressionId}
    {event : RetainedGeneralization whole finalSubstitution binder initializerId}

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
    (lifetime : GeneralizationLifetime event (CallIndex.forItems fuel context initializer allocated initialized).initial.inference.next (CallIndex.forItems fuel context initializer allocated initialized).final (CallIndex.forItems fuel context initializer allocated initialized).outputTypes) :
    GeneralizationLifetime event (CallIndex.statement (fuel + 1) context source expectedReturn initial result).initial.inference.next (CallIndex.statement (fuel + 1) context source expectedReturn initial result).final (CallIndex.statement (fuel + 1) context source expectedReturn initial result).outputTypes := by
  simp only [CallIndex.Accepted] at accepted child
  dsimp only [CallIndex.initial, CallIndex.final, CallIndex.outputTypes] at lifetime ⊢
  obtain ⟨receipt⟩ := SourceInference.ForStatementInferenceContinuation.of_accepted form accepted
  have actualInit := receipt.initialization
  rw [allocation] at actualInit
  have sameInit := Except.ok.inj (actualInit.symm.trans child)
  have sameNext : allocated.inference.next = initial.inference.next := by
    rw [← show initial.allocateStatementId.2 = allocated from congrArg Prod.snd allocation]; rfl
  exact GeneralizationLifetime.forLoop_initializer receipt inputs.ready inputs.wellFormed inputs.catalog inputs.bounds (by simpa only [allocation, sameInit, sameNext] using lifetime)

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
    (lifetime : GeneralizationLifetime event (CallIndex.expression fuel context condition (some .bool) initialized.state conditionValue conditionState).initial.inference.next (CallIndex.expression fuel context condition (some .bool) initialized.state conditionValue conditionState).final (CallIndex.expression fuel context condition (some .bool) initialized.state conditionValue conditionState).outputTypes) :
    GeneralizationLifetime event (CallIndex.statement (fuel + 1) context source expectedReturn initial result).initial.inference.next (CallIndex.statement (fuel + 1) context source expectedReturn initial result).final (CallIndex.statement (fuel + 1) context source expectedReturn initial result).outputTypes := by
  simp only [CallIndex.Accepted] at accepted child
  dsimp only [CallIndex.initial, CallIndex.final, CallIndex.outputTypes] at lifetime ⊢
  obtain ⟨receipt⟩ := SourceInference.ForStatementInferenceContinuation.of_accepted form accepted
  have actualInit := receipt.initialization
  rw [allocation] at actualInit
  have sameInit := Except.ok.inj (actualInit.symm.trans initializerAccepted)
  have actualTest := receipt.tested
  rw [sameInit] at actualTest
  have sameTest := Except.ok.inj (actualTest.symm.trans child)
  have sameTestState : receipt.testState = conditionState := congrArg Prod.snd sameTest
  have sameTestValue : receipt.test = conditionValue := congrArg Prod.fst sameTest
  exact GeneralizationLifetime.forLoop_condition receipt inputs.ready inputs.wellFormed inputs.catalog inputs.bounds (by simpa only [sameInit, sameTestState, sameTestValue] using lifetime)

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
    (lifetime : GeneralizationLifetime event (CallIndex.statements fuel { context with loopDepth := context.loopDepth + 1 } body.value expectedReturn conditionState bodyResult).initial.inference.next (CallIndex.statements fuel { context with loopDepth := context.loopDepth + 1 } body.value expectedReturn conditionState bodyResult).final (CallIndex.statements fuel { context with loopDepth := context.loopDepth + 1 } body.value expectedReturn conditionState bodyResult).outputTypes) :
    GeneralizationLifetime event (CallIndex.statement (fuel + 1) context source expectedReturn initial result).initial.inference.next (CallIndex.statement (fuel + 1) context source expectedReturn initial result).final (CallIndex.statement (fuel + 1) context source expectedReturn initial result).outputTypes := by
  simp only [CallIndex.Accepted] at accepted child
  dsimp only [CallIndex.initial, CallIndex.final, CallIndex.outputTypes] at lifetime ⊢
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
  exact GeneralizationLifetime.forLoop_body receipt inputs.ready inputs.wellFormed inputs.catalog inputs.bounds (by simpa only [sameTestState, sameBody] using lifetime)

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
    (lifetime : GeneralizationLifetime event (CallIndex.forItems fuel { context with loopDepth := context.loopDepth + 1 } post (bodyResult.state.restoreLexicalScope initialized.state.lexicalScope) postResult).initial.inference.next (CallIndex.forItems fuel { context with loopDepth := context.loopDepth + 1 } post (bodyResult.state.restoreLexicalScope initialized.state.lexicalScope) postResult).final (CallIndex.forItems fuel { context with loopDepth := context.loopDepth + 1 } post (bodyResult.state.restoreLexicalScope initialized.state.lexicalScope) postResult).outputTypes) :
    GeneralizationLifetime event (CallIndex.statement (fuel + 1) context source expectedReturn initial result).initial.inference.next (CallIndex.statement (fuel + 1) context source expectedReturn initial result).final (CallIndex.statement (fuel + 1) context source expectedReturn initial result).outputTypes := by
  simp only [CallIndex.Accepted] at accepted child
  dsimp only [CallIndex.initial, CallIndex.final, CallIndex.outputTypes] at lifetime ⊢
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
  exact GeneralizationLifetime.forLoop_post receipt inputs.ready inputs.wellFormed inputs.catalog inputs.bounds (by simpa only [sameInit, sameBody, samePost, State.restoreLexicalScope] using lifetime)

end ActualStatementLifetime
end Solcore.SourceSemantics.SourceInferenceExecution
