import Solcore.SourceSemantics.SourceInferenceActualCallInputTraversal

/-! The last actual child and pure recording/restoration preserve inference state. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceExecution
open Frontend SourceInference TypeSystem Detail SourceInferenceSoundness.ProtectedVariables
namespace ActualSuffixProgress

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
    (inputs : (CallIndex.statement (fuel + 1) context source expectedReturn initial result).Inputs) :
    (CallIndex.expression fuel context initializer expected allocated value final).final.InferenceProgress (CallIndex.statement (fuel + 1) context source expectedReturn initial result).final := by
  have step : ChildStep (CallIndex.statement (fuel + 1) context source expectedReturn initial result) (CallIndex.expression fuel context initializer expected allocated value final) := .statement_initializer accepted form allocation annotation child
  have childReady := ((step.inputs inputs).progress child).2.1
  simp only [CallIndex.Accepted] at accepted child
  dsimp only [CallIndex.final] at childReady ⊢
  cases annotation
  all_goals unfold inferStatementFuel at accepted
  all_goals simp_all only [bind, Except.bind, pure, Pure.pure, Except.pure]
  all_goals first
  | (cases Except.ok.inj accepted; exact .of_inference_eq childReady.solved rfl)
  | skip

theorem statement_return
      {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Statement}
      {expectedReturn : Ty} {initial allocated : State} {id : StatementId}
      {result : StatementResult}
      {value : Syntax.Expr} {inferred : InferredExpression} {final : State}
      (accepted : (CallIndex.statement (fuel + 1) context source expectedReturn initial result).Accepted)
      (form : source.value = .returnStmt (some value))
      (allocation : initial.allocateStatementId = (id, allocated))
      (child : (CallIndex.expression fuel context value (some expectedReturn) allocated inferred final).Accepted)
    (inputs : (CallIndex.statement (fuel + 1) context source expectedReturn initial result).Inputs) :
    (CallIndex.expression fuel context value (some expectedReturn) allocated inferred final).final.InferenceProgress (CallIndex.statement (fuel + 1) context source expectedReturn initial result).final := by
  have step : ChildStep (CallIndex.statement (fuel + 1) context source expectedReturn initial result) (CallIndex.expression fuel context value (some expectedReturn) allocated inferred final) := .statement_return accepted form allocation child
  have childReady := ((step.inputs inputs).progress child).2.1
  simp only [CallIndex.Accepted] at accepted child
  dsimp only [CallIndex.final] at childReady ⊢
  unfold inferStatementFuel at accepted
  simp only [form, allocation, child, bind, Except.bind, pure, Pure.pure, Except.pure, Except.ok.injEq] at accepted
  cases accepted
  exact .of_inference_eq childReady.solved rfl

theorem statement_expression
      {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Statement}
      {expectedReturn : Ty} {initial allocated : State} {id : StatementId}
      {result : StatementResult}
      {value : Syntax.Expr} {semicolon : Bool} {inferred : InferredExpression} {final : State}
      (accepted : (CallIndex.statement (fuel + 1) context source expectedReturn initial result).Accepted)
      (form : source.value = .expression value semicolon)
      (allocation : initial.allocateStatementId = (id, allocated))
      (child : (CallIndex.expression fuel context value none allocated inferred final).Accepted)
    (inputs : (CallIndex.statement (fuel + 1) context source expectedReturn initial result).Inputs) :
    (CallIndex.expression fuel context value none allocated inferred final).final.InferenceProgress (CallIndex.statement (fuel + 1) context source expectedReturn initial result).final := by
  have step : ChildStep (CallIndex.statement (fuel + 1) context source expectedReturn initial result) (CallIndex.expression fuel context value none allocated inferred final) := .statement_expression accepted form allocation child
  have childReady := ((step.inputs inputs).progress child).2.1
  simp only [CallIndex.Accepted] at accepted child
  dsimp only [CallIndex.final] at childReady ⊢
  unfold inferStatementFuel at accepted
  simp only [form, allocation, child, bind, Except.bind, pure, Pure.pure, Except.pure, Except.ok.injEq] at accepted
  cases accepted
  exact .of_inference_eq childReady.solved rfl

theorem statement_block
      {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Statement}
      {expectedReturn : Ty} {initial allocated : State} {id : StatementId}
      {result : StatementResult}
      {body : List Syntax.Statement} {bodyResult : BlockResult}
      (accepted : (CallIndex.statement (fuel + 1) context source expectedReturn initial result).Accepted)
      (form : source.value = .block body)
      (allocation : initial.allocateStatementId = (id, allocated))
      (child : (CallIndex.statements fuel context body expectedReturn allocated bodyResult).Accepted)
    (inputs : (CallIndex.statement (fuel + 1) context source expectedReturn initial result).Inputs) :
    (CallIndex.statements fuel context body expectedReturn allocated bodyResult).final.InferenceProgress (CallIndex.statement (fuel + 1) context source expectedReturn initial result).final := by
  have step : ChildStep (CallIndex.statement (fuel + 1) context source expectedReturn initial result) (CallIndex.statements fuel context body expectedReturn allocated bodyResult) := .statement_block accepted form allocation child
  have childReady := ((step.inputs inputs).progress child).2.1
  simp only [CallIndex.Accepted] at accepted child
  dsimp only [CallIndex.final] at childReady ⊢
  unfold inferStatementFuel at accepted
  simp only [form, allocation, child, bind, Except.bind, pure, Pure.pure, Except.pure, Except.ok.injEq] at accepted
  cases accepted
  exact .of_inference_eq childReady.solved rfl

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
    (inputs : (CallIndex.statement (fuel + 1) context source expectedReturn initial result).Inputs) :
    (CallIndex.assignedValue fuel context target operator.value value allocated assignment inferred final).final.InferenceProgress (CallIndex.statement (fuel + 1) context source expectedReturn initial result).final := by
  have step : ChildStep (CallIndex.statement (fuel + 1) context source expectedReturn initial result) (CallIndex.assignedValue fuel context target operator.value value allocated assignment inferred final) := .statement_assignment accepted form allocation child
  have childReady := ((step.inputs inputs).progress child).2.1
  simp only [CallIndex.Accepted] at accepted child
  dsimp only [CallIndex.final] at childReady ⊢
  unfold inferStatementFuel at accepted
  simp only [form, allocation, child, bind, Except.bind, pure, Pure.pure, Except.pure, Except.ok.injEq] at accepted
  cases accepted
  exact .of_inference_eq childReady.solved rfl

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
    (inputs : (CallIndex.statement (fuel + 1) context source expectedReturn initial result).Inputs) :
    (CallIndex.statements fuel { context with loopDepth := context.loopDepth + 1 } body.value expectedReturn conditionState bodyResult).final.InferenceProgress (CallIndex.statement (fuel + 1) context source expectedReturn initial result).final := by
  have step : ChildStep (CallIndex.statement (fuel + 1) context source expectedReturn initial result) (CallIndex.statements fuel { context with loopDepth := context.loopDepth + 1 } body.value expectedReturn conditionState bodyResult) := .statement_while_body accepted form allocation conditionAccepted child
  have childReady := ((step.inputs inputs).progress child).2.1
  simp only [CallIndex.Accepted] at accepted child
  dsimp only [CallIndex.final] at childReady ⊢
  unfold inferStatementFuel at accepted
  simp only [form, allocation, conditionAccepted, child, bind, Except.bind, pure, Pure.pure, Except.pure, Except.ok.injEq] at accepted
  cases accepted
  exact .of_inference_eq childReady.solved rfl

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
    (inputs : (CallIndex.statement (fuel + 1) context source expectedReturn initial result).Inputs) :
    (CallIndex.statements fuel context body.value expectedReturn (thenResult.state.restoreLexicalScope conditionState.lexicalScope) elseResult).final.InferenceProgress (CallIndex.statement (fuel + 1) context source expectedReturn initial result).final := by
  have step : ChildStep (CallIndex.statement (fuel + 1) context source expectedReturn initial result) (CallIndex.statements fuel context body.value expectedReturn (thenResult.state.restoreLexicalScope conditionState.lexicalScope) elseResult) := .statement_if_else accepted form allocation conditionAccepted hasElse thenAccepted child
  have childReady := ((step.inputs inputs).progress child).2.1
  simp only [CallIndex.Accepted] at accepted child
  dsimp only [CallIndex.final] at childReady ⊢
  subst elseBody
  unfold inferStatementFuel at accepted
  simp only [form, allocation, conditionAccepted, thenAccepted, child, bind, Except.bind, pure, Pure.pure, Except.pure, Except.ok.injEq] at accepted
  cases accepted
  exact .of_inference_eq childReady.solved rfl

theorem forItem_initializer
      {fuel : Nat} {context : SourceInference.Context} {source : Syntax.ForItem}
      {initial final : State} {result : ForItemForm}
      {name : Syntax.Identifier} {sourceType : Option Syntax.TypeExpr} {initializer : Syntax.Expr}
      {expected : Option Ty} {value : InferredExpression} {childFinal : State}
      (accepted : (CallIndex.forItem (fuel + 1) context source initial result final).Accepted)
      (form : source.value = .letDecl name sourceType (some initializer))
      (annotation : AnnotationExpected context sourceType expected)
      (child : (CallIndex.expression fuel context initializer expected initial value childFinal).Accepted)
    (inputs : (CallIndex.forItem (fuel + 1) context source initial result final).Inputs) :
    (CallIndex.expression fuel context initializer expected initial value childFinal).final.InferenceProgress (CallIndex.forItem (fuel + 1) context source initial result final).final := by
  have step : ChildStep (CallIndex.forItem (fuel + 1) context source initial result final) (CallIndex.expression fuel context initializer expected initial value childFinal) := .forItem_initializer accepted form annotation child
  have childReady := ((step.inputs inputs).progress child).2.1
  simp only [CallIndex.Accepted] at accepted child
  dsimp only [CallIndex.final] at childReady ⊢
  cases annotation
  all_goals unfold inferForItemFuel at accepted
  all_goals simp_all only [bind, Except.bind, pure, Pure.pure, Except.pure]
  all_goals first
  | (cases Except.ok.inj accepted; exact .of_inference_eq childReady.solved rfl)
  | skip

theorem forItem_expression
      {fuel : Nat} {context : SourceInference.Context} {source : Syntax.ForItem}
      {initial final : State} {result : ForItemForm}
      {value : Syntax.Expr} {inferred : InferredExpression} {childFinal : State}
      (accepted : (CallIndex.forItem (fuel + 1) context source initial result final).Accepted)
      (form : source.value = .expression value)
      (child : (CallIndex.expression fuel context value none initial inferred childFinal).Accepted)
    (inputs : (CallIndex.forItem (fuel + 1) context source initial result final).Inputs) :
    (CallIndex.expression fuel context value none initial inferred childFinal).final.InferenceProgress (CallIndex.forItem (fuel + 1) context source initial result final).final := by
  have step : ChildStep (CallIndex.forItem (fuel + 1) context source initial result final) (CallIndex.expression fuel context value none initial inferred childFinal) := .forItem_expression accepted form child
  have childReady := ((step.inputs inputs).progress child).2.1
  simp only [CallIndex.Accepted] at accepted child
  dsimp only [CallIndex.final] at childReady ⊢
  unfold inferForItemFuel at accepted
  simp only [form, child, bind, Except.bind, pure, Pure.pure, Except.pure, Except.ok.injEq] at accepted
  cases accepted
  exact .of_inference_eq childReady.solved rfl

theorem forItem_assignment
      {fuel : Nat} {context : SourceInference.Context} {source : Syntax.ForItem}
      {initial final : State} {result : ForItemForm}
      {target value : Syntax.Expr} {operator : Syntax.Located Syntax.ValueAssignOp}
      {assignment : AssignmentResolution} {inferred : InferredExpression} {childFinal : State}
      (accepted : (CallIndex.forItem (fuel + 1) context source initial result final).Accepted)
      (form : source.value = .assignValue target operator value)
      (child : (CallIndex.assignedValue fuel context target operator.value value initial assignment inferred childFinal).Accepted)
    (inputs : (CallIndex.forItem (fuel + 1) context source initial result final).Inputs) :
    (CallIndex.assignedValue fuel context target operator.value value initial assignment inferred childFinal).final.InferenceProgress (CallIndex.forItem (fuel + 1) context source initial result final).final := by
  have step : ChildStep (CallIndex.forItem (fuel + 1) context source initial result final) (CallIndex.assignedValue fuel context target operator.value value initial assignment inferred childFinal) := .forItem_assignment accepted form child
  have childReady := ((step.inputs inputs).progress child).2.1
  simp only [CallIndex.Accepted] at accepted child
  dsimp only [CallIndex.final] at childReady ⊢
  unfold inferForItemFuel at accepted
  simp only [form, child, bind, Except.bind, pure, Pure.pure, Except.pure, Except.ok.injEq] at accepted
  cases accepted
  exact .of_inference_eq childReady.solved rfl

theorem place_group
      {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Expr}
      {initial final : State} {result : PlaceResolution}
      {inner : Syntax.Expr} {value : PlaceResolution} {childFinal : State}
      (accepted : (CallIndex.place (fuel + 1) context source initial result final).Accepted)
      (form : source.value = .group inner)
      (child : (CallIndex.place fuel context inner initial value childFinal).Accepted)
    (inputs : (CallIndex.place (fuel + 1) context source initial result final).Inputs) :
    (CallIndex.place fuel context inner initial value childFinal).final.InferenceProgress (CallIndex.place (fuel + 1) context source initial result final).final := by
  have step : ChildStep (CallIndex.place (fuel + 1) context source initial result final) (CallIndex.place fuel context inner initial value childFinal) := .place_group accepted form child
  have childReady := ((step.inputs inputs).progress child).2.1
  simp only [CallIndex.Accepted] at accepted child
  dsimp only [CallIndex.final] at childReady ⊢
  unfold inferPlaceFuel at accepted
  simp only [form, child] at accepted
  cases accepted
  exact .of_inference_eq childReady.solved rfl

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
    (inputs : (CallIndex.place (fuel + 1) context source initial result final).Inputs) :
    (CallIndex.expression fuel context key (some (fitted.resolve keyType)) fitted keyValue childFinal).final.InferenceProgress (CallIndex.place (fuel + 1) context source initial result final).final := by
  have step : ChildStep (CallIndex.place (fuel + 1) context source initial result final) (CallIndex.expression fuel context key (some (fitted.resolve keyType)) fitted keyValue childFinal) := .place_index_key accepted form baseAccepted keyFresh valueFresh fitting child
  have childReady := ((step.inputs inputs).progress child).2.1
  simp only [CallIndex.Accepted] at accepted child
  dsimp only [CallIndex.final] at childReady ⊢
  unfold inferPlaceFuel at accepted
  simp only [form, baseAccepted, keyFresh, valueFresh, fitting, child, bind, Except.bind, pure, Pure.pure, Except.pure, Except.ok.injEq] at accepted
  cases accepted
  exact .of_inference_eq childReady.solved rfl

theorem constructorArguments_tail
      {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Expr} {sources : List Syntax.Expr}
      {expected : Ty} {expectedTypes : List Ty} {initial middle final : State}
      {values : List InferredExpression} {value : InferredExpression}
      {tailValues : List InferredExpression} {tailFinal : State}
      (accepted : (CallIndex.constructorArguments fuel context (source :: sources) (expected :: expectedTypes) initial values final).Accepted)
      (headAccepted : inferExprFuel fuel context source (some (initial.resolve expected)) initial = .ok (value, middle))
      (child : (CallIndex.constructorArguments fuel context sources expectedTypes middle tailValues tailFinal).Accepted)
    (inputs : (CallIndex.constructorArguments fuel context (source :: sources) (expected :: expectedTypes) initial values final).Inputs) :
    (CallIndex.constructorArguments fuel context sources expectedTypes middle tailValues tailFinal).final.InferenceProgress (CallIndex.constructorArguments fuel context (source :: sources) (expected :: expectedTypes) initial values final).final := by
  have step : ChildStep (CallIndex.constructorArguments fuel context (source :: sources) (expected :: expectedTypes) initial values final) (CallIndex.constructorArguments fuel context sources expectedTypes middle tailValues tailFinal) := .constructorArguments_tail accepted headAccepted child
  have childReady := ((step.inputs inputs).progress child).2.1
  simp only [CallIndex.Accepted] at accepted child
  dsimp only [CallIndex.final] at childReady ⊢
  unfold inferConstructorArgumentsFuel at accepted
  simp only [headAccepted, child, bind, Except.bind, pure, Pure.pure, Except.pure, Except.ok.injEq] at accepted
  cases accepted
  exact .of_inference_eq childReady.solved rfl

theorem expressions_tail
      {fuel : Nat} {context : SourceInference.Context}
      {source : Syntax.Expr} {sources : List Syntax.Expr}
      {initial middle final tailFinal : State} {value : InferredExpression}
      {values tailValues : List InferredExpression}
      (accepted : (CallIndex.expressions (fuel + 1) context (source :: sources)
        initial values final).Accepted)
      (head : inferExprFuel fuel context source none initial = .ok (value, middle))
      (child : inferExprsFuel fuel context sources middle = .ok (tailValues, tailFinal))
    (inputs : (CallIndex.expressions (fuel + 1) context (source :: sources) initial values final).Inputs) :
    (CallIndex.expressions fuel context sources middle tailValues tailFinal).final.InferenceProgress (CallIndex.expressions (fuel + 1) context (source :: sources) initial values final).final := by
  have step : ChildStep (CallIndex.expressions (fuel + 1) context (source :: sources) initial values final) (CallIndex.expressions fuel context sources middle tailValues tailFinal) := .expressions_tail accepted head child
  have childReady := ((step.inputs inputs).progress child).2.1
  simp only [CallIndex.Accepted] at accepted child
  dsimp only [CallIndex.final] at childReady ⊢
  unfold inferExprsFuel at accepted
  simp only [head, child, bind, Except.bind, pure, Pure.pure, Except.pure, Except.ok.injEq] at accepted
  cases accepted
  exact .of_inference_eq childReady.solved rfl

theorem forItems_tail
      {fuel : Nat} {context : SourceInference.Context}
      {source : Syntax.ForItem} {sources : List Syntax.ForItem} {initial middle : State}
      {result tail : InferredForItems} {head : ForItemForm}
      (accepted : (CallIndex.forItems fuel context (source :: sources) initial result).Accepted)
      (headAccepted : inferForItemFuel fuel context source initial = .ok (head, middle))
      (child : (CallIndex.forItems fuel context sources middle tail).Accepted)
    (inputs : (CallIndex.forItems fuel context (source :: sources) initial result).Inputs) :
    (CallIndex.forItems fuel context sources middle tail).final.InferenceProgress (CallIndex.forItems fuel context (source :: sources) initial result).final := by
  have step : ChildStep (CallIndex.forItems fuel context (source :: sources) initial result) (CallIndex.forItems fuel context sources middle tail) := .forItems_tail accepted headAccepted child
  have childReady := ((step.inputs inputs).progress child).2.1
  simp only [CallIndex.Accepted] at accepted child
  dsimp only [CallIndex.final] at childReady ⊢
  unfold inferForItemsFuel at accepted
  simp only [headAccepted, child, bind, Except.bind, pure, Pure.pure, Except.pure, Except.ok.injEq] at accepted
  cases accepted
  exact .of_inference_eq childReady.solved rfl

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
    (inputs : (CallIndex.matchCases (fuel + 1) context scrutineeType expectedReturn saved (arm :: arms) initial result).Inputs) :
    (CallIndex.matchCases fuel context scrutineeType expectedReturn saved arms (body.state.restoreLexicalScope saved) tail).final.InferenceProgress (CallIndex.matchCases (fuel + 1) context scrutineeType expectedReturn saved (arm :: arms) initial result).final := by
  have step : ChildStep (CallIndex.matchCases (fuel + 1) context scrutineeType expectedReturn saved (arm :: arms) initial result) (CallIndex.matchCases fuel context scrutineeType expectedReturn saved arms (body.state.restoreLexicalScope saved) tail) := .matchCases_tail accepted patternAccepted bodyAccepted child
  have childReady := ((step.inputs inputs).progress child).2.1
  simp only [CallIndex.Accepted] at accepted child
  dsimp only [CallIndex.final] at childReady ⊢
  unfold inferMatchCasesFuel at accepted
  simp only [patternAccepted, bodyAccepted, child, bind, Except.bind, pure, Pure.pure, Except.pure, Except.ok.injEq] at accepted
  cases accepted
  exact .of_inference_eq childReady.solved rfl

end ActualSuffixProgress
end Solcore.SourceSemantics.SourceInferenceExecution
