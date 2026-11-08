import Solcore.SourceSemantics.Internal.Execution.CallInputs
import Solcore.SourceSemantics.Internal.Privacy.Lifetimes
import Solcore.Frontend.SourceInference.Internal.Continuations
import Solcore.SourceSemantics.Internal.Execution.CallGraph
import Solcore.SourceSemantics.Internal.Privacy.LifetimeMatches

/-!
# Progress of statements

Each statement child continues to the final state of its root call, with its lifetime.
-/

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceActualTerminalProgress
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
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceActualBranchProgress
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
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceActualForLifetime
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
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceActualForProgress
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
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceActualListLifetime
/-! Exact child edges lift lifetimes through ordered expression and statement lists. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceExecution
open Frontend SourceInference TypeSystem Detail SourceInferenceSoundness.ProtectedVariables
variable {whole : TypedSource} {finalSubstitution : Substitution}
    {binder : TypedBinder} {initializer : ExpressionId}
    {event : RetainedGeneralization whole finalSubstitution binder initializer}

private theorem expressionsHead
    {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Expr} {sources : List Syntax.Expr}
    {initial : State} {head : InferredExpression × State} {result : List InferredExpression × State}
    (inputs : (CallIndex.expressions (fuel + 1) context (source :: sources) initial result.1 result.2).Inputs)
    (accepted : inferExprsFuel (fuel + 1) context (source :: sources) initial = .ok result)
    (headAccepted : inferExprFuel fuel context source none initial = .ok head)
    (lifetime : GeneralizationLifetime event initial.inference.next head.2 [head.1.type]) :
    GeneralizationLifetime event initial.inference.next result.2 (result.1.map (·.type)) := by
  cases tailAccepted : inferExprsFuel fuel context sources head.2 with
  | error error => simp [inferExprsFuel, headAccepted, tailAccepted, bind, Except.bind] at accepted
  | ok tail => exact lifetime.expressions_head inputs.ready inputs.wellFormed inputs.catalog headAccepted tailAccepted accepted

private theorem constructorArgumentsHead
    {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Expr} {sources : List Syntax.Expr}
    {expected : Ty} {expectedTypes : List Ty} {initial : State}
    {head : InferredExpression × State} {result : List InferredExpression × State}
    (inputs : (CallIndex.constructorArguments fuel context (source :: sources) (expected :: expectedTypes) initial result.1 result.2).Inputs)
    (accepted : inferConstructorArgumentsFuel fuel context (source :: sources) (expected :: expectedTypes) initial = .ok result)
    (headAccepted : inferExprFuel fuel context source (some (initial.resolve expected)) initial = .ok head)
    (lifetime : GeneralizationLifetime event initial.inference.next head.2 [head.1.type]) :
    GeneralizationLifetime event initial.inference.next result.2 (result.1.map (·.type)) := by
  cases tailAccepted : inferConstructorArgumentsFuel fuel context sources expectedTypes head.2 with
  | error error => simp [inferConstructorArgumentsFuel, headAccepted, tailAccepted, bind, Except.bind] at accepted
  | ok tail => exact lifetime.constructorArguments_head inputs.ready inputs.wellFormed inputs.catalog inputs.bounds headAccepted tailAccepted accepted

private theorem statementsHead
    {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Statement} {sources : List Syntax.Statement}
    {expectedReturn : Ty} {initial : State} {head : StatementResult} {result : BlockResult}
    (inputs : (CallIndex.statements (fuel + 1) context (source :: sources) expectedReturn initial result).Inputs)
    (accepted : inferStatementsFuel (fuel + 1) context (source :: sources) expectedReturn initial = .ok result)
    (headAccepted : inferStatementFuel fuel context source expectedReturn initial = .ok head)
    (lifetime : GeneralizationLifetime event initial.inference.next head.state [head.type]) :
    GeneralizationLifetime event initial.inference.next result.state [result.type] := by
  cases sources with
  | nil => exact lifetime.statements_single headAccepted accepted
  | cons next rest =>
    cases tailAccepted : inferStatementsFuel fuel context (next :: rest) expectedReturn head.state with
    | error error => simp [inferStatementsFuel, headAccepted, tailAccepted, bind, Except.bind] at accepted
    | ok tail => exact lifetime.statements_head inputs.ready inputs.wellFormed inputs.catalog inputs.bounds headAccepted tailAccepted accepted

private theorem forItemsHead
    {fuel : Nat} {context : SourceInference.Context} {source : Syntax.ForItem} {sources : List Syntax.ForItem}
    {initial : State} {head : ForItemForm × State} {result : InferredForItems}
    (inputs : (CallIndex.forItems fuel context (source :: sources) initial result).Inputs)
    (accepted : inferForItemsFuel fuel context (source :: sources) initial = .ok result)
    (headAccepted : inferForItemFuel fuel context source initial = .ok head)
    (lifetime : GeneralizationLifetime event initial.inference.next head.2 []) :
    GeneralizationLifetime event initial.inference.next result.state [] := by
  cases tailAccepted : inferForItemsFuel fuel context sources head.2 with
  | error error => simp [inferForItemsFuel, headAccepted, tailAccepted, bind, Except.bind] at accepted
  | ok tail => exact lifetime.forItems_head inputs.ready inputs.wellFormed inputs.catalog headAccepted tailAccepted accepted

namespace ChildStep

theorem lifetime_expressions
    {fuel : Nat} {context : SourceInference.Context} {sources : List Syntax.Expr}
    {initial final : State} {values : List InferredExpression} {child : CallIndex}
    (inputs : (CallIndex.expressions fuel context sources initial values final).Inputs)
    (step : ChildStep (.expressions fuel context sources initial values final) child)
    (lifetime : GeneralizationLifetime event child.initial.inference.next child.final child.outputTypes) :
    GeneralizationLifetime event initial.inference.next final (values.map (·.type)) := by
  cases step with
  | expressions_head accepted headAccepted => exact expressionsHead inputs accepted headAccepted lifetime
  | expressions_tail accepted headAccepted tailAccepted =>
      exact lifetime.expressions_tail inputs.ready inputs.catalog headAccepted tailAccepted accepted

theorem lifetime_constructorArguments
    {fuel : Nat} {context : SourceInference.Context} {sources : List Syntax.Expr} {expectedTypes : List Ty}
    {initial final : State} {values : List InferredExpression} {child : CallIndex}
    (inputs : (CallIndex.constructorArguments fuel context sources expectedTypes initial values final).Inputs)
    (step : ChildStep (.constructorArguments fuel context sources expectedTypes initial values final) child)
    (lifetime : GeneralizationLifetime event child.initial.inference.next child.final child.outputTypes) :
    GeneralizationLifetime event initial.inference.next final (values.map (·.type)) := by
  cases step with
  | constructorArguments_head accepted headAccepted => exact constructorArgumentsHead inputs accepted headAccepted lifetime
  | constructorArguments_tail accepted headAccepted tailAccepted =>
      exact lifetime.constructorArguments_tail inputs.ready inputs.catalog inputs.bounds headAccepted tailAccepted accepted

theorem lifetime_constructorApplication
    {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Expr} {id : ExpressionId}
    {instantiation : DataConstructorInstantiation} {arguments : List Syntax.Expr} {expected : Option Ty}
    {initial final : State} {value : InferredExpression} {child : CallIndex}
    (inputs : (CallIndex.constructorApplication fuel context source id instantiation arguments expected initial value final).Inputs)
    (step : ChildStep (.constructorApplication fuel context source id instantiation arguments expected initial value final) child)
    (lifetime : GeneralizationLifetime event child.initial.inference.next child.final child.outputTypes) :
    GeneralizationLifetime event initial.inference.next final [value.type] := by
  cases step with
  | constructorApplication_arguments accepted _ fitting childAccepted =>
      cases expected <;> exact lifetime.constructorApplication_arguments inputs.ready inputs.catalog inputs.bounds.1 inputs.bounds.2.1 inputs.bounds.2.2 fitting childAccepted accepted

theorem lifetime_statements
    {fuel : Nat} {context : SourceInference.Context} {sources : List Syntax.Statement} {expected : Ty}
    {initial : State} {result : BlockResult} {child : CallIndex}
    (inputs : (CallIndex.statements fuel context sources expected initial result).Inputs)
    (step : ChildStep (.statements fuel context sources expected initial result) child)
    (lifetime : GeneralizationLifetime event child.initial.inference.next child.final child.outputTypes) :
    GeneralizationLifetime event initial.inference.next result.state [result.type] := by
  cases step with
  | statements_head accepted headAccepted => exact statementsHead inputs accepted headAccepted lifetime
  | statements_tail accepted nonempty headAccepted tailAccepted =>
      rename_i rest _ _
      cases rest with
      | nil => exact False.elim (nonempty rfl)
      | cons next rest => exact lifetime.statements_tail inputs.ready inputs.catalog inputs.bounds headAccepted tailAccepted accepted

theorem lifetime_forItems
    {fuel : Nat} {context : SourceInference.Context} {sources : List Syntax.ForItem}
    {initial : State} {result : InferredForItems} {child : CallIndex}
    (inputs : (CallIndex.forItems fuel context sources initial result).Inputs)
    (step : ChildStep (.forItems fuel context sources initial result) child)
    (lifetime : GeneralizationLifetime event child.initial.inference.next child.final child.outputTypes) :
    GeneralizationLifetime event initial.inference.next result.state [] := by
  cases step with
  | forItems_head accepted headAccepted => exact forItemsHead inputs accepted headAccepted lifetime
  | forItems_tail accepted headAccepted tailAccepted =>
      exact lifetime.forItems_tail inputs.ready inputs.catalog headAccepted tailAccepted accepted

end ChildStep
end Solcore.SourceSemantics.SourceInferenceExecution
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceActualListProgress
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceExecution
open Frontend SourceInference TypeSystem Detail SourceInferenceSoundness.ProtectedVariables
namespace ActualSuffixProgress

theorem expressions_head
      {fuel : Nat} {context : SourceInference.Context}
      {source : Syntax.Expr} {sources : List Syntax.Expr}
      {initial middle final : State} {value : InferredExpression}
      {values : List InferredExpression}
      (accepted : (CallIndex.expressions (fuel + 1) context (source :: sources)
        initial values final).Accepted)
      (head : inferExprFuel fuel context source none initial = .ok (value, middle))
    (inputs : (CallIndex.expressions (fuel + 1) context (source :: sources) initial values final).Inputs) :
    (CallIndex.expression fuel context source none initial value middle).final.InferenceProgress (CallIndex.expressions (fuel + 1) context (source :: sources) initial values final).final := by
  simp only [CallIndex.Accepted] at accepted
  dsimp only [CallIndex.final] at ⊢
  cases tailAccepted : inferExprsFuel fuel context sources middle with
  | error error => simp [inferExprsFuel, head, tailAccepted, bind, Except.bind] at accepted
  | ok tail =>
    have after := ((ChildStep.expressions_tail accepted head tailAccepted).inputs inputs).progress tailAccepted
    exact after.1.trans (expressions_tail accepted head tailAccepted inputs)

theorem constructorArguments_head
      {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Expr} {sources : List Syntax.Expr}
      {expected : Ty} {expectedTypes : List Ty} {initial middle final : State}
      {values : List InferredExpression} {value : InferredExpression}
      (accepted : (CallIndex.constructorArguments fuel context (source :: sources) (expected :: expectedTypes) initial values final).Accepted)

      (child : (CallIndex.expression fuel context source (some (initial.resolve expected)) initial value middle).Accepted)
    (inputs : (CallIndex.constructorArguments fuel context (source :: sources) (expected :: expectedTypes) initial values final).Inputs) :
    (CallIndex.expression fuel context source (some (initial.resolve expected)) initial value middle).final.InferenceProgress (CallIndex.constructorArguments fuel context (source :: sources) (expected :: expectedTypes) initial values final).final := by
  simp only [CallIndex.Accepted] at accepted child
  dsimp only [CallIndex.final] at ⊢
  cases tailAccepted : inferConstructorArgumentsFuel fuel context sources expectedTypes middle with
  | error error => simp [inferConstructorArgumentsFuel, child, tailAccepted, bind, Except.bind] at accepted
  | ok tail =>
    have after := ((ChildStep.constructorArguments_tail accepted child tailAccepted).inputs inputs).progress tailAccepted
    exact after.1.trans (constructorArguments_tail accepted child tailAccepted inputs)

theorem forItems_head
      {fuel : Nat} {context : SourceInference.Context}
      {source : Syntax.ForItem} {sources : List Syntax.ForItem} {initial final : State}
      {result : InferredForItems} {value : ForItemForm}
      (accepted : (CallIndex.forItems fuel context (source :: sources) initial result).Accepted)

      (child : (CallIndex.forItem fuel context source initial value final).Accepted)
    (inputs : (CallIndex.forItems fuel context (source :: sources) initial result).Inputs) :
    (CallIndex.forItem fuel context source initial value final).final.InferenceProgress (CallIndex.forItems fuel context (source :: sources) initial result).final := by
  simp only [CallIndex.Accepted] at accepted child
  dsimp only [CallIndex.final] at ⊢
  cases tailAccepted : inferForItemsFuel fuel context sources final with
  | error error => simp [inferForItemsFuel, child, tailAccepted, bind, Except.bind] at accepted
  | ok tail =>
    have after := ((ChildStep.forItems_tail accepted child tailAccepted).inputs inputs).progress tailAccepted
    exact after.1.trans (forItems_tail accepted child tailAccepted inputs)

theorem statements_tail
      {fuel : Nat} {context : SourceInference.Context}
      {source : Syntax.Statement} {sources : List Syntax.Statement} {expectedReturn : Ty}
      {initial : State} {result tail : BlockResult} {head : StatementResult}
      (accepted : (CallIndex.statements (fuel + 1) context (source :: sources) expectedReturn initial result).Accepted)
      (nonempty : sources ≠ [])
      (headAccepted : inferStatementFuel fuel context source expectedReturn initial = .ok head)
      (child : (CallIndex.statements fuel context sources expectedReturn head.state tail).Accepted)
    (inputs : (CallIndex.statements (fuel + 1) context (source :: sources) expectedReturn initial result).Inputs) :
    (CallIndex.statements fuel context sources expectedReturn head.state tail).final.InferenceProgress (CallIndex.statements (fuel + 1) context (source :: sources) expectedReturn initial result).final := by
  simp only [CallIndex.Accepted] at accepted child
  dsimp only [CallIndex.final] at ⊢
  have childReady := ((ChildStep.statements_tail accepted nonempty headAccepted child).inputs inputs).progress child
  cases sources with
  | nil => exact False.elim (nonempty rfl)
  | cons next rest =>
    simp only [inferStatementsFuel, headAccepted, child, bind, Except.bind, pure, Pure.pure, Except.pure, Except.ok.injEq] at accepted
    cases accepted
    exact .of_inference_eq childReady.2.1.solved rfl

theorem statements_head
      {fuel : Nat} {context : SourceInference.Context}
      {source : Syntax.Statement} {sources : List Syntax.Statement} {expectedReturn : Ty}
      {initial : State} {result : BlockResult} {head : StatementResult}
      (accepted : (CallIndex.statements (fuel + 1) context (source :: sources) expectedReturn initial result).Accepted)

      (child : (CallIndex.statement fuel context source expectedReturn initial head).Accepted)
    (inputs : (CallIndex.statements (fuel + 1) context (source :: sources) expectedReturn initial result).Inputs) :
    (CallIndex.statement fuel context source expectedReturn initial head).final.InferenceProgress (CallIndex.statements (fuel + 1) context (source :: sources) expectedReturn initial result).final := by
  simp only [CallIndex.Accepted] at accepted child
  dsimp only [CallIndex.final] at ⊢
  cases sources with
  | nil =>
    have ready := ((ChildStep.statements_head accepted child).inputs inputs).progress child
    simp only [inferStatementsFuel, child, bind, Except.bind, pure, Pure.pure, Except.pure, Except.ok.injEq] at accepted
    cases accepted
    exact .of_inference_eq ready.2.1.solved rfl
  | cons next rest =>
    cases tailAccepted : inferStatementsFuel fuel context (next :: rest) expectedReturn head.state with
    | error error => simp [inferStatementsFuel, child, tailAccepted, bind, Except.bind] at accepted
    | ok tail =>
      have nonempty : next :: rest ≠ [] := List.cons_ne_nil _ _
      have after := ((ChildStep.statements_tail accepted nonempty child tailAccepted).inputs inputs).progress tailAccepted
      exact after.1.trans (statements_tail accepted nonempty child tailAccepted inputs)

end ActualSuffixProgress
end Solcore.SourceSemantics.SourceInferenceExecution
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceActualMatchProgress
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceExecution
open Frontend SourceInference TypeSystem Detail SourceInferenceSoundness.ProtectedVariables
namespace ActualSuffixProgress

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
    (inputs : (CallIndex.statement (fuel + 1) context source expectedReturn initial result).Inputs) :
    (CallIndex.statements fuel context body.value expectedReturn checked.state bodyResult).final.InferenceProgress (CallIndex.statement (fuel + 1) context source expectedReturn initial result).final := by
  simp only [CallIndex.Accepted] at accepted child
  dsimp only [CallIndex.final] at ⊢
  have ready := (((ChildStep.statement_match_default accepted form allocation scrutineeAccepted hiddenAllocation casesAccepted default child).inputs inputs).progress child).2.1
  have completion := matchCompletion_accepted form allocation scrutineeAccepted hiddenAllocation accepted
  unfold matchCompletion at completion
  simp only [casesAccepted, default, child, bind, Except.bind, pure, Pure.pure, Except.pure] at completion
  split at completion
  · contradiction
  · cases Except.ok.inj completion
    exact .of_inference_eq ready.solved rfl

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
    (inputs : (CallIndex.statement (fuel + 1) context source expectedReturn initial result).Inputs) :
    (CallIndex.matchCases fuel context scrutinee.type expectedReturn hiddenState.lexicalScope arms.value.cases hiddenState checked).final.InferenceProgress (CallIndex.statement (fuel + 1) context source expectedReturn initial result).final := by
  simp only [CallIndex.Accepted] at accepted child
  dsimp only [CallIndex.final] at ⊢
  have ready := (((ChildStep.statement_match_cases accepted form allocation scrutineeAccepted hiddenAllocation child).inputs inputs).progress child).2.1
  have completion := matchCompletion_accepted form allocation scrutineeAccepted hiddenAllocation accepted
  cases defaultEq : arms.value.defaultBody with
  | none =>
    unfold matchCompletion at completion
    simp only [child, defaultEq, bind, Except.bind, pure, Pure.pure, Except.pure] at completion
    split at completion
    · contradiction
    · cases Except.ok.inj completion
      exact .of_inference_eq ready.solved rfl
  | some body =>
    cases bodyAccepted : inferStatementsFuel fuel context body.value expectedReturn checked.state with
    | error error => simp [matchCompletion, child, defaultEq, bodyAccepted, bind, Except.bind] at completion
    | ok bodyResult =>
      have bodyProgress := ((ChildStep.statement_match_default accepted form allocation scrutineeAccepted hiddenAllocation child defaultEq bodyAccepted).inputs inputs).progress bodyAccepted
      exact bodyProgress.1.trans (statement_match_default accepted form allocation scrutineeAccepted hiddenAllocation child defaultEq bodyAccepted inputs)

private theorem afterScrutinee
    {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Statement}
    {scrutinees : Syntax.NonemptyDelimitedList Syntax.Expr} {arms : Syntax.MatchArms}
    {expectedReturn : Ty} {initial allocated : State} {id : StatementId}
    {scrutinee : InferredExpression} {scrutineeState : State} {result : StatementResult}
    (accepted : inferStatementFuel (fuel+1) context source expectedReturn initial = .ok result)
    (form : source.value = .matchWith scrutinees arms)
    (allocation : initial.allocateStatementId = (id, allocated))
    (scrutineeAccepted : matchScrutinee fuel context source.span scrutinees.elements.toList allocated = .ok (scrutinee, scrutineeState))
    (inputs : (CallIndex.statement (fuel+1) context source expectedReturn initial result).Inputs)
    (ready : scrutineeState.InferenceReady) : scrutineeState.InferenceProgress result.state := by
  let hidden := scrutineeState.allocateHiddenLocal.1
  let hiddenState := scrutineeState.allocateHiddenLocal.2
  have completion := matchCompletion_accepted form allocation scrutineeAccepted (show scrutineeState.allocateHiddenLocal = (hidden, hiddenState) from rfl) accepted
  cases casesAccepted : inferMatchCasesFuel fuel context scrutinee.type expectedReturn hiddenState.lexicalScope arms.value.cases hiddenState with
  | error error => simp [matchCompletion, casesAccepted, bind, Except.bind] at completion
  | ok checked =>
    have after := ((ChildStep.statement_match_cases accepted form allocation scrutineeAccepted rfl casesAccepted).inputs inputs).progress casesAccepted
    have hiddenProgress : scrutineeState.InferenceProgress hiddenState := .of_inference_eq ready.solved rfl
    exact hiddenProgress.trans (after.1.trans (statement_match_cases accepted form allocation scrutineeAccepted rfl casesAccepted inputs))

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
    (inputs : (CallIndex.statement (fuel + 1) context source expectedReturn initial result).Inputs) :
    (CallIndex.expression fuel context scrutinee none allocated value childFinal).final.InferenceProgress (CallIndex.statement (fuel + 1) context source expectedReturn initial result).final := by
  simp only [CallIndex.Accepted] at accepted child
  dsimp only [CallIndex.final] at ⊢
  have ready := (((ChildStep.statement_match_single accepted form allocation single child).inputs inputs).progress child).2.1
  have scrutineeAccepted : matchScrutinee fuel context source.span scrutinees.elements.toList allocated = .ok (value, childFinal) := by simpa only [matchScrutinee, single] using child
  exact afterScrutinee accepted form allocation scrutineeAccepted inputs ready

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
    (inputs : (CallIndex.statement (fuel + 1) context source expectedReturn initial result).Inputs) :
    (CallIndex.expressions fuel context scrutinees.elements.toList allocated values childFinal).final.InferenceProgress (CallIndex.statement (fuel + 1) context source expectedReturn initial result).final := by
  simp only [CallIndex.Accepted] at accepted child
  dsimp only [CallIndex.final] at ⊢
  have ready := (((ChildStep.statement_match_many accepted form allocation multiple child).inputs inputs).progress child).2.1
  let tuple : InferredExpression := ⟨childFinal.allocateExpressionId.1, Ty.productMany (values.map (·.type))⟩
  let tupleState := childFinal.allocateExpressionId.2.recordNode (.expression {
    id := tuple.id, span := source.span, type := tuple.type, form := .tuple (values.map (·.id)) })
  have scrutineeAccepted : matchScrutinee fuel context source.span scrutinees.elements.toList allocated = .ok (tuple, tupleState) := by
    unfold matchScrutinee
    split
    · rename_i sourceEq
      exact False.elim (multiple _ sourceEq)
    · simp only [child, bind, Except.bind, pure, Pure.pure, Except.pure]
      rfl
  have tupleReady : tupleState.InferenceReady := ready.allocateExpressionId.recordNode _
  have tupleProgress : childFinal.InferenceProgress tupleState := .of_inference_eq ready.solved rfl
  exact tupleProgress.trans (afterScrutinee accepted form allocation scrutineeAccepted inputs tupleReady)

end ActualSuffixProgress
end Solcore.SourceSemantics.SourceInferenceExecution
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceActualMutableLifetime
/-! Place, assigned-value and arm calls keep the exact child result and suffix. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceExecution
open Frontend SourceInference TypeSystem Detail SourceInferenceSoundness.ProtectedVariables
variable {whole : TypedSource} {finalSubstitution : Substitution}
    {binder : TypedBinder} {initializer : ExpressionId}
    {event : RetainedGeneralization whole finalSubstitution binder initializer}

private theorem placeBase
    {fuel : Nat} {context : SourceInference.Context} {source base key : Syntax.Expr}
    {brackets : Syntax.SourceSpan} {initial baseState : State} {baseValue : PlaceResolution}
    {result : PlaceResolution × State}
    (inputs : (CallIndex.place (fuel + 1) context source initial result.1 result.2).Inputs)
    (form : source.value = .index base brackets key)
    (baseAccepted : inferPlaceFuel fuel context base initial = .ok (baseValue, baseState))
    (accepted : inferPlaceFuel (fuel + 1) context source initial = .ok result)
    (lifetime : GeneralizationLifetime event initial.inference.next baseState [baseValue.type]) :
    GeneralizationLifetime event initial.inference.next result.2 [result.1.type] := by
  cases fitting : Detail.unify baseState.fresh.2.fresh.2 baseValue.type
      (.mapping baseState.fresh.1 baseState.fresh.2.fresh.1) with
  | error error => simp [inferPlaceFuel, form, baseAccepted, fitting, bind, Except.bind] at accepted
  | ok fitted =>
    cases keyAccepted : inferExprFuel fuel context key (some (fitted.resolve baseState.fresh.1)) fitted with
    | error error => simp [inferPlaceFuel, form, baseAccepted, fitting, keyAccepted, bind, Except.bind] at accepted
    | ok keyResult => exact lifetime.place_index_base inputs.ready inputs.wellFormed inputs.catalog form baseAccepted rfl rfl fitting keyAccepted accepted

private theorem matchBody
    {fuel : Nat} {context : SourceInference.Context} {scrutinee expected : Ty} {saved : LexicalScope}
    {arm : Syntax.MatchCase} {rest : List Syntax.MatchCase} {initial patternState : State}
    {pattern : TypedMatchPattern} {body : BlockResult} {result : MatchCasesResult}
    (inputs : (CallIndex.matchCases (fuel + 1) context scrutinee expected saved (arm :: rest) initial result).Inputs)
    (patternAccepted : inferMatchPatternFuel fuel context arm.value.pattern scrutinee initial = .ok (pattern, patternState))
    (bodyAccepted : inferStatementsFuel fuel context arm.value.body.value expected patternState = .ok body)
    (accepted : inferMatchCasesFuel (fuel + 1) context scrutinee expected saved (arm :: rest) initial = .ok result)
    (lifetime : GeneralizationLifetime event patternState.inference.next body.state [body.type]) :
    GeneralizationLifetime event initial.inference.next result.state [] := by
  cases tailAccepted : inferMatchCasesFuel fuel context scrutinee expected saved rest (body.state.restoreLexicalScope saved) with
  | error error => simp [inferMatchCasesFuel, patternAccepted, bodyAccepted, tailAccepted, bind, Except.bind] at accepted
  | ok tail => exact lifetime.matchCases_body inputs.ready inputs.wellFormed inputs.catalog inputs.bounds.1 inputs.bounds.2.1 inputs.bounds.2.2 patternAccepted bodyAccepted tailAccepted accepted

namespace ChildStep

theorem lifetime_place
    {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Expr}
    {initial final : State} {value : PlaceResolution} {child : CallIndex}
    (inputs : (CallIndex.place fuel context source initial value final).Inputs)
    (step : ChildStep (.place fuel context source initial value final) child)
    (lifetime : GeneralizationLifetime event child.initial.inference.next child.final child.outputTypes) :
    GeneralizationLifetime event initial.inference.next final [value.type] := by
  cases step with
  | place_group accepted form childAccepted => exact lifetime.place_group form childAccepted accepted
  | place_index_base accepted form childAccepted => exact placeBase inputs form childAccepted accepted lifetime
  | place_index_key accepted form baseAccepted keyFresh valueFresh fitting childAccepted =>
      exact lifetime.place_index_key inputs.ready inputs.catalog form baseAccepted keyFresh valueFresh fitting childAccepted accepted

theorem lifetime_assignedValue
    {fuel : Nat} {context : SourceInference.Context} {target value : Syntax.Expr} {operator : Syntax.ValueAssignOp}
    {initial final : State} {assignment : AssignmentResolution} {inferred : InferredExpression} {child : CallIndex}
    (inputs : (CallIndex.assignedValue fuel context target operator value initial assignment inferred final).Inputs)
    (step : ChildStep (.assignedValue fuel context target operator value initial assignment inferred final) child)
    (lifetime : GeneralizationLifetime event child.initial.inference.next child.final child.outputTypes) :
    GeneralizationLifetime event initial.inference.next final [assignment.target.type, inferred.type] := by
  cases step with
  | assignedValue_place accepted childAccepted =>
      exact lifetime.assignedValue_place inputs.ready inputs.wellFormed inputs.catalog childAccepted accepted
  | assignedValue_value accepted targetAccepted fitting childAccepted =>
      apply GeneralizationLifetime.assignedValue_value (operator := operator) inputs.ready inputs.catalog targetAccepted ?_ childAccepted accepted lifetime
      cases operator <;> exact fitting

theorem lifetime_matchCases
    {fuel : Nat} {context : SourceInference.Context} {scrutinee expected : Ty} {saved : LexicalScope}
    {sources : List Syntax.MatchCase} {initial : State} {result : MatchCasesResult} {child : CallIndex}
    (inputs : (CallIndex.matchCases fuel context scrutinee expected saved sources initial result).Inputs)
    (step : ChildStep (.matchCases fuel context scrutinee expected saved sources initial result) child)
    (lifetime : GeneralizationLifetime event child.initial.inference.next child.final child.outputTypes) :
    GeneralizationLifetime event initial.inference.next result.state [] := by
  cases step with
  | matchCases_body accepted patternAccepted bodyAccepted =>
      exact matchBody inputs patternAccepted bodyAccepted accepted lifetime
  | matchCases_tail accepted patternAccepted bodyAccepted tailAccepted =>
      exact lifetime.matchCases_tail inputs.ready inputs.catalog inputs.bounds.1 inputs.bounds.2.1 inputs.bounds.2.2 patternAccepted bodyAccepted tailAccepted accepted

end ChildStep
end Solcore.SourceSemantics.SourceInferenceExecution
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceActualMutableProgress
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceExecution
open Frontend SourceInference TypeSystem Detail SourceInferenceSoundness.ProtectedVariables
namespace ActualSuffixProgress

theorem assignedValue_value
      {fuel : Nat} {context : SourceInference.Context} {target value : Syntax.Expr}
      {operator : Syntax.ValueAssignOp} {initial final targetState : State}
      {assignment : AssignmentResolution} {inferred : InferredExpression} {place : PlaceResolution}
      {fitted childFinal : State} {childValue : InferredExpression}
      (accepted : (CallIndex.assignedValue fuel context target operator value initial assignment inferred final).Accepted)
      (targetAccepted : inferPlaceFuel fuel context target initial = .ok (place, targetState))
      (fitting : (match operator with | .equal => pure targetState | _ => unify targetState place.type .word) = (Except.ok fitted : Except Error State))
      (child : (CallIndex.expression fuel context value (some (assignmentExpected operator fitted place.type)) fitted childValue childFinal).Accepted)
    (inputs : (CallIndex.assignedValue fuel context target operator value initial assignment inferred final).Inputs) :
    (CallIndex.expression fuel context value (some (assignmentExpected operator fitted place.type)) fitted childValue childFinal).final.InferenceProgress (CallIndex.assignedValue fuel context target operator value initial assignment inferred final).final := by
  simp only [CallIndex.Accepted] at accepted child
  dsimp only [CallIndex.final] at ⊢
  have childReady := ((ChildStep.assignedValue_value accepted targetAccepted fitting child).inputs inputs).progress child
  obtain ⟨actualPlace, actualState, actualFitted, actualPlaceAccepted, actualFitting, actualValueAccepted, _⟩ := assignedValue_actual_prefix accepted
  cases Except.ok.inj (actualPlaceAccepted.symm.trans targetAccepted)
  have actualFitting : assignmentFit operator targetState place.type = (Except.ok actualFitted : Except Error State) := by cases operator <;> exact actualFitting
  have fitting : assignmentFit operator targetState place.type = (Except.ok fitted : Except Error State) := by cases operator <;> exact fitting
  cases Except.ok.inj (actualFitting.symm.trans fitting)
  cases Except.ok.inj (actualValueAccepted.symm.trans child)
  exact .refl childReady.2.1.solved

theorem assignedValue_place
      {fuel : Nat} {context : SourceInference.Context} {target value : Syntax.Expr}
      {operator : Syntax.ValueAssignOp} {initial final targetState : State}
      {assignment : AssignmentResolution} {inferred : InferredExpression} {place : PlaceResolution}
      (accepted : (CallIndex.assignedValue fuel context target operator value initial assignment inferred final).Accepted)

      (child : (CallIndex.place fuel context target initial place targetState).Accepted)
    (inputs : (CallIndex.assignedValue fuel context target operator value initial assignment inferred final).Inputs) :
    (CallIndex.place fuel context target initial place targetState).final.InferenceProgress (CallIndex.assignedValue fuel context target operator value initial assignment inferred final).final := by
  simp only [CallIndex.Accepted] at accepted child
  dsimp only [CallIndex.final] at ⊢
  obtain ⟨actualPlace, actualState, fitted, actualPlaceAccepted, fitting, valueAccepted, _⟩ := assignedValue_actual_prefix accepted
  cases Except.ok.inj (actualPlaceAccepted.symm.trans child)
  have fitting : assignmentFit operator targetState place.type = (Except.ok fitted : Except Error State) := by cases operator <;> exact fitting
  have placeProperties := inferPlaceFuel_inferenceProperties inputs.ready inputs.catalog.formation inputs.catalog.canonical child
  have fitProperties := assignmentFit_properties placeProperties.2.1 placeProperties.2.2 fitting
  have valueProperties := inferExprFuel_inferenceProperties fitProperties.2.1 inputs.catalog.formation inputs.catalog.canonical
    (by intro type member; cases member; exact fitProperties.2.2) valueAccepted
  exact fitProperties.1.trans valueProperties.1

theorem place_index_base
      {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Expr}
      {initial final : State} {result : PlaceResolution}
      {base key : Syntax.Expr} {brackets : Syntax.SourceSpan} {value : PlaceResolution} {childFinal : State}
      (accepted : (CallIndex.place (fuel + 1) context source initial result final).Accepted)
      (form : source.value = .index base brackets key)
      (child : (CallIndex.place fuel context base initial value childFinal).Accepted)
    (inputs : (CallIndex.place (fuel + 1) context source initial result final).Inputs) :
    (CallIndex.place fuel context base initial value childFinal).final.InferenceProgress (CallIndex.place (fuel + 1) context source initial result final).final := by
  simp only [CallIndex.Accepted] at accepted child
  dsimp only [CallIndex.final] at ⊢
  cases fitting : Detail.unify childFinal.fresh.2.fresh.2 value.type (.mapping childFinal.fresh.1 childFinal.fresh.2.fresh.1) with
  | error error => simp [inferPlaceFuel, form, child, fitting, bind, Except.bind] at accepted
  | ok fitted =>
    cases keyAccepted : inferExprFuel fuel context key (some (fitted.resolve childFinal.fresh.1)) fitted with
    | error error => simp [inferPlaceFuel, form, child, fitting, keyAccepted, bind, Except.bind] at accepted
    | ok keyResult =>
      have baseProperties := inferPlaceFuel_inferenceProperties inputs.ready inputs.catalog.formation inputs.catalog.canonical child
      have keyProperties := fresh_eq_inferenceProperties baseProperties.2.1 rfl
      have valueProperties := fresh_eq_inferenceProperties keyProperties.2.1 rfl
      have baseBelow := baseProperties.2.2.weaken (keyProperties.1.trans valueProperties.1).next_le
      have keyBelow := keyProperties.2.2.weaken valueProperties.1.next_le
      have mappingBelow := (Ty.variablesBelow_mapping_iff _ _ _).2 ⟨keyBelow, valueProperties.2.2⟩
      have mappingProgress := unify_inferenceProgress valueProperties.2.1.solved baseBelow mappingBelow fitting
      have keyStep := ChildStep.place_index_key accepted form child rfl rfl fitting keyAccepted
      have keyProgress := (keyStep.inputs inputs).progress keyAccepted
      exact keyProperties.1.trans (valueProperties.1.trans (mappingProgress.trans
        (keyProgress.1.trans (place_index_key accepted form child rfl rfl fitting keyAccepted inputs))))

theorem constructorApplication_arguments
      {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Expr} {id : ExpressionId}
      {instantiation : DataConstructorInstantiation} {sources : List Syntax.Expr} {expected : Option Ty}
      {initial fitted final childFinal : State} {value : InferredExpression} {values : List InferredExpression}
      (accepted : (CallIndex.constructorApplication fuel context source id instantiation sources expected initial value final).Accepted)
      (arity : sources.length = instantiation.payloadTypes.length)
      (fitting : (match expected with | none => pure initial | some type => unify initial instantiation.resultType type) = (Except.ok fitted : Except Error State))
      (child : (CallIndex.constructorArguments fuel context sources instantiation.payloadTypes fitted values childFinal).Accepted)
    (inputs : (CallIndex.constructorApplication fuel context source id instantiation sources expected initial value final).Inputs) :
    (CallIndex.constructorArguments fuel context sources instantiation.payloadTypes fitted values childFinal).final.InferenceProgress (CallIndex.constructorApplication fuel context source id instantiation sources expected initial value final).final := by
  simp only [CallIndex.Accepted] at accepted child
  dsimp only [CallIndex.final] at ⊢
  have fitting : (match expected with | none => Except.ok initial | some type => Detail.unify initial instantiation.resultType type) = .ok fitted := by cases expected <;> exact fitting
  have fitProperties : initial.InferenceProgress fitted ∧ fitted.InferenceReady := by
    cases expected with
    | none => cases Except.ok.inj fitting; exact ⟨.refl inputs.ready.solved, inputs.ready⟩
    | some type => exact ⟨unify_inferenceProgress inputs.ready.solved inputs.bounds.2.1 (inputs.bounds.2.2 _ (by simp)) fitting,
        unify_preserves_inferenceReady inputs.ready inputs.bounds.2.1 (inputs.bounds.2.2 _ (by simp)) fitting⟩
  have childProperties := inferConstructorArgumentsFuel_inferenceProperties fitProperties.2 inputs.catalog.formation inputs.catalog.canonical
    (fun type member => (inputs.bounds.1 type member).weaken fitProperties.1.next_le) child
  have recorded : recordExpressionWithExpected context source id (childFinal.resolve instantiation.resultType)
      (.constructor instantiation (values.map (·.id))) [] expected childFinal = .ok (value, final) := by
    unfold inferConstructorApplicationFuel at accepted
    cases expected with
    | none => cases Except.ok.inj fitting; simpa [arity, child, bind, Except.bind, pure, Pure.pure, Except.pure] using accepted
    | some type => simpa [arity, fitting, child, bind, Except.bind] using accepted
  exact (recordExpressionWithExpected_inferenceProperties childProperties.2.1
    (childProperties.2.1.solved.variablesBelow_apply (inputs.bounds.2.1.weaken (fitProperties.1.trans childProperties.1).next_le))
    (fun type member => (inputs.bounds.2.2 type member).weaken (fitProperties.1.trans childProperties.1).next_le) recorded).1

theorem matchCases_body
      {fuel : Nat} {context : SourceInference.Context} {scrutineeType expectedReturn : Ty}
      {saved : LexicalScope} {arm : Syntax.MatchCase} {arms : List Syntax.MatchCase}
      {initial patternState : State} {pattern : TypedMatchPattern} {result : MatchCasesResult}
      {body : BlockResult}
      (accepted : (CallIndex.matchCases (fuel + 1) context scrutineeType expectedReturn saved (arm :: arms) initial result).Accepted)
      (patternAccepted : inferMatchPatternFuel fuel context arm.value.pattern scrutineeType initial = .ok (pattern, patternState))
      (child : (CallIndex.statements fuel context arm.value.body.value expectedReturn patternState body).Accepted)
    (inputs : (CallIndex.matchCases (fuel + 1) context scrutineeType expectedReturn saved (arm :: arms) initial result).Inputs) :
    (CallIndex.statements fuel context arm.value.body.value expectedReturn patternState body).final.InferenceProgress (CallIndex.matchCases (fuel + 1) context scrutineeType expectedReturn saved (arm :: arms) initial result).final := by
  simp only [CallIndex.Accepted] at accepted child
  dsimp only [CallIndex.final] at ⊢
  have bodyProperties := ((ChildStep.matchCases_body accepted patternAccepted child).inputs inputs).progress child
  cases tailAccepted : inferMatchCasesFuel fuel context scrutineeType expectedReturn saved arms (body.state.restoreLexicalScope saved) with
  | error error => simp [inferMatchCasesFuel, patternAccepted, child, tailAccepted, bind, Except.bind] at accepted
  | ok tail =>
    have after := ((ChildStep.matchCases_tail accepted patternAccepted child tailAccepted).inputs inputs).progress tailAccepted
    have restored : body.state.InferenceProgress (body.state.restoreLexicalScope saved) := .of_inference_eq bodyProperties.2.1.solved rfl
    exact restored.trans (after.1.trans (matchCases_tail accepted patternAccepted child tailAccepted inputs))

end ActualSuffixProgress
end Solcore.SourceSemantics.SourceInferenceExecution
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceActualNonExpressionProgress
/-! Every non-expression child has its actual suffix substitution continuation. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceExecution

def CallIndex.NonExpression : CallIndex → Prop
  | .expression .. => False
  | _ => True

theorem ChildStep.progress_nonexpression {parent child : CallIndex}
    (inputs : parent.Inputs) (step : ChildStep parent child)
    (nonexpression : parent.NonExpression) :
    child.final.InferenceProgress parent.final := by
  cases step with
  | expression_group accepted form allocation child =>
      exact False.elim nonexpression
  | expression_tuple accepted form allocation child =>
      exact False.elim nonexpression
  | expressions_head accepted head =>
      exact ActualSuffixProgress.expressions_head accepted head inputs
  | expressions_tail accepted head tail =>
      exact ActualSuffixProgress.expressions_tail accepted head tail inputs
  | statements_head accepted child =>
      exact ActualSuffixProgress.statements_head accepted child inputs
  | statements_tail accepted nonempty headAccepted child =>
      exact ActualSuffixProgress.statements_tail accepted nonempty headAccepted child inputs
  | statement_initializer accepted form allocation annotation child =>
      exact ActualSuffixProgress.statement_initializer accepted form allocation annotation child inputs
  | statement_return accepted form allocation child =>
      exact ActualSuffixProgress.statement_return accepted form allocation child inputs
  | statement_expression accepted form allocation child =>
      exact ActualSuffixProgress.statement_expression accepted form allocation child inputs
  | statement_block accepted form allocation child =>
      exact ActualSuffixProgress.statement_block accepted form allocation child inputs
  | statement_if_condition accepted form allocation child =>
      exact ActualSuffixProgress.statement_if_condition accepted form allocation child inputs
  | statement_if_then accepted form allocation conditionAccepted child =>
      exact ActualSuffixProgress.statement_if_then accepted form allocation conditionAccepted child inputs
  | statement_if_else accepted form allocation conditionAccepted hasElse thenAccepted child =>
      exact ActualSuffixProgress.statement_if_else accepted form allocation conditionAccepted hasElse thenAccepted child inputs
  | statement_assignment accepted form allocation child =>
      exact ActualSuffixProgress.statement_assignment accepted form allocation child inputs
  | statement_bitnot accepted form allocation child =>
      exact ActualSuffixProgress.statement_bitnot accepted form allocation child inputs
  | statement_while_condition accepted form allocation child =>
      exact ActualSuffixProgress.statement_while_condition accepted form allocation child inputs
  | statement_while_body accepted form allocation conditionAccepted child =>
      exact ActualSuffixProgress.statement_while_body accepted form allocation conditionAccepted child inputs
  | statement_for_initializer accepted form allocation child =>
      exact ActualSuffixProgress.statement_for_initializer accepted form allocation child inputs
  | statement_for_condition accepted form allocation initializerAccepted child =>
      exact ActualSuffixProgress.statement_for_condition accepted form allocation initializerAccepted child inputs
  | statement_for_body accepted form allocation initializerAccepted conditionAccepted child =>
      exact ActualSuffixProgress.statement_for_body accepted form allocation initializerAccepted conditionAccepted child inputs
  | statement_for_post accepted form allocation initializerAccepted conditionAccepted bodyAccepted child =>
      exact ActualSuffixProgress.statement_for_post accepted form allocation initializerAccepted conditionAccepted bodyAccepted child inputs
  | forItems_head accepted child =>
      exact ActualSuffixProgress.forItems_head accepted child inputs
  | forItems_tail accepted headAccepted child =>
      exact ActualSuffixProgress.forItems_tail accepted headAccepted child inputs
  | forItem_initializer accepted form annotation child =>
      exact ActualSuffixProgress.forItem_initializer accepted form annotation child inputs
  | forItem_expression accepted form child =>
      exact ActualSuffixProgress.forItem_expression accepted form child inputs
  | forItem_assignment accepted form child =>
      exact ActualSuffixProgress.forItem_assignment accepted form child inputs
  | forItem_bitnot accepted form child =>
      exact ActualSuffixProgress.forItem_bitnot accepted form child inputs
  | assignedValue_place accepted child =>
      exact ActualSuffixProgress.assignedValue_place accepted child inputs
  | assignedValue_value accepted targetAccepted fitting child =>
      exact ActualSuffixProgress.assignedValue_value accepted targetAccepted fitting child inputs
  | place_group accepted form child =>
      exact ActualSuffixProgress.place_group accepted form child inputs
  | place_index_base accepted form child =>
      exact ActualSuffixProgress.place_index_base accepted form child inputs
  | place_index_key accepted form baseAccepted keyFresh valueFresh fitting child =>
      exact ActualSuffixProgress.place_index_key accepted form baseAccepted keyFresh valueFresh fitting child inputs
  | constructorApplication_arguments accepted arity fitting child =>
      exact ActualSuffixProgress.constructorApplication_arguments accepted arity fitting child inputs
  | constructorArguments_head accepted child =>
      exact ActualSuffixProgress.constructorArguments_head accepted child inputs
  | constructorArguments_tail accepted headAccepted child =>
      exact ActualSuffixProgress.constructorArguments_tail accepted headAccepted child inputs
  | expression_unary accepted form allocation child =>
      exact False.elim nonexpression
  | expression_binary_left accepted form allocation child =>
      exact False.elim nonexpression
  | expression_binary_right accepted form allocation leftAccepted child =>
      exact False.elim nonexpression
  | expression_conditional_condition accepted form allocation child =>
      exact False.elim nonexpression
  | expression_conditional_then accepted form allocation conditionAccepted child =>
      exact False.elim nonexpression
  | expression_conditional_else accepted form allocation conditionAccepted thenAccepted child =>
      exact False.elim nonexpression
  | expression_lambda_body accepted form allocation parametersAccepted prefixFacts child =>
      exact False.elim nonexpression
  | expression_index_base accepted form allocation child =>
      exact False.elim nonexpression
  | expression_index_key accepted form allocation baseAccepted keyFresh valueFresh fitting child =>
      exact False.elim nonexpression
  | expression_call_constructor accepted form allocation selected fresh child =>
      exact False.elim nonexpression
  | expression_call_arguments accepted form allocation nonconstructor child =>
      exact False.elim nonexpression
  | expression_call_callee accepted form allocation nonconstructor argumentsAccepted indirect child =>
      exact False.elim nonexpression
  | expression_contextual_constructor accepted form allocation selected child =>
      exact False.elim nonexpression
  | expression_field_constructor accepted form allocation selected fresh child =>
      exact False.elim nonexpression
  | matchCases_body accepted patternAccepted child =>
      exact ActualSuffixProgress.matchCases_body accepted patternAccepted child inputs
  | matchCases_tail accepted patternAccepted bodyAccepted child =>
      exact ActualSuffixProgress.matchCases_tail accepted patternAccepted bodyAccepted child inputs
  | statement_match_single accepted form allocation single child =>
      exact ActualSuffixProgress.statement_match_single accepted form allocation single child inputs
  | statement_match_many accepted form allocation multiple child =>
      exact ActualSuffixProgress.statement_match_many accepted form allocation multiple child inputs
  | statement_match_cases accepted form allocation scrutineeAccepted hiddenAllocation child =>
      exact ActualSuffixProgress.statement_match_cases accepted form allocation scrutineeAccepted hiddenAllocation child inputs
  | statement_match_default accepted form allocation scrutineeAccepted hiddenAllocation casesAccepted default child =>
      exact ActualSuffixProgress.statement_match_default accepted form allocation scrutineeAccepted hiddenAllocation casesAccepted default child inputs

end Solcore.SourceSemantics.SourceInferenceExecution
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceActualStatementLifetime
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
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceActualRemainingLifetime
/-! All non-expression edges except enclosing generalization use checker evidence alone.
The two declaration edges additionally consume their actual compiled template scope. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceExecution
open Frontend SourceInference TypeSystem Detail SourceInferenceSoundness.ProtectedVariables
variable {whole : TypedSource} {finalSubstitution : Substitution}
    {binder : TypedBinder} {initializer : ExpressionId}
    {event : RetainedGeneralization whole finalSubstitution binder initializer}

def CallIndex.Initializes : CallIndex → Prop
  | .statement _ _ source _ _ _ => match source.value with
    | .letDecl _ _ (some _) => True
    | _ => False
  | .forItem _ _ source _ _ _ => match source.value with
    | .letDecl _ _ (some _) => True
    | _ => False
  | _ => False

namespace ChildStep

theorem lifetime_statement_noninitializer
    {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Statement} {expected : Ty}
    {initial : State} {result : StatementResult} {child : CallIndex}
    (inputs : (CallIndex.statement fuel context source expected initial result).Inputs)
    (step : ChildStep (.statement fuel context source expected initial result) child)
    (noninitializer : ¬ (CallIndex.statement fuel context source expected initial result).Initializes)
    (lifetime : GeneralizationLifetime event child.initial.inference.next child.final child.outputTypes) :
    GeneralizationLifetime event initial.inference.next result.state [result.type] := by
  cases step
  all_goals first
  | solve | apply False.elim; apply noninitializer; simp_all [CallIndex.Initializes]
  | solve | apply ActualStatementLifetime.statement_return <;> assumption
  | solve | apply ActualStatementLifetime.statement_expression <;> assumption
  | solve | apply ActualStatementLifetime.statement_block <;> assumption
  | solve | apply ActualStatementLifetime.statement_assignment <;> assumption
  | solve | apply ActualStatementLifetime.statement_bitnot <;> assumption
  | solve | apply ActualStatementLifetime.statement_if_condition <;> assumption
  | solve | apply ActualStatementLifetime.statement_if_then <;> assumption
  | solve | apply ActualStatementLifetime.statement_if_else <;> assumption
  | solve | apply ActualStatementLifetime.statement_while_condition <;> assumption
  | solve | apply ActualStatementLifetime.statement_while_body <;> assumption
  | solve | apply ActualStatementLifetime.statement_for_initializer <;> assumption
  | solve | apply ActualStatementLifetime.statement_for_condition <;> assumption
  | solve | apply ActualStatementLifetime.statement_for_body <;> assumption
  | solve | apply ActualStatementLifetime.statement_for_post <;> assumption
  | solve | apply ActualStatementLifetime.statement_match_single <;> assumption
  | solve | apply ActualStatementLifetime.statement_match_many <;> assumption
  | solve | apply ActualStatementLifetime.statement_match_cases <;> assumption
  | solve | apply ActualStatementLifetime.statement_match_default <;> assumption

theorem lifetime_forItem_noninitializer
    {fuel : Nat} {context : SourceInference.Context} {source : Syntax.ForItem}
    {initial final : State} {value : ForItemForm} {child : CallIndex}
    (inputs : (CallIndex.forItem fuel context source initial value final).Inputs)
    (step : ChildStep (.forItem fuel context source initial value final) child)
    (noninitializer : ¬ (CallIndex.forItem fuel context source initial value final).Initializes)
    (lifetime : GeneralizationLifetime event child.initial.inference.next child.final child.outputTypes) :
    GeneralizationLifetime event initial.inference.next final [] := by
  cases step
  all_goals first
  | solve | apply False.elim; apply noninitializer; simp_all [CallIndex.Initializes]
  | solve | apply ActualStatementLifetime.forItem_expression <;> assumption
  | solve | apply ActualStatementLifetime.forItem_assignment <;> assumption
  | solve | apply ActualStatementLifetime.forItem_bitnot <;> assumption

end ChildStep
end Solcore.SourceSemantics.SourceInferenceExecution
end
