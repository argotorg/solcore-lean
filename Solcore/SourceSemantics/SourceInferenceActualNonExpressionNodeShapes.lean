import Solcore.SourceSemantics.SourceInferenceActualNonExpressionProgress
import Solcore.SourceSemantics.SourceInferenceAssignedValueActualPrefix
import Solcore.Frontend.SourceInference.ForStatementInferenceContinuation
import Solcore.SourceSemantics.SourceInferenceActualMatchCompletion
import Solcore.Frontend.SourceInference.NodeShapeProperties
import Solcore.SourceSemantics.SourceInferenceActualCallGraph
import Solcore.SourceSemantics.SourceInferenceActualAssignmentProperties
import Solcore.Frontend.SourceInference.OccurrenceProperties

/-! The actual suffix of a non-expression call preserves node identities and
syntax. Evidence and inferred types may be updated by coercion attachment. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceExecution
open Frontend SourceInference TypeSystem Detail
namespace ActualNodeShapeSuffix

private theorem append (nodes tail : List Node) :
    NodeShapesPreserved nodes (nodes ++ tail) := by
  intro node member
  exact ⟨node, List.mem_append_left tail member, .refl node⟩

private theorem of_nodes_eq {before after : State} (same : after.nodes = before.nodes) :
    NodeShapesPreserved before.nodes after.nodes := by
  rw [same]
  exact .refl _

private theorem unify_shapes {before after : State} {left right : Ty}
    (accepted : Detail.unify before left right = .ok after) :
    NodeShapesPreserved before.nodes after.nodes :=
  of_nodes_eq (unify_occurrenceState_eq accepted).1

private theorem record_shapes
    {context : SourceInference.Context} {source : Syntax.Expr} {id : ExpressionId}
    {type : Ty} {form : ExpressionForm} {requirements : List RequirementId}
    {expected : Option Ty} {state : State} {start : Option Nat}
    {result : InferredExpression × State}
    (accepted : recordExpressionWithExpected context source id type form
      requirements expected state start = .ok result) :
    NodeShapesPreserved state.nodes result.2.nodes := by
  obtain ⟨fitted, fitting, _, recorded⟩ := recordExpressionWithExpected_success_record accepted
  rw [recorded]
  exact (of_nodes_eq (withExpected_occurrenceState_eq fitting).1).trans
    (NodeShapesPreserved.recordNode _ _)

private theorem statement_initializer
      {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Statement}
      {expectedReturn : Ty} {initial allocated : State} {id : StatementId}
      {result : StatementResult}
      {name : Syntax.Identifier} {sourceType : Option Syntax.TypeExpr} {initializer : Syntax.Expr}
      {expected : Option Ty} {value : InferredExpression} {final : State}
      (accepted : (CallIndex.statement (fuel + 1) context source expectedReturn initial result).Accepted)
      (form : source.value = .letDecl name sourceType (some initializer))
      (allocation : initial.allocateStatementId = (id, allocated))
      (annotation : AnnotationExpected context sourceType expected)
      (child : (CallIndex.expression fuel context initializer expected allocated value final).Accepted)  :
    NodeShapesPreserved (CallIndex.expression fuel context initializer expected allocated value final).final.nodes (CallIndex.statement (fuel + 1) context source expectedReturn initial result).final.nodes := by
  simp only [CallIndex.Accepted] at accepted child
  dsimp only [CallIndex.final] at ⊢
  cases annotation
  all_goals unfold inferStatementFuel at accepted
  all_goals simp_all only [bind, Except.bind, pure, Pure.pure, Except.pure]
  all_goals cases Except.ok.inj accepted
  all_goals first | exact .refl _ | exact append _ _


private theorem statement_return
      {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Statement}
      {expectedReturn : Ty} {initial allocated : State} {id : StatementId}
      {result : StatementResult}
      {value : Syntax.Expr} {inferred : InferredExpression} {final : State}
      (accepted : (CallIndex.statement (fuel + 1) context source expectedReturn initial result).Accepted)
      (form : source.value = .returnStmt (some value))
      (allocation : initial.allocateStatementId = (id, allocated))
      (child : (CallIndex.expression fuel context value (some expectedReturn) allocated inferred final).Accepted)  :
    NodeShapesPreserved (CallIndex.expression fuel context value (some expectedReturn) allocated inferred final).final.nodes (CallIndex.statement (fuel + 1) context source expectedReturn initial result).final.nodes := by
  simp only [CallIndex.Accepted] at accepted child
  dsimp only [CallIndex.final] at ⊢
  unfold inferStatementFuel at accepted
  simp only [form, allocation, child, bind, Except.bind, pure, Pure.pure, Except.pure, Except.ok.injEq] at accepted
  cases accepted
  first | exact .refl _ | exact append _ _


private theorem statement_expression
      {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Statement}
      {expectedReturn : Ty} {initial allocated : State} {id : StatementId}
      {result : StatementResult}
      {value : Syntax.Expr} {semicolon : Bool} {inferred : InferredExpression} {final : State}
      (accepted : (CallIndex.statement (fuel + 1) context source expectedReturn initial result).Accepted)
      (form : source.value = .expression value semicolon)
      (allocation : initial.allocateStatementId = (id, allocated))
      (child : (CallIndex.expression fuel context value none allocated inferred final).Accepted)  :
    NodeShapesPreserved (CallIndex.expression fuel context value none allocated inferred final).final.nodes (CallIndex.statement (fuel + 1) context source expectedReturn initial result).final.nodes := by
  simp only [CallIndex.Accepted] at accepted child
  dsimp only [CallIndex.final] at ⊢
  unfold inferStatementFuel at accepted
  simp only [form, allocation, child, bind, Except.bind, pure, Pure.pure, Except.pure, Except.ok.injEq] at accepted
  cases accepted
  first | exact .refl _ | exact append _ _


private theorem statement_block
      {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Statement}
      {expectedReturn : Ty} {initial allocated : State} {id : StatementId}
      {result : StatementResult}
      {body : List Syntax.Statement} {bodyResult : BlockResult}
      (accepted : (CallIndex.statement (fuel + 1) context source expectedReturn initial result).Accepted)
      (form : source.value = .block body)
      (allocation : initial.allocateStatementId = (id, allocated))
      (child : (CallIndex.statements fuel context body expectedReturn allocated bodyResult).Accepted)  :
    NodeShapesPreserved (CallIndex.statements fuel context body expectedReturn allocated bodyResult).final.nodes (CallIndex.statement (fuel + 1) context source expectedReturn initial result).final.nodes := by
  simp only [CallIndex.Accepted] at accepted child
  dsimp only [CallIndex.final] at ⊢
  unfold inferStatementFuel at accepted
  simp only [form, allocation, child, bind, Except.bind, pure, Pure.pure, Except.pure, Except.ok.injEq] at accepted
  cases accepted
  first | exact .refl _ | exact append _ _


private theorem statement_assignment
      {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Statement}
      {expectedReturn : Ty} {initial allocated : State} {id : StatementId}
      {result : StatementResult}
      {target value : Syntax.Expr} {operator : Syntax.Located Syntax.ValueAssignOp}
      {assignment : AssignmentResolution} {inferred : InferredExpression} {final : State}
      (accepted : (CallIndex.statement (fuel + 1) context source expectedReturn initial result).Accepted)
      (form : source.value = .assignValue target operator value)
      (allocation : initial.allocateStatementId = (id, allocated))
      (child : (CallIndex.assignedValue fuel context target operator.value value allocated assignment inferred final).Accepted)  :
    NodeShapesPreserved (CallIndex.assignedValue fuel context target operator.value value allocated assignment inferred final).final.nodes (CallIndex.statement (fuel + 1) context source expectedReturn initial result).final.nodes := by
  simp only [CallIndex.Accepted] at accepted child
  dsimp only [CallIndex.final] at ⊢
  unfold inferStatementFuel at accepted
  simp only [form, allocation, child, bind, Except.bind, pure, Pure.pure, Except.pure, Except.ok.injEq] at accepted
  cases accepted
  first | exact .refl _ | exact append _ _


private theorem statement_while_body
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
      (child : (CallIndex.statements fuel { context with loopDepth := context.loopDepth + 1 } body.value expectedReturn conditionState bodyResult).Accepted)  :
    NodeShapesPreserved (CallIndex.statements fuel { context with loopDepth := context.loopDepth + 1 } body.value expectedReturn conditionState bodyResult).final.nodes (CallIndex.statement (fuel + 1) context source expectedReturn initial result).final.nodes := by
  simp only [CallIndex.Accepted] at accepted child
  dsimp only [CallIndex.final] at ⊢
  unfold inferStatementFuel at accepted
  simp only [form, allocation, conditionAccepted, child, bind, Except.bind, pure, Pure.pure, Except.pure, Except.ok.injEq] at accepted
  cases accepted
  first | exact .refl _ | exact append _ _


private theorem statement_if_else
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
      (child : (CallIndex.statements fuel context body.value expectedReturn (thenResult.state.restoreLexicalScope conditionState.lexicalScope) elseResult).Accepted)  :
    NodeShapesPreserved (CallIndex.statements fuel context body.value expectedReturn (thenResult.state.restoreLexicalScope conditionState.lexicalScope) elseResult).final.nodes (CallIndex.statement (fuel + 1) context source expectedReturn initial result).final.nodes := by
  simp only [CallIndex.Accepted] at accepted child
  dsimp only [CallIndex.final] at ⊢
  subst elseBody
  unfold inferStatementFuel at accepted
  simp only [form, allocation, conditionAccepted, thenAccepted, child, bind, Except.bind, pure, Pure.pure, Except.pure, Except.ok.injEq] at accepted
  cases accepted
  exact append _ _


private theorem forItem_initializer
      {fuel : Nat} {context : SourceInference.Context} {source : Syntax.ForItem}
      {initial final : State} {result : ForItemForm}
      {name : Syntax.Identifier} {sourceType : Option Syntax.TypeExpr} {initializer : Syntax.Expr}
      {expected : Option Ty} {value : InferredExpression} {childFinal : State}
      (accepted : (CallIndex.forItem (fuel + 1) context source initial result final).Accepted)
      (form : source.value = .letDecl name sourceType (some initializer))
      (annotation : AnnotationExpected context sourceType expected)
      (child : (CallIndex.expression fuel context initializer expected initial value childFinal).Accepted)  :
    NodeShapesPreserved (CallIndex.expression fuel context initializer expected initial value childFinal).final.nodes (CallIndex.forItem (fuel + 1) context source initial result final).final.nodes := by
  simp only [CallIndex.Accepted] at accepted child
  dsimp only [CallIndex.final] at ⊢
  cases annotation
  all_goals unfold inferForItemFuel at accepted
  all_goals simp_all only [bind, Except.bind, pure, Pure.pure, Except.pure]
  all_goals cases Except.ok.inj accepted
  all_goals first | exact .refl _ | exact append _ _


private theorem forItem_expression
      {fuel : Nat} {context : SourceInference.Context} {source : Syntax.ForItem}
      {initial final : State} {result : ForItemForm}
      {value : Syntax.Expr} {inferred : InferredExpression} {childFinal : State}
      (accepted : (CallIndex.forItem (fuel + 1) context source initial result final).Accepted)
      (form : source.value = .expression value)
      (child : (CallIndex.expression fuel context value none initial inferred childFinal).Accepted)  :
    NodeShapesPreserved (CallIndex.expression fuel context value none initial inferred childFinal).final.nodes (CallIndex.forItem (fuel + 1) context source initial result final).final.nodes := by
  simp only [CallIndex.Accepted] at accepted child
  dsimp only [CallIndex.final] at ⊢
  unfold inferForItemFuel at accepted
  simp only [form, child, bind, Except.bind, pure, Pure.pure, Except.pure, Except.ok.injEq] at accepted
  cases accepted
  first | exact .refl _ | exact append _ _


private theorem forItem_assignment
      {fuel : Nat} {context : SourceInference.Context} {source : Syntax.ForItem}
      {initial final : State} {result : ForItemForm}
      {target value : Syntax.Expr} {operator : Syntax.Located Syntax.ValueAssignOp}
      {assignment : AssignmentResolution} {inferred : InferredExpression} {childFinal : State}
      (accepted : (CallIndex.forItem (fuel + 1) context source initial result final).Accepted)
      (form : source.value = .assignValue target operator value)
      (child : (CallIndex.assignedValue fuel context target operator.value value initial assignment inferred childFinal).Accepted)  :
    NodeShapesPreserved (CallIndex.assignedValue fuel context target operator.value value initial assignment inferred childFinal).final.nodes (CallIndex.forItem (fuel + 1) context source initial result final).final.nodes := by
  simp only [CallIndex.Accepted] at accepted child
  dsimp only [CallIndex.final] at ⊢
  unfold inferForItemFuel at accepted
  simp only [form, child, bind, Except.bind, pure, Pure.pure, Except.pure, Except.ok.injEq] at accepted
  cases accepted
  first | exact .refl _ | exact append _ _


private theorem place_group
      {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Expr}
      {initial final : State} {result : PlaceResolution}
      {inner : Syntax.Expr} {value : PlaceResolution} {childFinal : State}
      (accepted : (CallIndex.place (fuel + 1) context source initial result final).Accepted)
      (form : source.value = .group inner)
      (child : (CallIndex.place fuel context inner initial value childFinal).Accepted)  :
    NodeShapesPreserved (CallIndex.place fuel context inner initial value childFinal).final.nodes (CallIndex.place (fuel + 1) context source initial result final).final.nodes := by
  simp only [CallIndex.Accepted] at accepted child
  dsimp only [CallIndex.final] at ⊢
  unfold inferPlaceFuel at accepted
  simp only [form, child] at accepted
  cases accepted
  first | exact .refl _ | exact append _ _


private theorem place_index_key
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
      (child : (CallIndex.expression fuel context key (some (fitted.resolve keyType)) fitted keyValue childFinal).Accepted)  :
    NodeShapesPreserved (CallIndex.expression fuel context key (some (fitted.resolve keyType)) fitted keyValue childFinal).final.nodes (CallIndex.place (fuel + 1) context source initial result final).final.nodes := by
  simp only [CallIndex.Accepted] at accepted child
  dsimp only [CallIndex.final] at ⊢
  unfold inferPlaceFuel at accepted
  simp only [form, baseAccepted, keyFresh, valueFresh, fitting, child, bind, Except.bind, pure, Pure.pure, Except.pure, Except.ok.injEq] at accepted
  cases accepted
  first | exact .refl _ | exact append _ _


private theorem constructorArguments_tail
      {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Expr} {sources : List Syntax.Expr}
      {expected : Ty} {expectedTypes : List Ty} {initial middle final : State}
      {values : List InferredExpression} {value : InferredExpression}
      {tailValues : List InferredExpression} {tailFinal : State}
      (accepted : (CallIndex.constructorArguments fuel context (source :: sources) (expected :: expectedTypes) initial values final).Accepted)
      (headAccepted : inferExprFuel fuel context source (some (initial.resolve expected)) initial = .ok (value, middle))
      (child : (CallIndex.constructorArguments fuel context sources expectedTypes middle tailValues tailFinal).Accepted)  :
    NodeShapesPreserved (CallIndex.constructorArguments fuel context sources expectedTypes middle tailValues tailFinal).final.nodes (CallIndex.constructorArguments fuel context (source :: sources) (expected :: expectedTypes) initial values final).final.nodes := by
  simp only [CallIndex.Accepted] at accepted child
  dsimp only [CallIndex.final] at ⊢
  unfold inferConstructorArgumentsFuel at accepted
  simp only [headAccepted, child, bind, Except.bind, pure, Pure.pure, Except.pure, Except.ok.injEq] at accepted
  cases accepted
  first | exact .refl _ | exact append _ _


private theorem expressions_tail
      {fuel : Nat} {context : SourceInference.Context}
      {source : Syntax.Expr} {sources : List Syntax.Expr}
      {initial middle final tailFinal : State} {value : InferredExpression}
      {values tailValues : List InferredExpression}
      (accepted : (CallIndex.expressions (fuel + 1) context (source :: sources)
        initial values final).Accepted)
      (head : inferExprFuel fuel context source none initial = .ok (value, middle))
      (child : inferExprsFuel fuel context sources middle = .ok (tailValues, tailFinal))  :
    NodeShapesPreserved (CallIndex.expressions fuel context sources middle tailValues tailFinal).final.nodes (CallIndex.expressions (fuel + 1) context (source :: sources) initial values final).final.nodes := by
  simp only [CallIndex.Accepted] at accepted child
  dsimp only [CallIndex.final] at ⊢
  unfold inferExprsFuel at accepted
  simp only [head, child, bind, Except.bind, pure, Pure.pure, Except.pure, Except.ok.injEq] at accepted
  cases accepted
  first | exact .refl _ | exact append _ _


private theorem forItems_tail
      {fuel : Nat} {context : SourceInference.Context}
      {source : Syntax.ForItem} {sources : List Syntax.ForItem} {initial middle : State}
      {result tail : InferredForItems} {head : ForItemForm}
      (accepted : (CallIndex.forItems fuel context (source :: sources) initial result).Accepted)
      (headAccepted : inferForItemFuel fuel context source initial = .ok (head, middle))
      (child : (CallIndex.forItems fuel context sources middle tail).Accepted)  :
    NodeShapesPreserved (CallIndex.forItems fuel context sources middle tail).final.nodes (CallIndex.forItems fuel context (source :: sources) initial result).final.nodes := by
  simp only [CallIndex.Accepted] at accepted child
  dsimp only [CallIndex.final] at ⊢
  unfold inferForItemsFuel at accepted
  simp only [headAccepted, child, bind, Except.bind, pure, Pure.pure, Except.pure, Except.ok.injEq] at accepted
  cases accepted
  first | exact .refl _ | exact append _ _


private theorem matchCases_tail
      {fuel : Nat} {context : SourceInference.Context} {scrutineeType expectedReturn : Ty}
      {saved : LexicalScope} {arm : Syntax.MatchCase} {arms : List Syntax.MatchCase}
      {initial patternState : State} {pattern : TypedMatchPattern} {result : MatchCasesResult}
      {body : BlockResult}
      {tail : MatchCasesResult}
      (accepted : (CallIndex.matchCases (fuel + 1) context scrutineeType expectedReturn saved (arm :: arms) initial result).Accepted)
      (patternAccepted : inferMatchPatternFuel fuel context arm.value.pattern scrutineeType initial = .ok (pattern, patternState))
      (bodyAccepted : inferStatementsFuel fuel context arm.value.body.value expectedReturn patternState = .ok body)
      (child : (CallIndex.matchCases fuel context scrutineeType expectedReturn saved arms (body.state.restoreLexicalScope saved) tail).Accepted)  :
    NodeShapesPreserved (CallIndex.matchCases fuel context scrutineeType expectedReturn saved arms (body.state.restoreLexicalScope saved) tail).final.nodes (CallIndex.matchCases (fuel + 1) context scrutineeType expectedReturn saved (arm :: arms) initial result).final.nodes := by
  simp only [CallIndex.Accepted] at accepted child
  dsimp only [CallIndex.final] at ⊢
  unfold inferMatchCasesFuel at accepted
  simp only [patternAccepted, bodyAccepted, child, bind, Except.bind, pure, Pure.pure, Except.pure, Except.ok.injEq] at accepted
  cases accepted
  first | exact .refl _ | exact append _ _



private theorem expressions_head
      {fuel : Nat} {context : SourceInference.Context}
      {source : Syntax.Expr} {sources : List Syntax.Expr}
      {initial middle final : State} {value : InferredExpression}
      {values : List InferredExpression}
      (accepted : (CallIndex.expressions (fuel + 1) context (source :: sources)
        initial values final).Accepted)
      (head : inferExprFuel fuel context source none initial = .ok (value, middle))  :
    NodeShapesPreserved (CallIndex.expression fuel context source none initial value middle).final.nodes (CallIndex.expressions (fuel + 1) context (source :: sources) initial values final).final.nodes := by
  simp only [CallIndex.Accepted] at accepted
  dsimp only [CallIndex.final] at ⊢
  cases tailAccepted : inferExprsFuel fuel context sources middle with
  | error error => simp [inferExprsFuel, head, tailAccepted, bind, Except.bind] at accepted
  | ok tail =>
    exact (inferExprsFuel_occurrenceGraph tailAccepted).graph.shapes.trans
      (expressions_tail accepted head tailAccepted)


private theorem constructorArguments_head
      {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Expr} {sources : List Syntax.Expr}
      {expected : Ty} {expectedTypes : List Ty} {initial middle final : State}
      {values : List InferredExpression} {value : InferredExpression}
      (accepted : (CallIndex.constructorArguments fuel context (source :: sources) (expected :: expectedTypes) initial values final).Accepted)

      (child : (CallIndex.expression fuel context source (some (initial.resolve expected)) initial value middle).Accepted)  :
    NodeShapesPreserved (CallIndex.expression fuel context source (some (initial.resolve expected)) initial value middle).final.nodes (CallIndex.constructorArguments fuel context (source :: sources) (expected :: expectedTypes) initial values final).final.nodes := by
  simp only [CallIndex.Accepted] at accepted child
  dsimp only [CallIndex.final] at ⊢
  cases tailAccepted : inferConstructorArgumentsFuel fuel context sources expectedTypes middle with
  | error error => simp [inferConstructorArgumentsFuel, child, tailAccepted, bind, Except.bind] at accepted
  | ok tail =>
    exact (inferConstructorArgumentsFuel_occurrenceGraph tailAccepted).graph.shapes.trans
      (constructorArguments_tail accepted child tailAccepted)


private theorem forItems_head
      {fuel : Nat} {context : SourceInference.Context}
      {source : Syntax.ForItem} {sources : List Syntax.ForItem} {initial final : State}
      {result : InferredForItems} {value : ForItemForm}
      (accepted : (CallIndex.forItems fuel context (source :: sources) initial result).Accepted)

      (child : (CallIndex.forItem fuel context source initial value final).Accepted)  :
    NodeShapesPreserved (CallIndex.forItem fuel context source initial value final).final.nodes (CallIndex.forItems fuel context (source :: sources) initial result).final.nodes := by
  simp only [CallIndex.Accepted] at accepted child
  dsimp only [CallIndex.final] at ⊢
  cases tailAccepted : inferForItemsFuel fuel context sources final with
  | error error => simp [inferForItemsFuel, child, tailAccepted, bind, Except.bind] at accepted
  | ok tail =>
    exact (inferForItemsFuel_occurrenceGraph tailAccepted).graph.shapes.trans
      (forItems_tail accepted child tailAccepted)


private theorem statements_tail
      {fuel : Nat} {context : SourceInference.Context}
      {source : Syntax.Statement} {sources : List Syntax.Statement} {expectedReturn : Ty}
      {initial : State} {result tail : BlockResult} {head : StatementResult}
      (accepted : (CallIndex.statements (fuel + 1) context (source :: sources) expectedReturn initial result).Accepted)
      (nonempty : sources ≠ [])
      (headAccepted : inferStatementFuel fuel context source expectedReturn initial = .ok head)
      (child : (CallIndex.statements fuel context sources expectedReturn head.state tail).Accepted)  :
    NodeShapesPreserved (CallIndex.statements fuel context sources expectedReturn head.state tail).final.nodes (CallIndex.statements (fuel + 1) context (source :: sources) expectedReturn initial result).final.nodes := by
  simp only [CallIndex.Accepted] at accepted child
  dsimp only [CallIndex.final] at ⊢
  cases sources with
  | nil => exact False.elim (nonempty rfl)
  | cons next rest =>
    simp only [inferStatementsFuel, headAccepted, child, bind, Except.bind, pure, Pure.pure, Except.pure, Except.ok.injEq] at accepted
    cases accepted
    exact .refl _


private theorem statements_head
      {fuel : Nat} {context : SourceInference.Context}
      {source : Syntax.Statement} {sources : List Syntax.Statement} {expectedReturn : Ty}
      {initial : State} {result : BlockResult} {head : StatementResult}
      (accepted : (CallIndex.statements (fuel + 1) context (source :: sources) expectedReturn initial result).Accepted)

      (child : (CallIndex.statement fuel context source expectedReturn initial head).Accepted)  :
    NodeShapesPreserved (CallIndex.statement fuel context source expectedReturn initial head).final.nodes (CallIndex.statements (fuel + 1) context (source :: sources) expectedReturn initial result).final.nodes := by
  simp only [CallIndex.Accepted] at accepted child
  dsimp only [CallIndex.final] at ⊢
  cases sources with
  | nil =>
    simp only [inferStatementsFuel, child, bind, Except.bind, pure, Pure.pure, Except.pure, Except.ok.injEq] at accepted
    cases accepted
    exact .refl _
  | cons next rest =>
    cases tailAccepted : inferStatementsFuel fuel context (next :: rest) expectedReturn head.state with
    | error error => simp [inferStatementsFuel, child, tailAccepted, bind, Except.bind] at accepted
    | ok tail =>
      have nonempty : next :: rest ≠ [] := List.cons_ne_nil _ _
      exact (inferStatementsFuel_occurrenceGraph tailAccepted).graph.shapes.trans
        (statements_tail accepted nonempty child tailAccepted)



private theorem statement_bitnot
      {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Statement}
      {expectedReturn : Ty} {initial allocated : State} {id : StatementId}
      {result : StatementResult}
      {target : Syntax.Expr} {operator : Syntax.SourceSpan}
      {place : PlaceResolution} {final : State}
      (accepted : (CallIndex.statement (fuel + 1) context source expectedReturn initial result).Accepted)
      (form : source.value = .assignBitNot target operator)
      (allocation : initial.allocateStatementId = (id, allocated))
      (child : (CallIndex.place fuel context target allocated place final).Accepted)  :
    NodeShapesPreserved (CallIndex.place fuel context target allocated place final).final.nodes (CallIndex.statement (fuel + 1) context source expectedReturn initial result).final.nodes := by
  simp only [CallIndex.Accepted] at accepted child
  dsimp only [CallIndex.final] at ⊢
  cases fitting : Detail.unify final place.type .word with
  | error error => simp [inferStatementFuel, allocation, form, child, fitting, bind, Except.bind] at accepted
  | ok fitted =>
    unfold inferStatementFuel at accepted
    simp only [allocation, form, child, fitting, bind, Except.bind, pure, Pure.pure, Except.pure, Except.ok.injEq] at accepted
    cases accepted
    exact (unify_shapes fitting).trans (append _ _)


private theorem forItem_bitnot
      {fuel : Nat} {context : SourceInference.Context} {source : Syntax.ForItem}
      {initial final : State} {result : ForItemForm}
      {target : Syntax.Expr} {operator : Syntax.SourceSpan} {place : PlaceResolution} {childFinal : State}
      (accepted : (CallIndex.forItem (fuel + 1) context source initial result final).Accepted)
      (form : source.value = .assignBitNot target operator)
      (child : (CallIndex.place fuel context target initial place childFinal).Accepted)  :
    NodeShapesPreserved (CallIndex.place fuel context target initial place childFinal).final.nodes (CallIndex.forItem (fuel + 1) context source initial result final).final.nodes := by
  simp only [CallIndex.Accepted] at accepted child
  dsimp only [CallIndex.final] at ⊢
  cases fitting : Detail.unify childFinal place.type .word with
  | error error => simp [inferForItemFuel, form, child, fitting, bind, Except.bind] at accepted
  | ok fitted =>
    unfold inferForItemFuel at accepted
    simp only [form, child, fitting, bind, Except.bind, pure, Pure.pure, Except.pure, Except.ok.injEq] at accepted
    cases accepted
    exact unify_shapes fitting


private theorem statement_if_then
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
    NodeShapesPreserved (CallIndex.statements fuel context thenBody.value expectedReturn conditionState thenResult).final.nodes (CallIndex.statement (fuel + 1) context source expectedReturn initial result).final.nodes := by
  simp only [CallIndex.Accepted] at accepted child
  dsimp only [CallIndex.final] at ⊢
  cases elseBody with
  | none =>
    unfold inferStatementFuel at accepted
    simp only [form, allocation, conditionAccepted, child, bind, Except.bind, pure, Pure.pure, Except.pure, Except.ok.injEq] at accepted
    cases accepted
    exact append _ _
  | some elseBody =>
    cases elseAccepted : inferStatementsFuel fuel context elseBody.value expectedReturn (thenResult.state.restoreLexicalScope conditionState.lexicalScope) with
    | error error => simp [inferStatementFuel, allocation, form, conditionAccepted, child, elseAccepted, bind, Except.bind] at accepted
    | ok elseResult =>
      exact (inferStatementsFuel_occurrenceGraph elseAccepted).graph.shapes.trans
        (statement_if_else accepted form allocation conditionAccepted rfl child elseAccepted)


private theorem statement_if_condition
      {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Statement}
      {expectedReturn : Ty} {initial allocated : State} {id : StatementId}
      {result : StatementResult}
      {condition : Syntax.Expr} {thenBody : Syntax.Block} {elseBody : Option Syntax.Block}
      {conditionValue : InferredExpression} {conditionState : State}
      (accepted : (CallIndex.statement (fuel + 1) context source expectedReturn initial result).Accepted)
      (form : source.value = .ifThen condition thenBody elseBody)
      (allocation : initial.allocateStatementId = (id, allocated))
      (child : (CallIndex.expression fuel context condition (some .bool) allocated conditionValue conditionState).Accepted)  :
    NodeShapesPreserved (CallIndex.expression fuel context condition (some .bool) allocated conditionValue conditionState).final.nodes (CallIndex.statement (fuel + 1) context source expectedReturn initial result).final.nodes := by
  simp only [CallIndex.Accepted] at accepted child
  dsimp only [CallIndex.final] at ⊢
  cases thenAccepted : inferStatementsFuel fuel context thenBody.value expectedReturn conditionState with
  | error error => simp [inferStatementFuel, allocation, form, child, thenAccepted, bind, Except.bind] at accepted
  | ok thenResult =>
    exact (inferStatementsFuel_occurrenceGraph thenAccepted).graph.shapes.trans
      (statement_if_then accepted form allocation child thenAccepted)


private theorem statement_while_condition
      {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Statement}
      {expectedReturn : Ty} {initial allocated : State} {id : StatementId}
      {result : StatementResult}
      {condition : Syntax.Expr} {body : Syntax.Block}
      {conditionValue : InferredExpression} {conditionState : State}
      (accepted : (CallIndex.statement (fuel + 1) context source expectedReturn initial result).Accepted)
      (form : source.value = .whileLoop condition body)
      (allocation : initial.allocateStatementId = (id, allocated))
      (child : (CallIndex.expression fuel context condition (some .bool) allocated conditionValue conditionState).Accepted)  :
    NodeShapesPreserved (CallIndex.expression fuel context condition (some .bool) allocated conditionValue conditionState).final.nodes (CallIndex.statement (fuel + 1) context source expectedReturn initial result).final.nodes := by
  simp only [CallIndex.Accepted] at accepted child
  dsimp only [CallIndex.final] at ⊢
  cases bodyAccepted : inferStatementsFuel fuel {context with loopDepth := context.loopDepth + 1} body.value expectedReturn conditionState with
  | error error => simp [inferStatementFuel, allocation, form, child, bodyAccepted, bind, Except.bind] at accepted
  | ok bodyResult =>
    exact (inferStatementsFuel_occurrenceGraph bodyAccepted).graph.shapes.trans
      (statement_while_body accepted form allocation child bodyAccepted)



private theorem forRetention
    {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Statement}
    {initializers post : List Syntax.ForItem} {condition : Syntax.Expr} {body : Syntax.Block}
    {expected : Ty} {initial : State} {result : StatementResult}
    (receipt : SourceInference.ForStatementInferenceContinuation.Receipt fuel context source initializers condition post body expected initial result) :
    NodeShapesPreserved receipt.initialized.state.nodes result.state.nodes ∧
    NodeShapesPreserved receipt.testState.nodes result.state.nodes ∧
    NodeShapesPreserved receipt.bodyResult.state.nodes result.state.nodes ∧
    NodeShapesPreserved receipt.postResult.state.nodes result.state.nodes := by
  have tested := (inferExprFuel_occurrenceGraph receipt.tested).graph.shapes
  have body := (inferStatementsFuel_occurrenceGraph receipt.bodyAccepted).graph.shapes
  have post := (inferForItemsFuel_occurrenceGraph receipt.postAccepted).graph.shapes
  have finished : NodeShapesPreserved receipt.postResult.state.nodes result.state.nodes := by
    have nodesEq := congrArg (fun r : StatementResult => r.state.nodes) receipt.completed
    rw [nodesEq]
    exact append _ _
  have afterBody := post.trans finished
  have afterTest := body.trans afterBody
  exact ⟨tested.trans afterTest, afterTest, afterBody, finished⟩

private theorem statement_for_initializer
      {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Statement}
      {expectedReturn : Ty} {initial allocated : State} {id : StatementId}
      {result : StatementResult}
      {span : Syntax.SourceSpan} {initializer post : List Syntax.ForItem}
      {condition : Syntax.Expr} {body : Syntax.Block} {initialized : InferredForItems}
      (accepted : (CallIndex.statement (fuel + 1) context source expectedReturn initial result).Accepted)
      (form : source.value = .forLoop span initializer condition post body)
      (allocation : initial.allocateStatementId = (id, allocated))
      (child : (CallIndex.forItems fuel context initializer allocated initialized).Accepted)  :
    NodeShapesPreserved (CallIndex.forItems fuel context initializer allocated initialized).final.nodes (CallIndex.statement (fuel + 1) context source expectedReturn initial result).final.nodes := by
  simp only [CallIndex.Accepted] at accepted child
  dsimp only [CallIndex.final] at ⊢
  obtain ⟨receipt⟩ := SourceInference.ForStatementInferenceContinuation.of_accepted form accepted
  have actualInit := receipt.initialization
  rw [allocation] at actualInit
  have sameInit := Except.ok.inj (actualInit.symm.trans child)
  simpa only [sameInit] using (forRetention receipt).1



private theorem statement_for_condition
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
      (child : (CallIndex.expression fuel context condition (some .bool) initialized.state conditionValue conditionState).Accepted)  :
    NodeShapesPreserved (CallIndex.expression fuel context condition (some .bool) initialized.state conditionValue conditionState).final.nodes (CallIndex.statement (fuel + 1) context source expectedReturn initial result).final.nodes := by
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
  simpa only [sameTestState] using (forRetention receipt).2.1



private theorem statement_for_body
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
      (child : (CallIndex.statements fuel { context with loopDepth := context.loopDepth + 1 } body.value expectedReturn conditionState bodyResult).Accepted)  :
    NodeShapesPreserved (CallIndex.statements fuel { context with loopDepth := context.loopDepth + 1 } body.value expectedReturn conditionState bodyResult).final.nodes (CallIndex.statement (fuel + 1) context source expectedReturn initial result).final.nodes := by
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
  simpa only [sameBody] using (forRetention receipt).2.2.1



private theorem statement_for_post
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
      (child : (CallIndex.forItems fuel { context with loopDepth := context.loopDepth + 1 } post (bodyResult.state.restoreLexicalScope initialized.state.lexicalScope) postResult).Accepted)  :
    NodeShapesPreserved (CallIndex.forItems fuel { context with loopDepth := context.loopDepth + 1 } post (bodyResult.state.restoreLexicalScope initialized.state.lexicalScope) postResult).final.nodes (CallIndex.statement (fuel + 1) context source expectedReturn initial result).final.nodes := by
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
  simpa only [samePost] using (forRetention receipt).2.2.2




private theorem assignedValue_value
      {fuel : Nat} {context : SourceInference.Context} {target value : Syntax.Expr}
      {operator : Syntax.ValueAssignOp} {initial final targetState : State}
      {assignment : AssignmentResolution} {inferred : InferredExpression} {place : PlaceResolution}
      {fitted childFinal : State} {childValue : InferredExpression}
      (accepted : (CallIndex.assignedValue fuel context target operator value initial assignment inferred final).Accepted)
      (targetAccepted : inferPlaceFuel fuel context target initial = .ok (place, targetState))
      (fitting : (match operator with | .equal => pure targetState | _ => unify targetState place.type .word) = (Except.ok fitted : Except Error State))
      (child : (CallIndex.expression fuel context value (some (assignmentExpected operator fitted place.type)) fitted childValue childFinal).Accepted)  :
    NodeShapesPreserved (CallIndex.expression fuel context value (some (assignmentExpected operator fitted place.type)) fitted childValue childFinal).final.nodes (CallIndex.assignedValue fuel context target operator value initial assignment inferred final).final.nodes := by
  simp only [CallIndex.Accepted] at accepted child
  dsimp only [CallIndex.final] at ⊢
  obtain ⟨actualPlace, actualState, actualFitted, actualPlaceAccepted, actualFitting, actualValueAccepted, _⟩ := assignedValue_actual_prefix accepted
  cases Except.ok.inj (actualPlaceAccepted.symm.trans targetAccepted)
  have actualFitting : assignmentFit operator targetState place.type = (Except.ok actualFitted : Except Error State) := by cases operator <;> exact actualFitting
  have fitting : assignmentFit operator targetState place.type = (Except.ok fitted : Except Error State) := by cases operator <;> exact fitting
  cases Except.ok.inj (actualFitting.symm.trans fitting)
  cases Except.ok.inj (actualValueAccepted.symm.trans child)
  exact .refl _


private theorem assignedValue_place
      {fuel : Nat} {context : SourceInference.Context} {target value : Syntax.Expr}
      {operator : Syntax.ValueAssignOp} {initial final targetState : State}
      {assignment : AssignmentResolution} {inferred : InferredExpression} {place : PlaceResolution}
      (accepted : (CallIndex.assignedValue fuel context target operator value initial assignment inferred final).Accepted)

      (child : (CallIndex.place fuel context target initial place targetState).Accepted)  :
    NodeShapesPreserved (CallIndex.place fuel context target initial place targetState).final.nodes (CallIndex.assignedValue fuel context target operator value initial assignment inferred final).final.nodes := by
  simp only [CallIndex.Accepted] at accepted child
  dsimp only [CallIndex.final] at ⊢
  obtain ⟨actualPlace, actualState, fitted, actualPlaceAccepted, fitting, valueAccepted, _⟩ := assignedValue_actual_prefix accepted
  cases Except.ok.inj (actualPlaceAccepted.symm.trans child)
  have fitRetained : NodeShapesPreserved targetState.nodes fitted.nodes := by
    cases operator <;> simp only [pure, Pure.pure, Except.pure] at fitting
    all_goals first
    | (cases Except.ok.inj fitting; exact .refl _)
    | exact unify_shapes fitting
  exact fitRetained.trans (inferExprFuel_occurrenceGraph valueAccepted).graph.shapes


private theorem place_index_base
      {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Expr}
      {initial final : State} {result : PlaceResolution}
      {base key : Syntax.Expr} {brackets : Syntax.SourceSpan} {value : PlaceResolution} {childFinal : State}
      (accepted : (CallIndex.place (fuel + 1) context source initial result final).Accepted)
      (form : source.value = .index base brackets key)
      (child : (CallIndex.place fuel context base initial value childFinal).Accepted)  :
    NodeShapesPreserved (CallIndex.place fuel context base initial value childFinal).final.nodes (CallIndex.place (fuel + 1) context source initial result final).final.nodes := by
  simp only [CallIndex.Accepted] at accepted child
  dsimp only [CallIndex.final] at ⊢
  cases fitting : Detail.unify childFinal.fresh.2.fresh.2 value.type (.mapping childFinal.fresh.1 childFinal.fresh.2.fresh.1) with
  | error error => simp [inferPlaceFuel, form, child, fitting, bind, Except.bind] at accepted
  | ok fitted =>
    cases keyAccepted : inferExprFuel fuel context key (some (fitted.resolve childFinal.fresh.1)) fitted with
    | error error => simp [inferPlaceFuel, form, child, fitting, keyAccepted, bind, Except.bind] at accepted
    | ok keyResult =>
      exact (unify_shapes fitting).trans ((inferExprFuel_occurrenceGraph keyAccepted).graph.shapes.trans
        (place_index_key accepted form child rfl rfl fitting keyAccepted))


private theorem constructorApplication_arguments
      {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Expr} {id : ExpressionId}
      {instantiation : DataConstructorInstantiation} {sources : List Syntax.Expr} {expected : Option Ty}
      {initial fitted final childFinal : State} {value : InferredExpression} {values : List InferredExpression}
      (accepted : (CallIndex.constructorApplication fuel context source id instantiation sources expected initial value final).Accepted)
      (arity : sources.length = instantiation.payloadTypes.length)
      (fitting : (match expected with | none => pure initial | some type => unify initial instantiation.resultType type) = (Except.ok fitted : Except Error State))
      (child : (CallIndex.constructorArguments fuel context sources instantiation.payloadTypes fitted values childFinal).Accepted)  :
    NodeShapesPreserved (CallIndex.constructorArguments fuel context sources instantiation.payloadTypes fitted values childFinal).final.nodes (CallIndex.constructorApplication fuel context source id instantiation sources expected initial value final).final.nodes := by
  simp only [CallIndex.Accepted] at accepted child
  dsimp only [CallIndex.final] at ⊢
  have fitting : (match expected with | none => Except.ok initial | some type => Detail.unify initial instantiation.resultType type) = .ok fitted := by cases expected <;> exact fitting
  have recorded : recordExpressionWithExpected context source id (childFinal.resolve instantiation.resultType)
      (.constructor instantiation (values.map (·.id))) [] expected childFinal = .ok (value, final) := by
    unfold inferConstructorApplicationFuel at accepted
    cases expected with
    | none => cases Except.ok.inj fitting; simpa [arity, child, bind, Except.bind, pure, Pure.pure, Except.pure] using accepted
    | some type => simpa [arity, fitting, child, bind, Except.bind] using accepted
  exact record_shapes recorded


private theorem matchCases_body
      {fuel : Nat} {context : SourceInference.Context} {scrutineeType expectedReturn : Ty}
      {saved : LexicalScope} {arm : Syntax.MatchCase} {arms : List Syntax.MatchCase}
      {initial patternState : State} {pattern : TypedMatchPattern} {result : MatchCasesResult}
      {body : BlockResult}
      (accepted : (CallIndex.matchCases (fuel + 1) context scrutineeType expectedReturn saved (arm :: arms) initial result).Accepted)
      (patternAccepted : inferMatchPatternFuel fuel context arm.value.pattern scrutineeType initial = .ok (pattern, patternState))
      (child : (CallIndex.statements fuel context arm.value.body.value expectedReturn patternState body).Accepted)  :
    NodeShapesPreserved (CallIndex.statements fuel context arm.value.body.value expectedReturn patternState body).final.nodes (CallIndex.matchCases (fuel + 1) context scrutineeType expectedReturn saved (arm :: arms) initial result).final.nodes := by
  simp only [CallIndex.Accepted] at accepted child
  dsimp only [CallIndex.final] at ⊢
  cases tailAccepted : inferMatchCasesFuel fuel context scrutineeType expectedReturn saved arms (body.state.restoreLexicalScope saved) with
  | error error => simp [inferMatchCasesFuel, patternAccepted, child, tailAccepted, bind, Except.bind] at accepted
  | ok tail =>
    exact (inferMatchCasesFuel_occurrenceGraph tailAccepted).graph.shapes.trans
      (matchCases_tail accepted patternAccepted child tailAccepted)



private theorem statement_match_default
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
      (child : (CallIndex.statements fuel context body.value expectedReturn checked.state bodyResult).Accepted)  :
    NodeShapesPreserved (CallIndex.statements fuel context body.value expectedReturn checked.state bodyResult).final.nodes (CallIndex.statement (fuel + 1) context source expectedReturn initial result).final.nodes := by
  simp only [CallIndex.Accepted] at accepted child
  dsimp only [CallIndex.final] at ⊢
  have completion := matchCompletion_accepted form allocation scrutineeAccepted hiddenAllocation accepted
  unfold matchCompletion at completion
  simp only [casesAccepted, default, child, bind, Except.bind, pure, Pure.pure, Except.pure] at completion
  split at completion
  · contradiction
  · cases Except.ok.inj completion
    exact append _ _


private theorem statement_match_cases
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
      (child : (CallIndex.matchCases fuel context scrutinee.type expectedReturn hiddenState.lexicalScope arms.value.cases hiddenState checked).Accepted)  :
    NodeShapesPreserved (CallIndex.matchCases fuel context scrutinee.type expectedReturn hiddenState.lexicalScope arms.value.cases hiddenState checked).final.nodes (CallIndex.statement (fuel + 1) context source expectedReturn initial result).final.nodes := by
  simp only [CallIndex.Accepted] at accepted child
  dsimp only [CallIndex.final] at ⊢
  have completion := matchCompletion_accepted form allocation scrutineeAccepted hiddenAllocation accepted
  cases defaultEq : arms.value.defaultBody with
  | none =>
    unfold matchCompletion at completion
    simp only [child, defaultEq, bind, Except.bind, pure, Pure.pure, Except.pure] at completion
    split at completion
    · contradiction
    · cases Except.ok.inj completion
      exact append _ _
  | some body =>
    cases bodyAccepted : inferStatementsFuel fuel context body.value expectedReturn checked.state with
    | error error => simp [matchCompletion, child, defaultEq, bodyAccepted, bind, Except.bind] at completion
    | ok bodyResult =>
      exact (inferStatementsFuel_occurrenceGraph bodyAccepted).graph.shapes.trans
        (statement_match_default accepted form allocation scrutineeAccepted hiddenAllocation child defaultEq bodyAccepted)

private theorem afterScrutinee
    {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Statement}
    {scrutinees : Syntax.NonemptyDelimitedList Syntax.Expr} {arms : Syntax.MatchArms}
    {expectedReturn : Ty} {initial allocated : State} {id : StatementId}
    {scrutinee : InferredExpression} {scrutineeState : State} {result : StatementResult}
    (accepted : inferStatementFuel (fuel+1) context source expectedReturn initial = .ok result)
    (form : source.value = .matchWith scrutinees arms)
    (allocation : initial.allocateStatementId = (id, allocated))
    (scrutineeAccepted : matchScrutinee fuel context source.span scrutinees.elements.toList allocated = .ok (scrutinee, scrutineeState)) :
    NodeShapesPreserved scrutineeState.nodes result.state.nodes := by
  let hidden := scrutineeState.allocateHiddenLocal.1
  let hiddenState := scrutineeState.allocateHiddenLocal.2
  have completion := matchCompletion_accepted form allocation scrutineeAccepted (show scrutineeState.allocateHiddenLocal = (hidden, hiddenState) from rfl) accepted
  cases casesAccepted : inferMatchCasesFuel fuel context scrutinee.type expectedReturn hiddenState.lexicalScope arms.value.cases hiddenState with
  | error error => simp [matchCompletion, casesAccepted, bind, Except.bind] at completion
  | ok checked =>
    exact (inferMatchCasesFuel_occurrenceGraph casesAccepted).graph.shapes.trans
      (statement_match_cases accepted form allocation scrutineeAccepted rfl casesAccepted)

private theorem statement_match_single
      {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Statement}
      {expectedReturn : Ty} {initial allocated : State} {id : StatementId}
      {result : StatementResult} {scrutinees : Syntax.NonemptyDelimitedList Syntax.Expr}
      {arms : Syntax.MatchArms}
      {scrutinee : Syntax.Expr} {value : InferredExpression} {childFinal : State}
      (accepted : (CallIndex.statement (fuel + 1) context source expectedReturn initial result).Accepted)
      (form : source.value = .matchWith scrutinees arms)
      (allocation : initial.allocateStatementId = (id, allocated))
      (single : scrutinees.elements.toList = [scrutinee])
      (child : (CallIndex.expression fuel context scrutinee none allocated value childFinal).Accepted)  :
    NodeShapesPreserved (CallIndex.expression fuel context scrutinee none allocated value childFinal).final.nodes (CallIndex.statement (fuel + 1) context source expectedReturn initial result).final.nodes := by
  simp only [CallIndex.Accepted] at accepted child
  dsimp only [CallIndex.final] at ⊢
  have scrutineeAccepted : matchScrutinee fuel context source.span scrutinees.elements.toList allocated = .ok (value, childFinal) := by simpa only [matchScrutinee, single] using child
  exact afterScrutinee accepted form allocation scrutineeAccepted


private theorem statement_match_many
      {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Statement}
      {expectedReturn : Ty} {initial allocated : State} {id : StatementId}
      {result : StatementResult} {scrutinees : Syntax.NonemptyDelimitedList Syntax.Expr}
      {arms : Syntax.MatchArms}
      {values : List InferredExpression} {childFinal : State}
      (accepted : (CallIndex.statement (fuel + 1) context source expectedReturn initial result).Accepted)
      (form : source.value = .matchWith scrutinees arms)
      (allocation : initial.allocateStatementId = (id, allocated))
      (multiple : ∀ scrutinee, scrutinees.elements.toList ≠ [scrutinee])
      (child : (CallIndex.expressions fuel context scrutinees.elements.toList allocated values childFinal).Accepted)  :
    NodeShapesPreserved (CallIndex.expressions fuel context scrutinees.elements.toList allocated values childFinal).final.nodes (CallIndex.statement (fuel + 1) context source expectedReturn initial result).final.nodes := by
  simp only [CallIndex.Accepted] at accepted child
  dsimp only [CallIndex.final] at ⊢
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
  exact (append _ _).trans (afterScrutinee accepted form allocation scrutineeAccepted)

end ActualNodeShapeSuffix

theorem ChildStep.nonexpression_shapes {parent child : CallIndex}
    (step : ChildStep parent child)
    (nonexpression : parent.NonExpression) :
    Frontend.SourceInference.NodeShapesPreserved child.final.nodes parent.final.nodes := by
  cases step with
  | expression_group accepted form allocation child =>
      exact False.elim nonexpression
  | expression_tuple accepted form allocation child =>
      exact False.elim nonexpression
  | expressions_head accepted head =>
      exact ActualNodeShapeSuffix.expressions_head accepted head
  | expressions_tail accepted head tail =>
      exact ActualNodeShapeSuffix.expressions_tail accepted head tail
  | statements_head accepted child =>
      exact ActualNodeShapeSuffix.statements_head accepted child
  | statements_tail accepted nonempty headAccepted child =>
      exact ActualNodeShapeSuffix.statements_tail accepted nonempty headAccepted child
  | statement_initializer accepted form allocation annotation child =>
      exact ActualNodeShapeSuffix.statement_initializer accepted form allocation annotation child
  | statement_return accepted form allocation child =>
      exact ActualNodeShapeSuffix.statement_return accepted form allocation child
  | statement_expression accepted form allocation child =>
      exact ActualNodeShapeSuffix.statement_expression accepted form allocation child
  | statement_block accepted form allocation child =>
      exact ActualNodeShapeSuffix.statement_block accepted form allocation child
  | statement_if_condition accepted form allocation child =>
      exact ActualNodeShapeSuffix.statement_if_condition accepted form allocation child
  | statement_if_then accepted form allocation conditionAccepted child =>
      exact ActualNodeShapeSuffix.statement_if_then accepted form allocation conditionAccepted child
  | statement_if_else accepted form allocation conditionAccepted hasElse thenAccepted child =>
      exact ActualNodeShapeSuffix.statement_if_else accepted form allocation conditionAccepted hasElse thenAccepted child
  | statement_assignment accepted form allocation child =>
      exact ActualNodeShapeSuffix.statement_assignment accepted form allocation child
  | statement_bitnot accepted form allocation child =>
      exact ActualNodeShapeSuffix.statement_bitnot accepted form allocation child
  | statement_while_condition accepted form allocation child =>
      exact ActualNodeShapeSuffix.statement_while_condition accepted form allocation child
  | statement_while_body accepted form allocation conditionAccepted child =>
      exact ActualNodeShapeSuffix.statement_while_body accepted form allocation conditionAccepted child
  | statement_for_initializer accepted form allocation child =>
      exact ActualNodeShapeSuffix.statement_for_initializer accepted form allocation child
  | statement_for_condition accepted form allocation initializerAccepted child =>
      exact ActualNodeShapeSuffix.statement_for_condition accepted form allocation initializerAccepted child
  | statement_for_body accepted form allocation initializerAccepted conditionAccepted child =>
      exact ActualNodeShapeSuffix.statement_for_body accepted form allocation initializerAccepted conditionAccepted child
  | statement_for_post accepted form allocation initializerAccepted conditionAccepted bodyAccepted child =>
      exact ActualNodeShapeSuffix.statement_for_post accepted form allocation initializerAccepted conditionAccepted bodyAccepted child
  | forItems_head accepted child =>
      exact ActualNodeShapeSuffix.forItems_head accepted child
  | forItems_tail accepted headAccepted child =>
      exact ActualNodeShapeSuffix.forItems_tail accepted headAccepted child
  | forItem_initializer accepted form annotation child =>
      exact ActualNodeShapeSuffix.forItem_initializer accepted form annotation child
  | forItem_expression accepted form child =>
      exact ActualNodeShapeSuffix.forItem_expression accepted form child
  | forItem_assignment accepted form child =>
      exact ActualNodeShapeSuffix.forItem_assignment accepted form child
  | forItem_bitnot accepted form child =>
      exact ActualNodeShapeSuffix.forItem_bitnot accepted form child
  | assignedValue_place accepted child =>
      exact ActualNodeShapeSuffix.assignedValue_place accepted child
  | assignedValue_value accepted targetAccepted fitting child =>
      exact ActualNodeShapeSuffix.assignedValue_value accepted targetAccepted fitting child
  | place_group accepted form child =>
      exact ActualNodeShapeSuffix.place_group accepted form child
  | place_index_base accepted form child =>
      exact ActualNodeShapeSuffix.place_index_base accepted form child
  | place_index_key accepted form baseAccepted keyFresh valueFresh fitting child =>
      exact ActualNodeShapeSuffix.place_index_key accepted form baseAccepted keyFresh valueFresh fitting child
  | constructorApplication_arguments accepted arity fitting child =>
      exact ActualNodeShapeSuffix.constructorApplication_arguments accepted arity fitting child
  | constructorArguments_head accepted child =>
      exact ActualNodeShapeSuffix.constructorArguments_head accepted child
  | constructorArguments_tail accepted headAccepted child =>
      exact ActualNodeShapeSuffix.constructorArguments_tail accepted headAccepted child
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
      exact ActualNodeShapeSuffix.matchCases_body accepted patternAccepted child
  | matchCases_tail accepted patternAccepted bodyAccepted child =>
      exact ActualNodeShapeSuffix.matchCases_tail accepted patternAccepted bodyAccepted child
  | statement_match_single accepted form allocation single child =>
      exact ActualNodeShapeSuffix.statement_match_single accepted form allocation single child
  | statement_match_many accepted form allocation multiple child =>
      exact ActualNodeShapeSuffix.statement_match_many accepted form allocation multiple child
  | statement_match_cases accepted form allocation scrutineeAccepted hiddenAllocation child =>
      exact ActualNodeShapeSuffix.statement_match_cases accepted form allocation scrutineeAccepted hiddenAllocation child
  | statement_match_default accepted form allocation scrutineeAccepted hiddenAllocation casesAccepted default child =>
      exact ActualNodeShapeSuffix.statement_match_default accepted form allocation scrutineeAccepted hiddenAllocation casesAccepted default child

end Solcore.SourceSemantics.SourceInferenceExecution
