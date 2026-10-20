import Solcore.SourceSemantics.SourceInferenceActualCallIndex
import Solcore.Frontend.SourceInference.ExpressionProperties

/-! Immediate calls in successful executions of the actual inference functions.
Each edge records the original syntax branch and all state-producing prefixes.
Every constructor exposes the actual original branch and its ordered prefixes. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceExecution
open Frontend SourceInference TypeSystem Detail

inductive AnnotationExpected (context : SourceInference.Context) :
    Option Syntax.TypeExpr → Option Ty → Prop where
  | absent : AnnotationExpected context none none
  | present {source : Syntax.TypeExpr} {type : Ty}
      (accepted : resolveSourceType context source = .ok type) :
      AnnotationExpected context (some source) (some type)

def assignmentExpected (operator : Syntax.ValueAssignOp) (state : State) (type : Ty) : Ty :=
  match operator with
  | .equal => state.resolve type
  | _ => .word

/-- The actual dispatch tests selecting an indirect callee after its arguments. -/
def IndirectCalleeAt (context : SourceInference.Context) (callee : Syntax.Expr)
    (state : State) : Prop :=
  match calleeQualifiedIdentifier? callee with
  | some (namespacePath, name) =>
      state.lookupBinder? namespacePath.head! ≠ none ∨
        (state.lookupBinder? namespacePath.head! = none ∧
          qualifiedFunctionsNamed context namespacePath name = .ok none)
  | none =>
      match calleeIdentifier? callee with
      | some name => state.lookupBinder? name ≠ none
      | none => True

/-- The original match scrutinee prefix, including the actual synthetic tuple. -/
def matchScrutinee (fuel : Nat) (context : SourceInference.Context)
    (span : Syntax.SourceSpan) (sources : List Syntax.Expr) (state : State) :
    Except Error (InferredExpression × State) :=
  match sources with
  | [source] => inferExprFuel fuel context source none state
  | sources => do
      let (elements, state) ← inferExprsFuel fuel context sources state
      let (tupleId, state) := state.allocateExpressionId
      let type := Ty.productMany (elements.map (·.type))
      let state := state.recordNode (.expression {
        id := tupleId, span, type, form := .tuple (elements.map (·.id)) })
      pure ({ id := tupleId, type }, state)

inductive ChildStep : CallIndex → CallIndex → Prop where
  | expression_group
      {fuel : Nat} {context : SourceInference.Context} {source inner : Syntax.Expr}
      {expected : Option Ty} {initial allocated final childFinal : State}
      {id : ExpressionId} {value childValue : InferredExpression}
      (accepted : (CallIndex.expression (fuel + 1) context source expected
        initial value final).Accepted)
      (form : source.value = .group inner)
      (allocation : initial.allocateExpressionId = (id, allocated))
      (child : inferExprFuel fuel context inner expected allocated =
        .ok (childValue, childFinal)) :
      ChildStep (.expression (fuel + 1) context source expected initial value final)
        (.expression fuel context inner expected allocated childValue childFinal)
  | expression_tuple
      {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Expr}
      {elements : Syntax.DelimitedList Syntax.Expr} {expected : Option Ty}
      {initial allocated final childFinal : State} {id : ExpressionId}
      {value : InferredExpression} {values : List InferredExpression}
      (accepted : (CallIndex.expression (fuel + 1) context source expected
        initial value final).Accepted)
      (form : source.value = .tuple elements)
      (allocation : initial.allocateExpressionId = (id, allocated))
      (child : inferExprsFuel fuel context elements.elements allocated =
        .ok (values, childFinal)) :
      ChildStep (.expression (fuel + 1) context source expected initial value final)
        (.expressions fuel context elements.elements allocated values childFinal)
  | expressions_head
      {fuel : Nat} {context : SourceInference.Context}
      {source : Syntax.Expr} {sources : List Syntax.Expr}
      {initial middle final : State} {value : InferredExpression}
      {values : List InferredExpression}
      (accepted : (CallIndex.expressions (fuel + 1) context (source :: sources)
        initial values final).Accepted)
      (head : inferExprFuel fuel context source none initial = .ok (value, middle)) :
      ChildStep (.expressions (fuel + 1) context (source :: sources) initial values final)
        (.expression fuel context source none initial value middle)
  | expressions_tail
      {fuel : Nat} {context : SourceInference.Context}
      {source : Syntax.Expr} {sources : List Syntax.Expr}
      {initial middle final tailFinal : State} {value : InferredExpression}
      {values tailValues : List InferredExpression}
      (accepted : (CallIndex.expressions (fuel + 1) context (source :: sources)
        initial values final).Accepted)
      (head : inferExprFuel fuel context source none initial = .ok (value, middle))
      (tail : inferExprsFuel fuel context sources middle = .ok (tailValues, tailFinal)) :
      ChildStep (.expressions (fuel + 1) context (source :: sources) initial values final)
        (.expressions fuel context sources middle tailValues tailFinal)

  | statements_head
      {fuel : Nat} {context : SourceInference.Context}
      {source : Syntax.Statement} {sources : List Syntax.Statement} {expectedReturn : Ty}
      {initial : State} {result : BlockResult} {head : StatementResult}
      (accepted : (CallIndex.statements (fuel + 1) context (source :: sources) expectedReturn initial result).Accepted)

      (child : (CallIndex.statement fuel context source expectedReturn initial head).Accepted) :
      ChildStep (CallIndex.statements (fuel + 1) context (source :: sources) expectedReturn initial result) (CallIndex.statement fuel context source expectedReturn initial head)
  | statements_tail
      {fuel : Nat} {context : SourceInference.Context}
      {source : Syntax.Statement} {sources : List Syntax.Statement} {expectedReturn : Ty}
      {initial : State} {result tail : BlockResult} {head : StatementResult}
      (accepted : (CallIndex.statements (fuel + 1) context (source :: sources) expectedReturn initial result).Accepted)
      (nonempty : sources ≠ [])
      (headAccepted : inferStatementFuel fuel context source expectedReturn initial = .ok head)
      (child : (CallIndex.statements fuel context sources expectedReturn head.state tail).Accepted) :
      ChildStep (CallIndex.statements (fuel + 1) context (source :: sources) expectedReturn initial result) (CallIndex.statements fuel context sources expectedReturn head.state tail)
  | statement_initializer
      {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Statement}
      {expectedReturn : Ty} {initial allocated : State} {id : StatementId}
      {result : StatementResult}
      {name : Syntax.Identifier} {sourceType : Option Syntax.TypeExpr} {initializer : Syntax.Expr}
      {expected : Option Ty} {value : InferredExpression} {final : State}
      (accepted : (CallIndex.statement (fuel + 1) context source expectedReturn initial result).Accepted)
      (form : source.value = .letDecl name sourceType (some initializer))
      (allocation : initial.allocateStatementId = (id, allocated))
      (annotation : AnnotationExpected context sourceType expected)
      (child : (CallIndex.expression fuel context initializer expected allocated value final).Accepted) :
      ChildStep (CallIndex.statement (fuel + 1) context source expectedReturn initial result) (CallIndex.expression fuel context initializer expected allocated value final)
  | statement_return
      {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Statement}
      {expectedReturn : Ty} {initial allocated : State} {id : StatementId}
      {result : StatementResult}
      {value : Syntax.Expr} {inferred : InferredExpression} {final : State}
      (accepted : (CallIndex.statement (fuel + 1) context source expectedReturn initial result).Accepted)
      (form : source.value = .returnStmt (some value))
      (allocation : initial.allocateStatementId = (id, allocated))
      (child : (CallIndex.expression fuel context value (some expectedReturn) allocated inferred final).Accepted) :
      ChildStep (CallIndex.statement (fuel + 1) context source expectedReturn initial result) (CallIndex.expression fuel context value (some expectedReturn) allocated inferred final)
  | statement_expression
      {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Statement}
      {expectedReturn : Ty} {initial allocated : State} {id : StatementId}
      {result : StatementResult}
      {value : Syntax.Expr} {semicolon : Bool} {inferred : InferredExpression} {final : State}
      (accepted : (CallIndex.statement (fuel + 1) context source expectedReturn initial result).Accepted)
      (form : source.value = .expression value semicolon)
      (allocation : initial.allocateStatementId = (id, allocated))
      (child : (CallIndex.expression fuel context value none allocated inferred final).Accepted) :
      ChildStep (CallIndex.statement (fuel + 1) context source expectedReturn initial result) (CallIndex.expression fuel context value none allocated inferred final)
  | statement_block
      {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Statement}
      {expectedReturn : Ty} {initial allocated : State} {id : StatementId}
      {result : StatementResult}
      {body : List Syntax.Statement} {bodyResult : BlockResult}
      (accepted : (CallIndex.statement (fuel + 1) context source expectedReturn initial result).Accepted)
      (form : source.value = .block body)
      (allocation : initial.allocateStatementId = (id, allocated))
      (child : (CallIndex.statements fuel context body expectedReturn allocated bodyResult).Accepted) :
      ChildStep (CallIndex.statement (fuel + 1) context source expectedReturn initial result) (CallIndex.statements fuel context body expectedReturn allocated bodyResult)
  | statement_if_condition
      {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Statement}
      {expectedReturn : Ty} {initial allocated : State} {id : StatementId}
      {result : StatementResult}
      {condition : Syntax.Expr} {thenBody : Syntax.Block} {elseBody : Option Syntax.Block}
      {conditionValue : InferredExpression} {conditionState : State}
      (accepted : (CallIndex.statement (fuel + 1) context source expectedReturn initial result).Accepted)
      (form : source.value = .ifThen condition thenBody elseBody)
      (allocation : initial.allocateStatementId = (id, allocated))
      (child : (CallIndex.expression fuel context condition (some .bool) allocated conditionValue conditionState).Accepted) :
      ChildStep (CallIndex.statement (fuel + 1) context source expectedReturn initial result) (CallIndex.expression fuel context condition (some .bool) allocated conditionValue conditionState)
  | statement_if_then
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
      (child : (CallIndex.statements fuel context thenBody.value expectedReturn conditionState thenResult).Accepted) :
      ChildStep (CallIndex.statement (fuel + 1) context source expectedReturn initial result) (CallIndex.statements fuel context thenBody.value expectedReturn conditionState thenResult)
  | statement_if_else
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
      (child : (CallIndex.statements fuel context body.value expectedReturn (thenResult.state.restoreLexicalScope conditionState.lexicalScope) elseResult).Accepted) :
      ChildStep (CallIndex.statement (fuel + 1) context source expectedReturn initial result) (CallIndex.statements fuel context body.value expectedReturn (thenResult.state.restoreLexicalScope conditionState.lexicalScope) elseResult)
  | statement_assignment
      {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Statement}
      {expectedReturn : Ty} {initial allocated : State} {id : StatementId}
      {result : StatementResult}
      {target value : Syntax.Expr} {operator : Syntax.Located Syntax.ValueAssignOp}
      {assignment : AssignmentResolution} {inferred : InferredExpression} {final : State}
      (accepted : (CallIndex.statement (fuel + 1) context source expectedReturn initial result).Accepted)
      (form : source.value = .assignValue target operator value)
      (allocation : initial.allocateStatementId = (id, allocated))
      (child : (CallIndex.assignedValue fuel context target operator.value value allocated assignment inferred final).Accepted) :
      ChildStep (CallIndex.statement (fuel + 1) context source expectedReturn initial result) (CallIndex.assignedValue fuel context target operator.value value allocated assignment inferred final)
  | statement_bitnot
      {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Statement}
      {expectedReturn : Ty} {initial allocated : State} {id : StatementId}
      {result : StatementResult}
      {target : Syntax.Expr} {operator : Syntax.SourceSpan}
      {place : PlaceResolution} {final : State}
      (accepted : (CallIndex.statement (fuel + 1) context source expectedReturn initial result).Accepted)
      (form : source.value = .assignBitNot target operator)
      (allocation : initial.allocateStatementId = (id, allocated))
      (child : (CallIndex.place fuel context target allocated place final).Accepted) :
      ChildStep (CallIndex.statement (fuel + 1) context source expectedReturn initial result) (CallIndex.place fuel context target allocated place final)
  | statement_while_condition
      {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Statement}
      {expectedReturn : Ty} {initial allocated : State} {id : StatementId}
      {result : StatementResult}
      {condition : Syntax.Expr} {body : Syntax.Block}
      {conditionValue : InferredExpression} {conditionState : State}
      (accepted : (CallIndex.statement (fuel + 1) context source expectedReturn initial result).Accepted)
      (form : source.value = .whileLoop condition body)
      (allocation : initial.allocateStatementId = (id, allocated))
      (child : (CallIndex.expression fuel context condition (some .bool) allocated conditionValue conditionState).Accepted) :
      ChildStep (CallIndex.statement (fuel + 1) context source expectedReturn initial result) (CallIndex.expression fuel context condition (some .bool) allocated conditionValue conditionState)
  | statement_while_body
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
      (child : (CallIndex.statements fuel { context with loopDepth := context.loopDepth + 1 } body.value expectedReturn conditionState bodyResult).Accepted) :
      ChildStep (CallIndex.statement (fuel + 1) context source expectedReturn initial result) (CallIndex.statements fuel { context with loopDepth := context.loopDepth + 1 } body.value expectedReturn conditionState bodyResult)
  | statement_for_initializer
      {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Statement}
      {expectedReturn : Ty} {initial allocated : State} {id : StatementId}
      {result : StatementResult}
      {span : Syntax.SourceSpan} {initializer post : List Syntax.ForItem}
      {condition : Syntax.Expr} {body : Syntax.Block} {initialized : InferredForItems}
      (accepted : (CallIndex.statement (fuel + 1) context source expectedReturn initial result).Accepted)
      (form : source.value = .forLoop span initializer condition post body)
      (allocation : initial.allocateStatementId = (id, allocated))
      (child : (CallIndex.forItems fuel context initializer allocated initialized).Accepted) :
      ChildStep (CallIndex.statement (fuel + 1) context source expectedReturn initial result) (CallIndex.forItems fuel context initializer allocated initialized)
  | statement_for_condition
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
      (child : (CallIndex.expression fuel context condition (some .bool) initialized.state conditionValue conditionState).Accepted) :
      ChildStep (CallIndex.statement (fuel + 1) context source expectedReturn initial result) (CallIndex.expression fuel context condition (some .bool) initialized.state conditionValue conditionState)
  | statement_for_body
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
      (child : (CallIndex.statements fuel { context with loopDepth := context.loopDepth + 1 } body.value expectedReturn conditionState bodyResult).Accepted) :
      ChildStep (CallIndex.statement (fuel + 1) context source expectedReturn initial result) (CallIndex.statements fuel { context with loopDepth := context.loopDepth + 1 } body.value expectedReturn conditionState bodyResult)
  | statement_for_post
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
      (child : (CallIndex.forItems fuel { context with loopDepth := context.loopDepth + 1 } post (bodyResult.state.restoreLexicalScope initialized.state.lexicalScope) postResult).Accepted) :
      ChildStep (CallIndex.statement (fuel + 1) context source expectedReturn initial result) (CallIndex.forItems fuel { context with loopDepth := context.loopDepth + 1 } post (bodyResult.state.restoreLexicalScope initialized.state.lexicalScope) postResult)
  | forItems_head
      {fuel : Nat} {context : SourceInference.Context}
      {source : Syntax.ForItem} {sources : List Syntax.ForItem} {initial final : State}
      {result : InferredForItems} {value : ForItemForm}
      (accepted : (CallIndex.forItems fuel context (source :: sources) initial result).Accepted)

      (child : (CallIndex.forItem fuel context source initial value final).Accepted) :
      ChildStep (CallIndex.forItems fuel context (source :: sources) initial result) (CallIndex.forItem fuel context source initial value final)
  | forItems_tail
      {fuel : Nat} {context : SourceInference.Context}
      {source : Syntax.ForItem} {sources : List Syntax.ForItem} {initial middle : State}
      {result tail : InferredForItems} {head : ForItemForm}
      (accepted : (CallIndex.forItems fuel context (source :: sources) initial result).Accepted)
      (headAccepted : inferForItemFuel fuel context source initial = .ok (head, middle))
      (child : (CallIndex.forItems fuel context sources middle tail).Accepted) :
      ChildStep (CallIndex.forItems fuel context (source :: sources) initial result) (CallIndex.forItems fuel context sources middle tail)
  | forItem_initializer
      {fuel : Nat} {context : SourceInference.Context} {source : Syntax.ForItem}
      {initial final : State} {result : ForItemForm}
      {name : Syntax.Identifier} {sourceType : Option Syntax.TypeExpr} {initializer : Syntax.Expr}
      {expected : Option Ty} {value : InferredExpression} {childFinal : State}
      (accepted : (CallIndex.forItem (fuel + 1) context source initial result final).Accepted)
      (form : source.value = .letDecl name sourceType (some initializer))
      (annotation : AnnotationExpected context sourceType expected)
      (child : (CallIndex.expression fuel context initializer expected initial value childFinal).Accepted) :
      ChildStep (CallIndex.forItem (fuel + 1) context source initial result final) (CallIndex.expression fuel context initializer expected initial value childFinal)
  | forItem_expression
      {fuel : Nat} {context : SourceInference.Context} {source : Syntax.ForItem}
      {initial final : State} {result : ForItemForm}
      {value : Syntax.Expr} {inferred : InferredExpression} {childFinal : State}
      (accepted : (CallIndex.forItem (fuel + 1) context source initial result final).Accepted)
      (form : source.value = .expression value)
      (child : (CallIndex.expression fuel context value none initial inferred childFinal).Accepted) :
      ChildStep (CallIndex.forItem (fuel + 1) context source initial result final) (CallIndex.expression fuel context value none initial inferred childFinal)
  | forItem_assignment
      {fuel : Nat} {context : SourceInference.Context} {source : Syntax.ForItem}
      {initial final : State} {result : ForItemForm}
      {target value : Syntax.Expr} {operator : Syntax.Located Syntax.ValueAssignOp}
      {assignment : AssignmentResolution} {inferred : InferredExpression} {childFinal : State}
      (accepted : (CallIndex.forItem (fuel + 1) context source initial result final).Accepted)
      (form : source.value = .assignValue target operator value)
      (child : (CallIndex.assignedValue fuel context target operator.value value initial assignment inferred childFinal).Accepted) :
      ChildStep (CallIndex.forItem (fuel + 1) context source initial result final) (CallIndex.assignedValue fuel context target operator.value value initial assignment inferred childFinal)
  | forItem_bitnot
      {fuel : Nat} {context : SourceInference.Context} {source : Syntax.ForItem}
      {initial final : State} {result : ForItemForm}
      {target : Syntax.Expr} {operator : Syntax.SourceSpan} {place : PlaceResolution} {childFinal : State}
      (accepted : (CallIndex.forItem (fuel + 1) context source initial result final).Accepted)
      (form : source.value = .assignBitNot target operator)
      (child : (CallIndex.place fuel context target initial place childFinal).Accepted) :
      ChildStep (CallIndex.forItem (fuel + 1) context source initial result final) (CallIndex.place fuel context target initial place childFinal)
  | assignedValue_place
      {fuel : Nat} {context : SourceInference.Context} {target value : Syntax.Expr}
      {operator : Syntax.ValueAssignOp} {initial final targetState : State}
      {assignment : AssignmentResolution} {inferred : InferredExpression} {place : PlaceResolution}
      (accepted : (CallIndex.assignedValue fuel context target operator value initial assignment inferred final).Accepted)

      (child : (CallIndex.place fuel context target initial place targetState).Accepted) :
      ChildStep (CallIndex.assignedValue fuel context target operator value initial assignment inferred final) (CallIndex.place fuel context target initial place targetState)
  | assignedValue_value
      {fuel : Nat} {context : SourceInference.Context} {target value : Syntax.Expr}
      {operator : Syntax.ValueAssignOp} {initial final targetState : State}
      {assignment : AssignmentResolution} {inferred : InferredExpression} {place : PlaceResolution}
      {fitted childFinal : State} {childValue : InferredExpression}
      (accepted : (CallIndex.assignedValue fuel context target operator value initial assignment inferred final).Accepted)
      (targetAccepted : inferPlaceFuel fuel context target initial = .ok (place, targetState))
      (fitting : (match operator with | .equal => pure targetState | _ => unify targetState place.type .word) = (Except.ok fitted : Except Error State))
      (child : (CallIndex.expression fuel context value (some (assignmentExpected operator fitted place.type)) fitted childValue childFinal).Accepted) :
      ChildStep (CallIndex.assignedValue fuel context target operator value initial assignment inferred final) (CallIndex.expression fuel context value (some (assignmentExpected operator fitted place.type)) fitted childValue childFinal)
  | place_group
      {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Expr}
      {initial final : State} {result : PlaceResolution}
      {inner : Syntax.Expr} {value : PlaceResolution} {childFinal : State}
      (accepted : (CallIndex.place (fuel + 1) context source initial result final).Accepted)
      (form : source.value = .group inner)
      (child : (CallIndex.place fuel context inner initial value childFinal).Accepted) :
      ChildStep (CallIndex.place (fuel + 1) context source initial result final) (CallIndex.place fuel context inner initial value childFinal)
  | place_index_base
      {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Expr}
      {initial final : State} {result : PlaceResolution}
      {base key : Syntax.Expr} {brackets : Syntax.SourceSpan} {value : PlaceResolution} {childFinal : State}
      (accepted : (CallIndex.place (fuel + 1) context source initial result final).Accepted)
      (form : source.value = .index base brackets key)
      (child : (CallIndex.place fuel context base initial value childFinal).Accepted) :
      ChildStep (CallIndex.place (fuel + 1) context source initial result final) (CallIndex.place fuel context base initial value childFinal)
  | place_index_key
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
      (child : (CallIndex.expression fuel context key (some (fitted.resolve keyType)) fitted keyValue childFinal).Accepted) :
      ChildStep (CallIndex.place (fuel + 1) context source initial result final) (CallIndex.expression fuel context key (some (fitted.resolve keyType)) fitted keyValue childFinal)
  | constructorApplication_arguments
      {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Expr} {id : ExpressionId}
      {instantiation : DataConstructorInstantiation} {sources : List Syntax.Expr} {expected : Option Ty}
      {initial fitted final childFinal : State} {value : InferredExpression} {values : List InferredExpression}
      (accepted : (CallIndex.constructorApplication fuel context source id instantiation sources expected initial value final).Accepted)
      (arity : sources.length = instantiation.payloadTypes.length)
      (fitting : (match expected with | none => pure initial | some type => unify initial instantiation.resultType type) = (Except.ok fitted : Except Error State))
      (child : (CallIndex.constructorArguments fuel context sources instantiation.payloadTypes fitted values childFinal).Accepted) :
      ChildStep (CallIndex.constructorApplication fuel context source id instantiation sources expected initial value final) (CallIndex.constructorArguments fuel context sources instantiation.payloadTypes fitted values childFinal)
  | constructorArguments_head
      {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Expr} {sources : List Syntax.Expr}
      {expected : Ty} {expectedTypes : List Ty} {initial middle final : State}
      {values : List InferredExpression} {value : InferredExpression}
      (accepted : (CallIndex.constructorArguments fuel context (source :: sources) (expected :: expectedTypes) initial values final).Accepted)

      (child : (CallIndex.expression fuel context source (some (initial.resolve expected)) initial value middle).Accepted) :
      ChildStep (CallIndex.constructorArguments fuel context (source :: sources) (expected :: expectedTypes) initial values final) (CallIndex.expression fuel context source (some (initial.resolve expected)) initial value middle)
  | constructorArguments_tail
      {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Expr} {sources : List Syntax.Expr}
      {expected : Ty} {expectedTypes : List Ty} {initial middle final : State}
      {values : List InferredExpression} {value : InferredExpression}
      {tailValues : List InferredExpression} {tailFinal : State}
      (accepted : (CallIndex.constructorArguments fuel context (source :: sources) (expected :: expectedTypes) initial values final).Accepted)
      (headAccepted : inferExprFuel fuel context source (some (initial.resolve expected)) initial = .ok (value, middle))
      (child : (CallIndex.constructorArguments fuel context sources expectedTypes middle tailValues tailFinal).Accepted) :
      ChildStep (CallIndex.constructorArguments fuel context (source :: sources) (expected :: expectedTypes) initial values final) (CallIndex.constructorArguments fuel context sources expectedTypes middle tailValues tailFinal)

  | expression_unary
      {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Expr}
      {expected : Option Ty} {initial allocated final : State} {id : ExpressionId}
      {value : InferredExpression}
      {operator : Syntax.Located Syntax.UnaryOp} {operand : Syntax.Expr}
      {inferred : InferredExpression} {childFinal : State}
      (accepted : (CallIndex.expression (fuel + 1) context source expected initial value final).Accepted)
      (form : source.value = .unary operator operand)
      (allocation : initial.allocateExpressionId = (id, allocated))
      (child : (CallIndex.expression fuel context operand none allocated inferred childFinal).Accepted) :
      ChildStep (CallIndex.expression (fuel + 1) context source expected initial value final) (CallIndex.expression fuel context operand none allocated inferred childFinal)
  | expression_binary_left
      {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Expr}
      {expected : Option Ty} {initial allocated final : State} {id : ExpressionId}
      {value : InferredExpression}
      {operator : Syntax.Located Syntax.BinaryOp} {left right : Syntax.Expr}
      {leftValue : InferredExpression} {leftState : State}
      (accepted : (CallIndex.expression (fuel + 1) context source expected initial value final).Accepted)
      (form : source.value = .binary left operator right)
      (allocation : initial.allocateExpressionId = (id, allocated))
      (child : (CallIndex.expression fuel context left none allocated leftValue leftState).Accepted) :
      ChildStep (CallIndex.expression (fuel + 1) context source expected initial value final) (CallIndex.expression fuel context left none allocated leftValue leftState)
  | expression_binary_right
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
      (child : (CallIndex.expression fuel context right none leftState rightValue rightState).Accepted) :
      ChildStep (CallIndex.expression (fuel + 1) context source expected initial value final) (CallIndex.expression fuel context right none leftState rightValue rightState)
  | expression_conditional_condition
      {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Expr}
      {expected : Option Ty} {initial allocated final : State} {id : ExpressionId}
      {value : InferredExpression}
      {condition thenBranch elseBranch : Syntax.Expr} {question colon : Syntax.SourceSpan}
      {conditionValue : InferredExpression} {conditionState : State}
      (accepted : (CallIndex.expression (fuel + 1) context source expected initial value final).Accepted)
      (form : source.value = .conditional condition question thenBranch colon elseBranch)
      (allocation : initial.allocateExpressionId = (id, allocated))
      (child : (CallIndex.expression fuel context condition (some .bool) allocated conditionValue conditionState).Accepted) :
      ChildStep (CallIndex.expression (fuel + 1) context source expected initial value final) (CallIndex.expression fuel context condition (some .bool) allocated conditionValue conditionState)
  | expression_conditional_then
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
      (child : (CallIndex.expression fuel context thenBranch expected conditionState thenValue thenState).Accepted) :
      ChildStep (CallIndex.expression (fuel + 1) context source expected initial value final) (CallIndex.expression fuel context thenBranch expected conditionState thenValue thenState)
  | expression_conditional_else
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
      (child : (CallIndex.expression fuel context elseBranch expected thenState elseValue elseState).Accepted) :
      ChildStep (CallIndex.expression (fuel + 1) context source expected initial value final) (CallIndex.expression fuel context elseBranch expected thenState elseValue elseState)
  | expression_lambda_body
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
      (child : (CallIndex.statements fuel { context with loopDepth := 0 } body.value resultType bodyState bodyResult).Accepted) :
      ChildStep (CallIndex.expression (fuel + 1) context source expected initial value final) (CallIndex.statements fuel { context with loopDepth := 0 } body.value resultType bodyState bodyResult)
  | expression_index_base
      {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Expr}
      {expected : Option Ty} {initial allocated final : State} {id : ExpressionId}
      {value : InferredExpression}
      {base key : Syntax.Expr} {brackets : Syntax.SourceSpan}
      {inferred : InferredExpression} {childFinal : State}
      (accepted : (CallIndex.expression (fuel + 1) context source expected initial value final).Accepted)
      (form : source.value = .index base brackets key)
      (allocation : initial.allocateExpressionId = (id, allocated))
      (child : (CallIndex.expression fuel context base none allocated inferred childFinal).Accepted) :
      ChildStep (CallIndex.expression (fuel + 1) context source expected initial value final) (CallIndex.expression fuel context base none allocated inferred childFinal)
  | expression_index_key
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
      (child : (CallIndex.expression fuel context key (some (fitted.resolve keyType)) fitted keyValue childFinal).Accepted) :
      ChildStep (CallIndex.expression (fuel + 1) context source expected initial value final) (CallIndex.expression fuel context key (some (fitted.resolve keyType)) fitted keyValue childFinal)
  | expression_call_constructor
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
      (child : (CallIndex.constructorApplication fuel context source id instantiation arguments.elements expected instantiated inferred childFinal).Accepted) :
      ChildStep (CallIndex.expression (fuel + 1) context source expected initial value final) (CallIndex.constructorApplication fuel context source id instantiation arguments.elements expected instantiated inferred childFinal)
  | expression_call_arguments
      {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Expr}
      {expected : Option Ty} {initial allocated final : State} {id : ExpressionId}
      {value : InferredExpression}
      {callee : Syntax.Expr} {arguments : Syntax.DelimitedList Syntax.Expr}
      {values : List InferredExpression} {childFinal : State}
      (accepted : (CallIndex.expression (fuel + 1) context source expected initial value final).Accepted)
      (form : source.value = .call callee arguments)
      (allocation : initial.allocateExpressionId = (id, allocated))
      (nonconstructor : constructorCalleeCandidates context allocated callee = .ok [])
      (child : (CallIndex.expressions fuel context arguments.elements allocated values childFinal).Accepted) :
      ChildStep (CallIndex.expression (fuel + 1) context source expected initial value final) (CallIndex.expressions fuel context arguments.elements allocated values childFinal)
  | expression_call_callee
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
      (child : (CallIndex.expression fuel context callee none argumentState inferred childFinal).Accepted) :
      ChildStep (CallIndex.expression (fuel + 1) context source expected initial value final) (CallIndex.expression fuel context callee none argumentState inferred childFinal)
  | expression_contextual_constructor
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
      (child : (CallIndex.constructorApplication fuel context source id (instantiateDataConstructor dataType constructor typeArguments) (arguments.map (·.elements) |>.getD []) expected allocated inferred childFinal).Accepted) :
      ChildStep (CallIndex.expression (fuel + 1) context source expected initial value final) (CallIndex.constructorApplication fuel context source id (instantiateDataConstructor dataType constructor typeArguments) (arguments.map (·.elements) |>.getD []) expected allocated inferred childFinal)
  | expression_field_constructor
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
      (child : (CallIndex.constructorApplication fuel context source id instantiation [] expected instantiated inferred childFinal).Accepted) :
      ChildStep (CallIndex.expression (fuel + 1) context source expected initial value final) (CallIndex.constructorApplication fuel context source id instantiation [] expected instantiated inferred childFinal)
  | matchCases_body
      {fuel : Nat} {context : SourceInference.Context} {scrutineeType expectedReturn : Ty}
      {saved : LexicalScope} {arm : Syntax.MatchCase} {arms : List Syntax.MatchCase}
      {initial patternState : State} {pattern : TypedMatchPattern} {result : MatchCasesResult}
      {body : BlockResult}
      (accepted : (CallIndex.matchCases (fuel + 1) context scrutineeType expectedReturn saved (arm :: arms) initial result).Accepted)
      (patternAccepted : inferMatchPatternFuel fuel context arm.value.pattern scrutineeType initial = .ok (pattern, patternState))
      (child : (CallIndex.statements fuel context arm.value.body.value expectedReturn patternState body).Accepted) :
      ChildStep (CallIndex.matchCases (fuel + 1) context scrutineeType expectedReturn saved (arm :: arms) initial result) (CallIndex.statements fuel context arm.value.body.value expectedReturn patternState body)
  | matchCases_tail
      {fuel : Nat} {context : SourceInference.Context} {scrutineeType expectedReturn : Ty}
      {saved : LexicalScope} {arm : Syntax.MatchCase} {arms : List Syntax.MatchCase}
      {initial patternState : State} {pattern : TypedMatchPattern} {result : MatchCasesResult}
      {body : BlockResult}
      {tail : MatchCasesResult}
      (accepted : (CallIndex.matchCases (fuel + 1) context scrutineeType expectedReturn saved (arm :: arms) initial result).Accepted)
      (patternAccepted : inferMatchPatternFuel fuel context arm.value.pattern scrutineeType initial = .ok (pattern, patternState))
      (bodyAccepted : inferStatementsFuel fuel context arm.value.body.value expectedReturn patternState = .ok body)
      (child : (CallIndex.matchCases fuel context scrutineeType expectedReturn saved arms (body.state.restoreLexicalScope saved) tail).Accepted) :
      ChildStep (CallIndex.matchCases (fuel + 1) context scrutineeType expectedReturn saved (arm :: arms) initial result) (CallIndex.matchCases fuel context scrutineeType expectedReturn saved arms (body.state.restoreLexicalScope saved) tail)
  | statement_match_single
      {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Statement}
      {expectedReturn : Ty} {initial allocated : State} {id : StatementId}
      {result : StatementResult} {scrutinees : Syntax.NonemptyDelimitedList Syntax.Expr}
      {arms : Syntax.MatchArms}
      {scrutinee : Syntax.Expr} {value : InferredExpression} {childFinal : State}
      (accepted : (CallIndex.statement (fuel + 1) context source expectedReturn initial result).Accepted)
      (form : source.value = .matchWith scrutinees arms)
      (allocation : initial.allocateStatementId = (id, allocated))
      (single : scrutinees.elements.toList = [scrutinee])
      (child : (CallIndex.expression fuel context scrutinee none allocated value childFinal).Accepted) :
      ChildStep (CallIndex.statement (fuel + 1) context source expectedReturn initial result) (CallIndex.expression fuel context scrutinee none allocated value childFinal)
  | statement_match_many
      {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Statement}
      {expectedReturn : Ty} {initial allocated : State} {id : StatementId}
      {result : StatementResult} {scrutinees : Syntax.NonemptyDelimitedList Syntax.Expr}
      {arms : Syntax.MatchArms}
      {values : List InferredExpression} {childFinal : State}
      (accepted : (CallIndex.statement (fuel + 1) context source expectedReturn initial result).Accepted)
      (form : source.value = .matchWith scrutinees arms)
      (allocation : initial.allocateStatementId = (id, allocated))
      (multiple : ∀ scrutinee, scrutinees.elements.toList ≠ [scrutinee])
      (child : (CallIndex.expressions fuel context scrutinees.elements.toList allocated values childFinal).Accepted) :
      ChildStep (CallIndex.statement (fuel + 1) context source expectedReturn initial result) (CallIndex.expressions fuel context scrutinees.elements.toList allocated values childFinal)
  | statement_match_cases
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
      (child : (CallIndex.matchCases fuel context scrutinee.type expectedReturn hiddenState.lexicalScope arms.value.cases hiddenState checked).Accepted) :
      ChildStep (CallIndex.statement (fuel + 1) context source expectedReturn initial result) (CallIndex.matchCases fuel context scrutinee.type expectedReturn hiddenState.lexicalScope arms.value.cases hiddenState checked)
  | statement_match_default
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
      (child : (CallIndex.statements fuel context body.value expectedReturn checked.state bodyResult).Accepted) :
      ChildStep (CallIndex.statement (fuel + 1) context source expectedReturn initial result) (CallIndex.statements fuel context body.value expectedReturn checked.state bodyResult)

theorem ChildStep.parent_accepted {parent child : CallIndex}
    (step : ChildStep parent child) : parent.Accepted := by
  cases step <;> assumption

theorem ChildStep.child_accepted {parent child : CallIndex}
    (step : ChildStep parent child) : child.Accepted := by
  cases step <;> assumption

/-- Reachability from one accepted root through the actual immediate calls. -/
inductive CallOccurrence (root : CallIndex) : CallIndex → Prop where
  | root (accepted : root.Accepted) : CallOccurrence root root
  | child {parent child : CallIndex}
      (parentOccurrence : CallOccurrence root parent)
      (step : ChildStep parent child) : CallOccurrence root child

theorem CallOccurrence.accepted {root call : CallIndex}
    (occurrence : CallOccurrence root call) : call.Accepted := by
  cases occurrence with
  | root accepted => exact accepted
  | child _ step => exact step.child_accepted

theorem CallOccurrence.root_accepted {root call : CallIndex}
    (occurrence : CallOccurrence root call) : root.Accepted := by
  induction occurrence with
  | root accepted => exact accepted
  | child _ _ ih => exact ih

theorem CallOccurrence.trans {root middle final : CallIndex}
    (before : CallOccurrence root middle)
    (after : CallOccurrence middle final) : CallOccurrence root final := by
  induction after with
  | root _ => exact before
  | child _ step ih => exact .child ih step

def ChildClosed (provenance : CallIndex → Prop) : Prop :=
  ∀ {parent child}, provenance parent → ChildStep parent child → provenance child

theorem CallOccurrence.childClosed (root : CallIndex) :
    ChildClosed (CallOccurrence root) :=
  fun _ step => .child ‹_› step

theorem true_childClosed : ChildClosed (fun _ => True) :=
  fun _ _ => True.intro

end Solcore.SourceSemantics.SourceInferenceExecution
