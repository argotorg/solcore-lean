import Solcore.Frontend.SourceInference.Expression
import Solcore.Frontend.SourceInference.Internal.ExpressionProperties
import Solcore.Frontend.SourceInference.Internal.NodeGraph
import Solcore.Frontend.SourceInference.Internal.OccurrenceProperties
import Lean
import Solcore.Frontend.SourceInference.Internal.LocalReadOrigins
import Solcore.Frontend.SourceInference.Internal.LocalReadScopes
import Solcore.Frontend.SourceInference.Internal.LocalGeneralization

/-!
# The call graph of inference

Immediate calls in successful runs of the eleven mutually recursive inference functions, their exact
inputs and outputs, and generalization origins. This file sits below the static context.
-/

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceActualCallIndex
/-! Exact inputs and outputs of the eleven mutually recursive inference calls.
These indices contain execution data, not a source typing or privacy law. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceExecution
open Frontend SourceInference TypeSystem Detail

inductive CallIndex where
  | expression (fuel : Nat) (context : SourceInference.Context) (source : Syntax.Expr)
      (expected : Option Ty) (initial : State) (value : InferredExpression) (final : State)
  | constructorApplication (fuel : Nat) (context : SourceInference.Context) (source : Syntax.Expr)
      (id : ExpressionId) (instantiation : DataConstructorInstantiation) (arguments : List Syntax.Expr)
      (expected : Option Ty) (initial : State) (value : InferredExpression) (final : State)
  | constructorArguments (fuel : Nat) (context : SourceInference.Context) (sources : List Syntax.Expr)
      (expectedTypes : List Ty) (initial : State) (values : List InferredExpression) (final : State)
  | statements (fuel : Nat) (context : SourceInference.Context) (sources : List Syntax.Statement)
      (expectedReturn : Ty) (initial : State) (result : BlockResult)
  | statement (fuel : Nat) (context : SourceInference.Context) (source : Syntax.Statement)
      (expectedReturn : Ty) (initial : State) (result : StatementResult)
  | forItems (fuel : Nat) (context : SourceInference.Context) (sources : List Syntax.ForItem)
      (initial : State) (result : InferredForItems)
  | forItem (fuel : Nat) (context : SourceInference.Context) (source : Syntax.ForItem)
      (initial : State) (value : ForItemForm) (final : State)
  | place (fuel : Nat) (context : SourceInference.Context) (source : Syntax.Expr)
      (initial : State) (value : PlaceResolution) (final : State)
  | assignedValue (fuel : Nat) (context : SourceInference.Context) (target : Syntax.Expr)
      (operator : Syntax.ValueAssignOp) (value : Syntax.Expr) (initial : State)
      (assignment : AssignmentResolution) (inferred : InferredExpression) (final : State)
  | expressions (fuel : Nat) (context : SourceInference.Context) (sources : List Syntax.Expr)
      (initial : State) (values : List InferredExpression) (final : State)
  | matchCases (fuel : Nat) (context : SourceInference.Context) (scrutineeType expectedReturn : Ty)
      (saved : LexicalScope) (cases : List Syntax.MatchCase) (initial : State) (result : MatchCasesResult)

namespace CallIndex

def Accepted : CallIndex → Prop
  | .expression fuel context source expected initial value final =>
      inferExprFuel fuel context source expected initial = .ok (value, final)
  | .constructorApplication fuel context source id instantiation arguments expected initial value final =>
      inferConstructorApplicationFuel fuel context source id instantiation arguments expected initial = .ok (value, final)
  | .constructorArguments fuel context sources expectedTypes initial values final =>
      inferConstructorArgumentsFuel fuel context sources expectedTypes initial = .ok (values, final)
  | .statements fuel context sources expectedReturn initial result =>
      inferStatementsFuel fuel context sources expectedReturn initial = .ok result
  | .statement fuel context source expectedReturn initial result =>
      inferStatementFuel fuel context source expectedReturn initial = .ok result
  | .forItems fuel context sources initial result =>
      inferForItemsFuel fuel context sources initial = .ok result
  | .forItem fuel context source initial value final =>
      inferForItemFuel fuel context source initial = .ok (value, final)
  | .place fuel context source initial value final =>
      inferPlaceFuel fuel context source initial = .ok (value, final)
  | .assignedValue fuel context target operator value initial assignment inferred final =>
      inferAssignedValueFuel fuel context target operator value initial = .ok (assignment, inferred, final)
  | .expressions fuel context sources initial values final =>
      inferExprsFuel fuel context sources initial = .ok (values, final)
  | .matchCases fuel context scrutineeType expectedReturn saved cases initial result =>
      inferMatchCasesFuel fuel context scrutineeType expectedReturn saved cases initial = .ok result

def initial : CallIndex → State
  | .expression _ _ _ _ state _ _
  | .constructorApplication _ _ _ _ _ _ _ state _ _
  | .constructorArguments _ _ _ _ state _ _
  | .statements _ _ _ _ state _
  | .statement _ _ _ _ state _
  | .forItems _ _ _ state _
  | .forItem _ _ _ state _ _
  | .place _ _ _ state _ _
  | .assignedValue _ _ _ _ _ state _ _ _
  | .expressions _ _ _ state _ _
  | .matchCases _ _ _ _ _ _ state _ => state

def final : CallIndex → State
  | .expression _ _ _ _ _ _ state
  | .constructorApplication _ _ _ _ _ _ _ _ _ state
  | .constructorArguments _ _ _ _ _ _ state
  | .forItem _ _ _ _ _ state
  | .place _ _ _ _ _ state
  | .assignedValue _ _ _ _ _ _ _ _ state
  | .expressions _ _ _ _ _ state => state
  | .statements _ _ _ _ _ result => result.state
  | .statement _ _ _ _ _ result => result.state
  | .forItems _ _ _ _ result => result.state
  | .matchCases _ _ _ _ _ _ _ result => result.state

end CallIndex
end Solcore.SourceSemantics.SourceInferenceExecution
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceActualCallGraph
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
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceActualNodeGraphPrefixes
/-! Actual nonrecursive prefixes leave the inference node table closed.
These facts use the saved states from each successful computation. -/
set_option autoImplicit false
set_option Elab.async false

namespace Solcore.SourceSemantics.SourceInferenceExecution.ActualNodeGraph
open Frontend SourceInference TypeSystem Detail

theorem expressionAllocation {initial allocated : State} {id : ExpressionId}
    (allocation : initial.allocateExpressionId = (id, allocated))
    (closed : NodesClosed initial.nodes) : NodesClosed allocated.nodes := by
  have same := congrArg (fun pair => pair.2.nodes) allocation
  exact same ▸ closed

theorem statementAllocation {initial allocated : State} {id : StatementId}
    (allocation : initial.allocateStatementId = (id, allocated))
    (closed : NodesClosed initial.nodes) : NodesClosed allocated.nodes := by
  have same := congrArg (fun pair => pair.2.nodes) allocation
  exact same ▸ closed

theorem freshAllocation {initial allocated : State} {type : Ty}
    (allocation : initial.fresh = (type, allocated))
    (closed : NodesClosed initial.nodes) : NodesClosed allocated.nodes := by
  have same := congrArg (fun pair => pair.2.nodes) allocation
  exact same ▸ closed

theorem hiddenAllocation {initial allocated : State} {id : Resolved.LocalId}
    (allocation : initial.allocateHiddenLocal = (id, allocated))
    (closed : NodesClosed initial.nodes) : NodesClosed allocated.nodes := by
  have same := congrArg (fun pair => pair.2.nodes) allocation
  exact same ▸ closed

theorem constructorAllocation {initial allocated : State}
    {dataType : ProgramDataSignature} {constructor : ProgramDataConstructorSignature}
    {value : DataConstructorInstantiation}
    (allocation : freshDataConstructorInstantiation dataType constructor initial = (value, allocated))
    (closed : NodesClosed initial.nodes) : NodesClosed allocated.nodes := by
  have same := congrArg (fun pair => pair.2.nodes) allocation
  rw [freshDataConstructorInstantiation_nodes] at same
  exact same ▸ closed

theorem unifyRun {initial final : State} {left right : Ty}
    (accepted : unify initial left right = .ok final)
    (closed : NodesClosed initial.nodes) : NodesClosed final.nodes :=
  (unify_occurrenceState_eq accepted).1.symm ▸ closed

theorem optionalFit {initial fitted : State} {expected : Option Ty} {type : Ty}
    (accepted : (match expected with | none => pure initial | some expected => unify initial type expected) =
      (Except.ok fitted : Except Error State))
    (closed : NodesClosed initial.nodes) : NodesClosed fitted.nodes := by
  cases expected with
  | none => cases Except.ok.inj accepted; exact closed
  | some type => exact unifyRun accepted closed

theorem assignedFit {initial fitted : State} {operator : Syntax.ValueAssignOp} {target : Ty}
    (accepted : (match operator with | .equal => pure initial | _ => unify initial target .word) =
      (Except.ok fitted : Except Error State))
    (closed : NodesClosed initial.nodes) : NodesClosed fitted.nodes := by
  cases operator
  · cases Except.ok.inj accepted; exact closed
  all_goals exact unifyRun accepted closed

theorem parameters {context : SourceInference.Context} {sources : List Syntax.LambdaParameter}
    {index : Nat} {seen : List String} {initial : State} {result : List TypedBinder × List Ty × State}
    (accepted : bindLambdaParameters context sources index seen initial = .ok result)
    (closed : NodesClosed initial.nodes) : NodesClosed result.2.2.nodes :=
  (bindLambdaParameters_occurrenceState_eq accepted).1.symm ▸ closed

theorem pattern {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Pattern}
    {expected : Ty} {initial : State} {result : TypedMatchPattern × State}
    (accepted : inferMatchPatternFuel fuel context source expected initial = .ok result)
    (closed : NodesClosed initial.nodes) : NodesClosed result.2.nodes :=
  (inferMatchPatternFuel_occurrenceState_eq accepted).1.symm ▸ closed

theorem lambdaPrefix {context : SourceInference.Context} {expected : Option Ty}
    {annotation : Option Syntax.TypeExpr} {types : List Ty} {initial final : State} {result : Ty}
    (prefixFacts : LambdaPrefixFacts context expected annotation types initial result final)
    (closed : NodesClosed initial.nodes) : NodesClosed final.nodes := by
  cases prefixFacts with
  | noExpectedPartsAnnotated => exact closed
  | noExpectedPartsFresh _ _ allocated => exact freshAllocation allocated closed
  | expectedPartsAnnotated _ unified => exact unifyRun unified closed
  | expectedPartsInferred _ unified => exact unifyRun unified closed

end Solcore.SourceSemantics.SourceInferenceExecution.ActualNodeGraph
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceActualCallGraphClosurePrefixes
/-! Closed node tables follow the exact prefixes of actual recursive calls. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000

namespace Solcore.SourceSemantics.SourceInferenceExecution
open Frontend SourceInference TypeSystem Detail
open ActualNodeGraph

private theorem expressionRun {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Expr}
    {expected : Option Ty} {initial : State} {value : InferredExpression} {final : State}
    (accepted : inferExprFuel fuel context source expected initial = .ok (value, final))
    (closed : NodesClosed initial.nodes) : NodesClosed final.nodes :=
  (inferExprFuel_occurrenceGraph accepted).graph.closed closed

private theorem expressionsRun {fuel : Nat} {context : SourceInference.Context} {sources : List Syntax.Expr}
    {initial : State} {values : List InferredExpression} {final : State}
    (accepted : inferExprsFuel fuel context sources initial = .ok (values, final))
    (closed : NodesClosed initial.nodes) : NodesClosed final.nodes :=
  (inferExprsFuel_occurrenceGraph accepted).graph.closed closed

private theorem placeRun {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Expr}
    {initial : State} {place : PlaceResolution} {final : State}
    (accepted : inferPlaceFuel fuel context source initial = .ok (place, final))
    (closed : NodesClosed initial.nodes) : NodesClosed final.nodes :=
  (inferPlaceFuel_occurrenceGraph accepted).graph.closed closed

private theorem itemsRun {fuel : Nat} {context : SourceInference.Context} {sources : List Syntax.ForItem}
    {initial : State} {result : InferredForItems}
    (accepted : inferForItemsFuel fuel context sources initial = .ok result)
    (closed : NodesClosed initial.nodes) : NodesClosed result.state.nodes :=
  (inferForItemsFuel_occurrenceGraph accepted).graph.closed closed

private theorem itemRun {fuel : Nat} {context : SourceInference.Context} {source : Syntax.ForItem}
    {initial : State} {item : ForItemForm} {final : State}
    (accepted : inferForItemFuel fuel context source initial = .ok (item, final))
    (closed : NodesClosed initial.nodes) : NodesClosed final.nodes :=
  (inferForItemFuel_occurrenceGraph accepted).graph.closed closed

private theorem statementsRun {fuel : Nat} {context : SourceInference.Context} {sources : List Syntax.Statement}
    {expected : Ty} {initial : State} {result : BlockResult}
    (accepted : inferStatementsFuel fuel context sources expected initial = .ok result)
    (closed : NodesClosed initial.nodes) : NodesClosed result.state.nodes :=
  (inferStatementsFuel_occurrenceGraph accepted).graph.closed closed

private theorem statementRun {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Statement}
    {expected : Ty} {initial : State} {result : StatementResult}
    (accepted : inferStatementFuel fuel context source expected initial = .ok result)
    (closed : NodesClosed initial.nodes) : NodesClosed result.state.nodes :=
  (inferStatementFuel_occurrenceGraph accepted).graph.closed closed

private theorem casesRun {fuel : Nat} {context : SourceInference.Context} {arms : List Syntax.MatchCase}
    {expected scrutinee : Ty} {saved : LexicalScope} {initial : State} {result : MatchCasesResult}
    (accepted : inferMatchCasesFuel fuel context scrutinee expected saved arms initial = .ok result)
    (closed : NodesClosed initial.nodes) : NodesClosed result.state.nodes :=
  (inferMatchCasesFuel_occurrenceGraph accepted).graph.closed closed

private theorem scrutineesRun {fuel : Nat} {context : SourceInference.Context}
    {span : Syntax.SourceSpan} {sources : List Syntax.Expr} {initial : State}
    {value : InferredExpression} {final : State}
    (accepted : matchScrutinee fuel context span sources initial = .ok (value, final))
    (closed : NodesClosed initial.nodes) : NodesClosed final.nodes := by
  unfold matchScrutinee at accepted
  split at accepted
  · exact expressionRun accepted closed
  · cases actual : inferExprsFuel fuel context sources initial with
    | error error => simp [actual, bind, Except.bind] at accepted
    | ok inferred =>
        simp only [actual, bind, Except.bind, pure, Pure.pure, Except.pure, Except.ok.injEq] at accepted
        cases accepted
        have graph := inferExprsFuel_occurrenceGraph actual
        apply NodesClosed.record (graph.graph.closed closed)
        simpa only [Node.references, ExpressionForm.references, List.map_map, Function.comp_def,
          State.allocateExpressionId_nodes, ReturnedNodeReferences.references] using graph.returned

/-- Only actual prefix runs are used; readiness or semantic typing is unnecessary. -/
theorem ChildStep.nodesClosed {parent child : CallIndex} (step : ChildStep parent child)
    (closed : NodesClosed parent.initial.nodes) : NodesClosed child.initial.nodes := by
  cases step
  all_goals simp only [CallIndex.initial, State.restoreLexicalScope_nodes] at closed ⊢
  all_goals try solve_by_elim (maxDepth := 12) (transparency := .reducible) [
    expressionAllocation, statementAllocation, freshAllocation, hiddenAllocation,
    constructorAllocation, optionalFit, assignedFit, parameters, pattern, lambdaPrefix,
    expressionRun, expressionsRun, placeRun, itemsRun, itemRun, unifyRun,
    statementsRun, statementRun, casesRun, scrutineesRun]

  case expression_lambda_body _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ allocation parametersAccepted prefixFacts _ =>
    exact lambdaPrefix prefixFacts (parameters parametersAccepted (expressionAllocation allocation closed))
  case matchCases_body _ _ _ _ _ _ _ _ _ _ _ _ _ patternAccepted _ =>
    exact ActualNodeGraph.pattern patternAccepted closed
  case matchCases_tail _ _ _ _ _ _ _ _ _ _ _ _ _ _ patternAccepted bodyAccepted _ =>
    exact statementsRun bodyAccepted (ActualNodeGraph.pattern patternAccepted closed)
  case assignedValue_value fuel context target value operator initial final targetState assignment inferred place
      fitted childFinal childValue accepted targetAccepted fitting child =>
    have targetClosed := placeRun targetAccepted closed
    cases operator <;> dsimp only at fitting
    · cases Except.ok.inj fitting; exact targetClosed
    all_goals exact unifyRun fitting targetClosed
  case constructorApplication_arguments fuel context source id instantiation sources expected initial fitted final childFinal
      value values accepted arity fitting child =>
    cases expected with
    | none => cases Except.ok.inj fitting; exact closed
    | some type => exact unifyRun fitting closed

theorem CallOccurrence.nodesClosed {root call : CallIndex}
    (here : CallOccurrence root call) (closed : NodesClosed root.initial.nodes) :
    NodesClosed call.initial.nodes := by
  induction here with
  | root _ => exact closed
  | child _ step ih => exact step.nodesClosed ih

end Solcore.SourceSemantics.SourceInferenceExecution
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceActualCallPathComparison
/-! Two actual paths have an ancestor relation or diverge at distinct
children of one reached call. This retains paths, not guessed source order. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceExecution

theorem CallOccurrence.uncons {root call : CallIndex}
    (path : CallOccurrence root call) :
    root = call ∨ ∃ child, ChildStep root child ∧ CallOccurrence child call := by
  induction path with
  | root accepted => exact .inl rfl
  | child prior step ih =>
      rcases ih with rfl | ⟨first, firstStep, rest⟩
      · exact .inr ⟨_, step, .root step.child_accepted⟩
      · exact .inr ⟨first, firstStep, .child rest step⟩

theorem CallOccurrence.compare_paths {root left right : CallIndex}
    (leftPath : CallOccurrence root left) (rightPath : CallOccurrence root right) :
    CallOccurrence left right ∨ CallOccurrence right left ∨
      ∃ parent first second,
        CallOccurrence root parent ∧ ChildStep parent first ∧ ChildStep parent second ∧
        first ≠ second ∧ CallOccurrence first left ∧ CallOccurrence second right := by
  induction leftPath generalizing right with
  | root accepted => exact .inl rightPath
  | @child parent left prior step ih =>
      rcases ih rightPath with forward | backward | ⟨split, first, second, reached, a, b, distinct, rest, other⟩
      · rcases forward.uncons with rfl | ⟨first, firstStep, rest⟩
        · exact .inr (.inl (.child (.root step.parent_accepted) step))
        · by_cases same : left = first
          · cases same
            exact .inl rest
          · exact .inr (.inr ⟨parent, left, first, prior, step, firstStep, same,
              .root step.child_accepted, rest⟩)
      · exact .inr (.inl (.child backward step))
      · exact .inr (.inr ⟨split, first, second, reached, a, b, distinct, .child rest step, other⟩)

end Solcore.SourceSemantics.SourceInferenceExecution
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceActualDirectRequirementPrefixes
/-! Direct requirement allocation follows the genuine prefixes of recursive
calls, including completed siblings and the actual saved lexical scopes. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
namespace Solcore.SourceSemantics.SourceInferenceExecution
open Frontend SourceInference TypeSystem Detail
open State (DirectRequirementsProgress)

private theorem allocated_expression {before after : State} {id : ExpressionId}
    (accepted : before.allocateExpressionId = (id, after)) :
    DirectRequirementsProgress before after := by
  have same : after = before.allocateExpressionId.2 := (congrArg Prod.snd accepted).symm
  rw [same]
  exact .refl _
private theorem allocated_statement {before after : State} {id : StatementId}
    (accepted : before.allocateStatementId = (id, after)) :
    DirectRequirementsProgress before after := by
  have same : after = before.allocateStatementId.2 := (congrArg Prod.snd accepted).symm
  rw [same]
  exact .refl _
private theorem allocated_fresh {before after : State} {type : Ty}
    (accepted : before.fresh = (type, after)) :
    DirectRequirementsProgress before after := by
  have same : after = before.fresh.2 := (congrArg Prod.snd accepted).symm
  rw [same]
  exact .refl _
private theorem allocated_hidden {before after : State} {id : Resolved.LocalId}
    (accepted : before.allocateHiddenLocal = (id, after)) :
    DirectRequirementsProgress before after := by
  have same : after = before.allocateHiddenLocal.2 := (congrArg Prod.snd accepted).symm
  rw [same]
  exact .refl _
private theorem allocated_constructor {before after : State}
    {dataType : ProgramDataSignature} {constructor : ProgramDataConstructorSignature}
    {instantiation : DataConstructorInstantiation}
    (accepted : freshDataConstructorInstantiation dataType constructor before = (instantiation, after)) :
    DirectRequirementsProgress before after := by
  simpa only [accepted] using
    freshDataConstructorInstantiation_direct_progress dataType constructor before

private theorem lambda_prefix {context : SourceInference.Context}
    {expected : Option Ty} {annotation : Option Syntax.TypeExpr}
    {parameters : List Ty} {before after : State} {resultType : Ty}
    (prefixFacts : LambdaPrefixFacts context expected annotation parameters before resultType after) :
    DirectRequirementsProgress before after := by
  cases prefixFacts with
  | noExpectedPartsAnnotated => exact .refl _
  | noExpectedPartsFresh _ _ allocated => exact allocated_fresh allocated
  | expectedPartsAnnotated _ unified => exact unify_direct_progress unified
  | expectedPartsInferred _ unified => exact unify_direct_progress unified

private theorem scrutinee_prefix {fuel : Nat} {context : SourceInference.Context}
    {span : Syntax.SourceSpan} {sources : List Syntax.Expr} {before : State}
    {result : InferredExpression × State}
    (accepted : matchScrutinee fuel context span sources before = .ok result) :
    DirectRequirementsProgress before result.2 := by
  unfold matchScrutinee at accepted
  split at accepted
  · exact inferExprFuel_direct_progress accepted
  · cases child : inferExprsFuel fuel context sources before with
    | error error => simp [child, bind, Except.bind] at accepted
    | ok value =>
      have progress := inferExprsFuel_direct_progress child
      simp only [child, bind, Except.bind, pure, Pure.pure, Except.pure, Except.ok.injEq] at accepted
      cases accepted
      exact progress

open Lean Meta Elab Tactic in
elab "collect_direct_prefix" : tactic => withMainContext do
  let hypotheses := (← getLCtx).getFVarIds
  for theoremName in [
      ``allocated_expression, ``allocated_statement, ``allocated_fresh, ``allocated_hidden,
      ``allocated_constructor, ``lambda_prefix, ``scrutinee_prefix,
      ``inferExprFuel_direct_progress, ``inferExprsFuel_direct_progress,
      ``inferStatementsFuel_direct_progress, ``inferStatementFuel_direct_progress,
      ``inferForItemsFuel_direct_progress, ``inferForItemFuel_direct_progress,
      ``inferPlaceFuel_direct_progress, ``inferMatchCasesFuel_direct_progress,
      ``inferMatchPatternFuel_direct_progress, ``bindLambdaParameters_direct_progress,
      ``unify_direct_progress] do
    for hypothesis in hypotheses do
      let saved ← saveState
      try
        let proof ← mkAppM theoremName #[mkFVar hypothesis]
        let proof ← instantiateMVars proof
        if proof.hasExprMVar then throwError "unresolved direct prefix"
        let (_, next) ← (← getMainGoal).note (Name.mkSimple "direct_prefix") proof
        setGoals [next]
      catch _ => saved.restore

theorem ChildStep.direct_prefix {parent child : CallIndex} (step : ChildStep parent child) :
    DirectRequirementsProgress parent.initial child.initial := by
  cases step
  case assignedValue_value accepted targetAccepted fitting child =>
    split at fitting
    all_goals try cases Except.ok.inj fitting
    all_goals collect_direct_prefix
    all_goals simp only [CallIndex.initial]
    all_goals try solve_by_elim (maxDepth := 8) (transparency := .reducible)
      [DirectRequirementsProgress.trans, DirectRequirementsProgress.refl]
  case constructorApplication_arguments accepted arity fitting child =>
    split at fitting
    all_goals try cases Except.ok.inj fitting
    all_goals collect_direct_prefix
    all_goals simp only [CallIndex.initial]
    all_goals try solve_by_elim (maxDepth := 8) (transparency := .reducible)
      [DirectRequirementsProgress.trans, DirectRequirementsProgress.refl]
  all_goals collect_direct_prefix
  all_goals simp only [CallIndex.initial]
  all_goals try solve_by_elim (maxDepth := 8) (transparency := .reducible)
    [DirectRequirementsProgress.trans, DirectRequirementsProgress.refl]
  case statement_if_else =>
    exact (allocated_statement (by assumption)).trans
      ((inferExprFuel_direct_progress (by assumption)).trans
        (inferStatementsFuel_direct_progress (by assumption)))
  case statement_for_post =>
    exact (allocated_statement (by assumption)).trans
      ((inferForItemsFuel_direct_progress (by assumption)).trans
        ((inferExprFuel_direct_progress (by assumption)).trans
          (inferStatementsFuel_direct_progress (by assumption))))
  case expression_index_key =>
    exact (allocated_expression (by assumption)).trans
      ((inferExprFuel_direct_progress (by assumption)).trans
        ((allocated_fresh (by assumption)).trans
          ((allocated_fresh (by assumption)).trans (unify_direct_progress (by assumption)))))
  case matchCases_tail =>
    exact (inferMatchPatternFuel_direct_progress (by assumption)).trans
      (inferStatementsFuel_direct_progress (by assumption))

theorem CallOccurrence.direct_prefix {root call : CallIndex} (here : CallOccurrence root call) :
    DirectRequirementsProgress root.initial call.initial := by
  induction here with
  | root _ => exact .refl _
  | child _ step ih => exact ih.trans step.direct_prefix

end Solcore.SourceSemantics.SourceInferenceExecution
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceActualGeneralizationOrigins
/-! A generalization origin retains the exact executed receipt and its path
from the same accepted body call. No arbitrary accepted initializer is
substituted for an initializer reached by that body. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceExecution.ActualGeneralization
open Frontend SourceInference TypeSystem

inductive Origin (root : CallIndex) : TypedBinder → ExpressionId → Prop where
  | statement {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Statement}
      {expectedReturn : Ty} {initial : State} {result : Detail.StatementResult}
      (receipt : LocalLetRequirementTiming.Receipt fuel context source initial result)
      (here : CallOccurrence root
        (.statement (fuel + 1) context source expectedReturn initial result)) :
      Origin root receipt.binding.1 receipt.value.id
  | header {fuel : Nat} {context : SourceInference.Context} {source : Syntax.ForItem}
      {initial : State} {result : ForItemForm × State}
      (receipt : LocalHeaderRequirementTiming.Receipt fuel context source initial result)
      (here : CallOccurrence root
        (.forItem (fuel + 1) context source initial result.1 result.2)) :
      Origin root receipt.binding.1 receipt.value.id

/-- An origin in an actual child remains an origin in every enclosing call
on the same inference path. -/
theorem Origin.rebase {root child : CallIndex}
    {binder : TypedBinder} {initializer : ExpressionId}
    (here : CallOccurrence root child)
    (origin : Origin child binder initializer) :
    Origin root binder initializer := by
  cases origin with
  | statement receipt reached => exact .statement receipt (here.trans reached)
  | header receipt reached => exact .header receipt (here.trans reached)

end Solcore.SourceSemantics.SourceInferenceExecution.ActualGeneralization
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceActualGeneralizationInventory
/-! Exact-call generalization origins are collected in node-table order and
in header results before the enclosing for statement records them. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceExecution.ActualGeneralization
open Frontend SourceInference TypeSystem Detail
variable {root : CallIndex}

def Item (root : CallIndex) (item : ForItemForm) : Prop :=
  ∀ binder initializer, item = .letDecl binder (some initializer) → Origin root binder initializer

def Items (root : CallIndex) (items : List ForItemForm) : Prop := ∀ item ∈ items, Item root item

def Statement (root : CallIndex) (node : StatementNode) : Prop :=
  match node.form with
  | .letDecl binder (some initializer) => Origin root binder initializer
  | .forLoop initial _ post _ => Items root initial ∧ Items root post
  | _ => True

def Origins (root : CallIndex) (nodes : List Node) : Prop :=
  ∀ node, .statement node ∈ nodes → Statement root node

theorem Origins.empty : Origins root [] := by intro _ impossible; cases impossible

theorem Origins.expression {nodes : List Node} (origins : Origins root nodes) (node : ExpressionNode) :
    Origins root (nodes ++ [.expression node]) := by
  intro statement present
  rcases List.mem_append.mp present with previous | fresh
  · exact origins statement previous
  · cases List.mem_singleton.mp fresh

theorem Origins.statement {nodes : List Node} (origins : Origins root nodes)
    (node : StatementNode) (event : Statement root node) : Origins root (nodes ++ [.statement node]) := by
  intro statement present
  rcases List.mem_append.mp present with previous | fresh
  · exact origins statement previous
  · cases List.mem_singleton.mp fresh
    exact event

theorem Origins.mapExpressions {nodes : List Node} (origins : Origins root nodes)
    (modify : ExpressionNode → ExpressionNode) :
    Origins root (nodes.map (fun node => match node with
      | .expression expression => .expression (modify expression)
      | .statement statement => .statement statement)) := by
  intro statement present
  obtain ⟨node, member, selected⟩ := List.mem_map.mp present
  cases node with
  | expression expression => cases selected
  | statement original =>
    cases selected
    exact origins _ member

theorem Statement.same_form {before after : StatementNode} (origin : Statement root before)
    (same : after.form = before.form) : Statement root after := by
  unfold Statement
  rw [same]
  exact origin

theorem Origins.mapStatements {nodes : List Node} (origins : Origins root nodes)
    (modify : StatementNode → StatementNode) (forms : ∀ node, (modify node).form = node.form) :
    Origins root (nodes.map (fun node => match node with
      | .expression expression => .expression expression
      | .statement statement => .statement (modify statement))) := by
  intro statement present
  obtain ⟨node, member, selected⟩ := List.mem_map.mp present
  cases node with
  | expression expression => cases selected
  | statement original =>
    cases selected
    exact (origins original member).same_form (forms original)

theorem Item.of_header {fuel context source initial result}
    (receipt : LocalHeaderRequirementTiming.Receipt fuel context source initial result)
    (here : CallOccurrence root (.forItem (fuel + 1) context source initial result.1 result.2)) : Item root result.1 := by
  intro binder initializer same
  rw [receipt.recorded] at same
  cases same
  exact .header receipt here

theorem Statement.of_let {fuel context source initial result}
    (receipt : LocalLetRequirementTiming.Receipt fuel context source initial result)
    {expectedReturn : Ty}
    (here : CallOccurrence root (.statement (fuel + 1) context source expectedReturn initial result))
    {node : StatementNode}
    (form : node.form = .letDecl receipt.binding.1 (some receipt.value.id)) : Statement root node := by
  unfold Statement
  rw [form]
  exact .statement receipt here

end Solcore.SourceSemantics.SourceInferenceExecution.ActualGeneralization
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceActualIndirectCallPrefix
/-! An accepted indirect dispatch identifies its actual application suffix. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceExecution
open Frontend SourceInference TypeSystem Detail

theorem indirectCall_actual_suffix
    {fuel : Nat} {context : SourceInference.Context} {source callee : Syntax.Expr}
    {arguments : Syntax.DelimitedList Syntax.Expr} {id : ExpressionId} {expected : Option Ty}
    {initial allocated argumentState calleeState : State}
    {inferredArguments : List InferredExpression} {inferredCallee : InferredExpression}
    {result : InferredExpression × State}
    (form : source.value = .call callee arguments)
    (allocation : initial.allocateExpressionId = (id, allocated))
    (nonconstructor : constructorCalleeCandidates context allocated callee = .ok [])
    (argumentsAccepted : inferExprsFuel fuel context arguments.elements allocated = .ok (inferredArguments, argumentState))
    (indirect : IndirectCalleeAt context callee argumentState)
    (calleeAccepted : inferExprFuel fuel context callee none argumentState = .ok (inferredCallee, calleeState))
    (accepted : inferExprFuel (fuel + 1) context source expected initial = .ok result) :
    ∃ application,
      applyFunctionType context id inferredCallee.type inferredArguments expected calleeState = .ok application ∧
      recordIndirectCall source inferredCallee inferredArguments application = result := by
  unfold inferExprFuel at accepted
  simp only [allocation, form, nonconstructor, argumentsAccepted, calleeAccepted,
    bind, Except.bind] at accepted
  repeat' first | split at accepted
  all_goals try simp_all [IndirectCalleeAt, pure, Pure.pure, Except.pure]
  all_goals exact ⟨_, by assumption, by assumption⟩

end Solcore.SourceSemantics.SourceInferenceExecution
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceActualInitializerReceipt
/-! The initialized declaration receipt is built from the exact child call in
its actual edge. No alternate existential initializer state is introduced. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceExecution
open Frontend SourceInference TypeSystem Detail
namespace ActualInitializerReceipt

theorem annotation {context : SourceInference.Context}
    {source : Option Syntax.TypeExpr} {expected : Option Ty}
    (accepted : AnnotationExpected context source expected) :
    LocalLetRequirementTiming.Annotation context source expected := by
  cases accepted with
  | absent => exact .none
  | present accepted => exact .some accepted

def statement
    {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Statement}
    {expectedReturn : Ty} {initial : State} {result : StatementResult}
    {name : Syntax.Identifier} {sourceType : Option Syntax.TypeExpr} {initializer : Syntax.Expr}
    {expected : Option Ty} {value : InferredExpression} {ready : State}
    (accepted : inferStatementFuel (fuel + 1) context source expectedReturn initial = .ok result)
    (form : source.value = .letDecl name sourceType (some initializer))
    (annotated : AnnotationExpected context sourceType expected)
    (child : inferExprFuel fuel context initializer expected initial.allocateStatementId.2 = .ok (value, ready)) :
    LocalLetRequirementTiming.Receipt fuel context source initial result :=
  { name, initializer, annotation := sourceType, expected,
    annotationAccepted := annotation annotated, form, value, ready, child,
    completed := by
      cases annotated with
      | absent =>
          unfold inferStatementFuel at accepted
          simp only [form, child, bind, Except.bind, pure, Pure.pure, Except.pure] at accepted
          exact (Except.ok.inj accepted).symm
      | present resolved =>
          unfold inferStatementFuel at accepted
          simp only [form, resolved, child, bind, Except.bind, pure, Pure.pure, Except.pure] at accepted
          exact (Except.ok.inj accepted).symm }

def header
    {fuel : Nat} {context : SourceInference.Context} {source : Syntax.ForItem}
    {initial final : State} {result : ForItemForm}
    {name : Syntax.Identifier} {sourceType : Option Syntax.TypeExpr} {initializer : Syntax.Expr}
    {expected : Option Ty} {value : InferredExpression} {ready : State}
    (accepted : inferForItemFuel (fuel + 1) context source initial = .ok (result, final))
    (form : source.value = .letDecl name sourceType (some initializer))
    (annotated : AnnotationExpected context sourceType expected)
    (child : inferExprFuel fuel context initializer expected initial = .ok (value, ready)) :
    LocalHeaderRequirementTiming.Receipt fuel context source initial (result, final) :=
  { name, initializer, annotation := sourceType, expected,
    annotationAccepted := annotation annotated, form, value, ready, child,
    completed := by
      cases annotated with
      | absent =>
          unfold inferForItemFuel at accepted
          simp only [form, child, bind, Except.bind, pure, Pure.pure, Except.pure] at accepted
          exact (Except.ok.inj accepted).symm
      | present resolved =>
          unfold inferForItemFuel at accepted
          simp only [form, resolved, child, bind, Except.bind, pure, Pure.pure, Except.pure] at accepted
          exact (Except.ok.inj accepted).symm }

end ActualInitializerReceipt
end Solcore.SourceSemantics.SourceInferenceExecution
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceActualMatchCompletion
/-! The actual match suffix, after scrutinee and hidden-identity allocation. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceExecution
open Frontend SourceInference TypeSystem Detail

def matchCompletion (fuel : Nat) (context : SourceInference.Context)
    (statement : Syntax.Statement) (id : StatementId) (hidden : Resolved.LocalId)
    (scrutinee : InferredExpression) (arms : Syntax.Located Syntax.MatchArmsValue)
    (expectedReturn : Ty) (state : State) : Except Error StatementResult := do
  let outerScope := state.lexicalScope
  let checked ← inferMatchCasesFuel fuel context scrutinee.type expectedReturn outerScope arms.value.cases state
  let (defaultBody,state) ← match arms.value.defaultBody with
    | none => pure (none,checked.state)
    | some body => do
      let inferred ← inferStatementsFuel fuel context body.value expectedReturn checked.state
      pure (some (inferred.statements,inferred.sawReturn),inferred.state.restoreLexicalScope outerScope)
  let exhaustive := checked.hasWildcard || defaultBody.isSome ||
    exhaustsNominalConstructors context state scrutinee.type checked.cases
  if !exhaustive then throw (.nonExhaustiveMatch statement.span) else
    let requirements := checked.cases.flatMap fun arm => arm.pattern.requirements
    let defaultStatements := defaultBody.map (·.1)
    let defaultReturns := defaultBody.map (·.2) |>.getD true
    let sawReturn := checked.allReturn && defaultReturns
    let type := if sawReturn then state.resolve expectedReturn else .unit
    let state := state.recordNode (.statement {
      id := id
      span := statement.span
      type := type
      form := .matchWith {
        scrutinee := scrutinee.id
        hiddenScrutinee := hidden
        cases := checked.cases
        defaultBody := defaultStatements
        requirements := requirements
      }
    })
    pure {
      id := id
      type := type
      hasValue := sawReturn
      sawReturn := sawReturn
      state := state
    }


theorem matchCompletion_accepted
    {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Statement}
    {scrutinees : Syntax.NonemptyDelimitedList Syntax.Expr} {arms : Syntax.MatchArms}
    {expectedReturn : Ty} {initial allocated : State} {id : StatementId}
    {scrutinee : InferredExpression} {scrutineeState hiddenState : State} {hidden : Resolved.LocalId}
    {result : StatementResult}
    (form : source.value = .matchWith scrutinees arms)
    (allocation : initial.allocateStatementId = (id, allocated))
    (scrutineeAccepted : matchScrutinee fuel context source.span scrutinees.elements.toList allocated = .ok (scrutinee, scrutineeState))
    (hiddenAllocation : scrutineeState.allocateHiddenLocal = (hidden, hiddenState))
    (accepted : inferStatementFuel (fuel + 1) context source expectedReturn initial = .ok result) :
    matchCompletion fuel context source id hidden scrutinee arms expectedReturn hiddenState = .ok result := by
  unfold inferStatementFuel at accepted
  simp only [allocation, form] at accepted
  unfold matchScrutinee at scrutineeAccepted
  split at scrutineeAccepted
  all_goals simp_all [matchCompletion, bind, Except.bind, pure, Pure.pure, Except.pure]
  all_goals try exact accepted
  cases sourcesRun : inferExprsFuel fuel context scrutinees.elements.toList allocated with
  | error error => simp [sourcesRun] at scrutineeAccepted
  | ok pair =>
      simp only [sourcesRun] at scrutineeAccepted accepted
      simp only [Except.ok.injEq, Prod.mk.injEq] at scrutineeAccepted
      rcases scrutineeAccepted with ⟨valueEq, stateEq⟩
      cases valueEq
      cases stateEq
      simp_all
      exact accepted

end Solcore.SourceSemantics.SourceInferenceExecution
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceAssignedValueActualPrefix
/-! The assignment prefix keeps its actual operator guard and expected type.
Both semantic and lifetime traversals can consume these same child calls. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceExecution
open Frontend SourceInference TypeSystem Detail

private theorem accepted_bind {α β : Type} {action : Except Error α}
    {next : α → Except Error β} {result : β}
    (accepted : action >>= next = .ok result) :
    ∃ value, action = .ok value ∧ next value = .ok result := by
  cases action with
  | error => cases accepted
  | ok value => exact ⟨value, rfl, accepted⟩

theorem assignedValue_actual_prefix
    {fuel : Nat} {context : SourceInference.Context} {target value : Syntax.Expr}
    {operator : Syntax.ValueAssignOp} {initial final : State}
    {assignment : AssignmentResolution} {inferred : InferredExpression}
    (accepted : inferAssignedValueFuel fuel context target operator value initial =
      .ok (assignment, inferred, final)) :
    ∃ place placeState fitted,
      inferPlaceFuel fuel context target initial = .ok (place, placeState) ∧
      (match operator with | .equal => pure placeState | _ => unify placeState place.type .word) =
        (Except.ok fitted : Except Error State) ∧
      inferExprFuel fuel context value (some (assignmentExpected operator fitted place.type)) fitted =
        .ok (inferred, final) ∧
      assignment.target = { place with type := final.resolve place.type } := by
  unfold inferAssignedValueFuel at accepted
  obtain ⟨⟨place, placeState⟩, placeCall, afterPlace⟩ := accepted_bind accepted
  cases operator <;>
    obtain ⟨fitted, fitting, afterFitting⟩ := accepted_bind afterPlace
  all_goals
    obtain ⟨⟨result, state⟩, valueCall, returned⟩ := accepted_bind afterFitting
    cases returned
    exact ⟨place, placeState, fitted, placeCall, fitting, valueCall, rfl⟩

end Solcore.SourceSemantics.SourceInferenceExecution
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceGeneralizationReceiptCalls
/-! Initialized statements and headers expose the exact child call from their
actual execution receipt. Annotation evidence follows the original resolver. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceExecution
open Frontend SourceInference TypeSystem

theorem annotationExpected_of_receipt
    {context : SourceInference.Context} {annotation : Option Syntax.TypeExpr} {expected : Option Ty}
    (receipt : LocalLetRequirementTiming.Annotation context annotation expected) :
    AnnotationExpected context annotation expected := by
  cases receipt with
  | none => exact .absent
  | some accepted => exact .present accepted

theorem statement_initializer_child
    {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Statement}
    {expectedReturn : Ty} {initial : State} {result : Detail.StatementResult}
    (receipt : LocalLetRequirementTiming.Receipt fuel context source initial result)
    (accepted : (CallIndex.statement (fuel + 1) context source expectedReturn initial result).Accepted) :
    ChildStep (.statement (fuel + 1) context source expectedReturn initial result)
      (.expression fuel context receipt.initializer receipt.expected initial.allocateStatementId.2
        receipt.value receipt.ready) :=
  .statement_initializer accepted receipt.form rfl
    (annotationExpected_of_receipt receipt.annotationAccepted) receipt.child

theorem header_initializer_child
    {fuel : Nat} {context : SourceInference.Context} {source : Syntax.ForItem}
    {initial final : State} {inferred : ForItemForm}
    (receipt : LocalHeaderRequirementTiming.Receipt fuel context source initial (inferred, final))
    (accepted : (CallIndex.forItem (fuel + 1) context source initial inferred final).Accepted) :
    ChildStep (.forItem (fuel + 1) context source initial inferred final)
      (.expression fuel context receipt.initializer receipt.expected initial receipt.value receipt.ready) :=
  .forItem_initializer accepted receipt.form
    (annotationExpected_of_receipt receipt.annotationAccepted) receipt.child

end Solcore.SourceSemantics.SourceInferenceExecution
end
