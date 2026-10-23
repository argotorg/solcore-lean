import Solcore.SourceSemantics.SourceInferenceExpressionCallProvenance
import Solcore.Frontend.SourceInference.NodeShapeProperties
import Solcore.Frontend.SourceInference.OccurrenceProperties

/-! Operator resolution and call recording preserve node identities and syntax,
including when they attach coercions to argument expressions. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceExecution.ActualExpressionNodeShapes
open Frontend SourceInference TypeSystem Detail
open SourceInferenceSoundness



theorem append (nodes tail : List Node) : NodeShapesPreserved nodes (nodes ++ tail) :=
  fun node member => ⟨node, List.mem_append_left tail member, .refl node⟩

theorem unify {before after : State} {left right : Ty}
    (accepted : Detail.unify before left right = .ok after) :
    NodeShapesPreserved before.nodes after.nodes :=
  .of_eq (unify_occurrenceState_eq accepted).1

theorem application {context : SourceInference.Context} {call : ExpressionId} {calleeType : Ty}
    {arguments : List InferredExpression} {expected : Option Ty}
    {state : State} {result : IndirectApplicationResult}
    (accepted : applyFunctionType context call calleeType arguments expected state = .ok result) :
    NodeShapesPreserved state.nodes result.state.nodes :=
  .of_eq (applyFunctionType_occurrenceState_eq accepted).1

theorem recordExpected {context : SourceInference.Context} {source : Syntax.Expr}
    {id : ExpressionId} {type : Ty} {form : ExpressionForm}
    {requirements : List RequirementId} {expected : Option Ty} {state : State}
    {start : Option Nat} {result : InferredExpression × State}
    (accepted : recordExpressionWithExpected context source id type form
      requirements expected state start = .ok result) :
    NodeShapesPreserved state.nodes result.2.nodes := by
  obtain ⟨fitted, fit, _, recorded⟩ := recordExpressionWithExpected_success_record accepted
  rw [recorded]
  exact (NodeShapesPreserved.of_eq (withExpected_occurrenceState_eq fit).1).trans
    (NodeShapesPreserved.recordNode _ _)

theorem recordSelectedResult (source callee : Syntax.Expr) (name : String)
    (arguments : List InferredExpression) (attempt : CandidateAttemptResult)
    (result : InferredExpression) (trailing : List CoercionStep) (state : State) :
    NodeShapesPreserved state.nodes
      (recordSelectedCallResult source callee name arguments attempt result trailing state).2.nodes := by
  unfold recordSelectedCallResult
  exact (NodeShapesPreserved.attachExpressionCoercions _ _).trans
    ((NodeShapesPreserved.recordNode _ _).trans (NodeShapesPreserved.recordNode _ _))

theorem recordSelected (source callee : Syntax.Expr) (name : String)
    (arguments : List InferredExpression) (attempt : CandidateAttemptResult) :
    NodeShapesPreserved attempt.state.nodes (recordSelectedCall source callee name arguments attempt).2.nodes :=
  recordSelectedResult _ _ _ _ _ _ _ _

theorem recordIndirect (source : Syntax.Expr) (callee : InferredExpression)
    (arguments : List InferredExpression) (result : IndirectApplicationResult) :
    NodeShapesPreserved result.state.nodes (recordIndirectCall source callee arguments result).2.nodes :=
  NodeShapesPreserved.recordNode _ _

theorem recordBuiltin {source callee : Syntax.Expr} {name : String} {function : BuiltinFunctionId}
    {arguments : List InferredExpression} {call : ExpressionId} {expected : Option Ty} {state : State}
    {result : InferredExpression × State}
    (accepted : recordBuiltinFunctionCall source callee name function arguments call expected state = .ok result) :
    NodeShapesPreserved state.nodes result.2.nodes := by
  obtain ⟨calleeId, nodes⟩ := recordBuiltinFunctionCall_success_nodes accepted
  rw [nodes]
  exact append _ _

theorem unary
    {context : SourceInference.Context} {source : Syntax.Expr} {id : ExpressionId}
    {operator : Syntax.Located Syntax.UnaryOp} {value : InferredExpression}
    {expected : Option Ty} {literals : List IntegerLiteralOrigin} {state : State}
    {result : InferredExpression × State}
    (dispatch : UnaryExpressionDispatchFacts context source id operator value expected literals state result) :
    NodeShapesPreserved state.nodes result.2.nodes := by
  have finish (operatorResult : OperatorInferenceResult)
      (accepted : inferUnaryOperator context operator.value value.type expected literals state = .ok operatorResult)
      (recorded : recordExpressionWithExpected context source id operatorResult.type
        (.unary operator.value value.id) operatorResult.requirements expected operatorResult.state = .ok result) :
      NodeShapesPreserved state.nodes result.2.nodes :=
    (NodeShapesPreserved.of_eq (inferUnaryOperator_occurrenceState_eq accepted).1).trans
      (recordExpected recorded)
  cases dispatch with
  | directFunction _ _ accepted recorded => exact finish _ accepted recorded
  | traitMethod _ accepted recorded => exact finish _ accepted recorded
  | @selectedFunction name head tail attempt _ lookup selected recorded =>
    let callee : Syntax.Expr := {
      span := operator.span
      value := .identifier {span := operator.span, value := name} }
    have after := recordSelected source callee name [value] attempt
    change recordSelectedCall source callee name [value] attempt = result at recorded
    rw [recorded] at after
    exact (NodeShapesPreserved.of_eq (selectFunctionCandidateFrom_occurrenceState_eq selected).1).trans after

theorem binary
    {context : SourceInference.Context} {source : Syntax.Expr} {id : ExpressionId}
    {operator : Syntax.Located Syntax.BinaryOp} {left right : InferredExpression}
    {expected : Option Ty} {literals : List IntegerLiteralOrigin} {state : State}
    {result : InferredExpression × State}
    (dispatch : BinaryExpressionDispatchFacts context source id operator left right expected literals state result) :
    NodeShapesPreserved state.nodes result.2.nodes := by
  have finish (operatorResult : OperatorInferenceResult)
      (accepted : inferBinaryOperator context operator.value left.type right.type expected literals state = .ok operatorResult)
      (recorded : recordExpressionWithExpected context source id operatorResult.type
        (.binary left.id operator.value right.id) operatorResult.requirements expected operatorResult.state = .ok result) :
      NodeShapesPreserved state.nodes result.2.nodes :=
    (NodeShapesPreserved.of_eq (inferBinaryOperator_occurrenceState_eq accepted).1).trans
      (recordExpected recorded)
  cases dispatch with
  | directFunction _ _ accepted recorded => exact finish _ accepted recorded
  | traitMethod _ accepted recorded => exact finish _ accepted recorded
  | @selectedFunction name head tail attempt fitted _ lookup selected fitting recorded =>
    let callee : Syntax.Expr := {
      span := operator.span
      value := .identifier {span := operator.span, value := name} }
    have after := recordSelectedResult source callee name [left, right]
      attempt fitted.expression fitted.coercions fitted.state
    change recordSelectedCallResult source callee name [left, right] attempt
      fitted.expression fitted.coercions fitted.state = result at recorded
    rw [recorded] at after
    exact (NodeShapesPreserved.of_eq (selectFunctionCandidateFrom_occurrenceState_eq selected).1).trans
      ((NodeShapesPreserved.of_eq (withExpected_occurrenceState_eq fitting).1).trans after)

theorem callArguments
    {fuel : Nat} {context : SourceInference.Context} {source callee : Syntax.Expr}
    {arguments : Syntax.DelimitedList Syntax.Expr} {id : ExpressionId} {expected : Option Ty}
    {initial : State} {child : List InferredExpression × State} {result : InferredExpression × State}
    (nonconstructor : constructorCalleeCandidates context initial callee = .ok [])
    (childAccepted : inferExprsFuel fuel context arguments.elements initial = .ok child)
    (dispatch : CallExpressionDispatchProvenanceFacts context source callee arguments id expected fuel initial result) :
    NodeShapesPreserved child.2.nodes result.2.nodes := by
  cases dispatch with
  | constructor discovery _ _ => simp [nonconstructor] at discovery
  | @selected inferredArguments argumentState name candidates integerLiterals attempt _ actualArguments origin selected recorded =>
    cases Except.ok.inj (actualArguments.symm.trans childAccepted)
    have after := recordSelected source callee name inferredArguments attempt
    rw [recorded] at after
    exact (NodeShapesPreserved.of_eq (selectFunctionCandidateFrom_occurrenceState_eq selected).1).trans after
  | builtin _ actualArguments recorded =>
    cases Except.ok.inj (actualArguments.symm.trans childAccepted)
    exact recordBuiltin recorded
  | @indirect inferredArguments argumentState calleeState inferredCallee application _ actualArguments _ calleeAccepted applicationAccepted recorded =>
    cases Except.ok.inj (actualArguments.symm.trans childAccepted)
    have after := recordIndirect source inferredCallee inferredArguments application
    rw [recorded] at after
    exact (inferExprFuel_occurrenceGraph calleeAccepted).graph.shapes.trans
      ((ActualExpressionNodeShapes.application applicationAccepted).trans after)

end Solcore.SourceSemantics.SourceInferenceExecution.ActualExpressionNodeShapes
