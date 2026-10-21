import Solcore.SourceSemantics.SourceInferenceExpressionCallProvenance
import Solcore.Frontend.SourceInference.LocalGeneralizationInference

/-! Operator resolution and call recording preserve initialized declarations,
including when they attach coercions to argument expressions. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceExecution.ActualBinderRetention
open Frontend SourceInference TypeSystem Detail
open SourceInferenceSoundness
open LocalGeneralizationEvents (BindersRetained)

theorem unary
    {context : SourceInference.Context} {source : Syntax.Expr} {id : ExpressionId}
    {operator : Syntax.Located Syntax.UnaryOp} {value : InferredExpression}
    {expected : Option Ty} {literals : List IntegerLiteralOrigin} {state : State}
    {result : InferredExpression × State}
    (dispatch : UnaryExpressionDispatchFacts context source id operator value expected literals state result) :
    BindersRetained state.nodes result.2.nodes := by
  have finish (operatorResult : OperatorInferenceResult)
      (accepted : inferUnaryOperator context operator.value value.type expected literals state = .ok operatorResult)
      (recorded : recordExpressionWithExpected context source id operatorResult.type
        (.unary operator.value value.id) operatorResult.requirements expected operatorResult.state = .ok result) :
      BindersRetained state.nodes result.2.nodes :=
    (LocalGeneralizationEvents.Progress.inferUnaryOperator accepted).retained.trans
      (BindersRetained.recordExpressionWithExpected recorded)
  cases dispatch with
  | directFunction _ _ accepted recorded => exact finish _ accepted recorded
  | traitMethod _ accepted recorded => exact finish _ accepted recorded
  | @selectedFunction name head tail attempt _ lookup selected recorded =>
    let callee : Syntax.Expr := {
      span := operator.span
      value := .identifier {span := operator.span, value := name} }
    have after := (LocalGeneralizationEvents.Progress.recordSelectedCall source callee name [value] attempt).retained
    change recordSelectedCall source callee name [value] attempt = result at recorded
    rw [recorded] at after
    exact (LocalGeneralizationEvents.Progress.selectFunctionCandidateFrom selected).retained.trans after

theorem binary
    {context : SourceInference.Context} {source : Syntax.Expr} {id : ExpressionId}
    {operator : Syntax.Located Syntax.BinaryOp} {left right : InferredExpression}
    {expected : Option Ty} {literals : List IntegerLiteralOrigin} {state : State}
    {result : InferredExpression × State}
    (dispatch : BinaryExpressionDispatchFacts context source id operator left right expected literals state result) :
    BindersRetained state.nodes result.2.nodes := by
  have finish (operatorResult : OperatorInferenceResult)
      (accepted : inferBinaryOperator context operator.value left.type right.type expected literals state = .ok operatorResult)
      (recorded : recordExpressionWithExpected context source id operatorResult.type
        (.binary left.id operator.value right.id) operatorResult.requirements expected operatorResult.state = .ok result) :
      BindersRetained state.nodes result.2.nodes :=
    (LocalGeneralizationEvents.Progress.inferBinaryOperator accepted).retained.trans
      (BindersRetained.recordExpressionWithExpected recorded)
  cases dispatch with
  | directFunction _ _ accepted recorded => exact finish _ accepted recorded
  | traitMethod _ accepted recorded => exact finish _ accepted recorded
  | @selectedFunction name head tail attempt fitted _ lookup selected fitting recorded =>
    let callee : Syntax.Expr := {
      span := operator.span
      value := .identifier {span := operator.span, value := name} }
    have after := BindersRetained.recordSelectedCallResult source callee name [left, right]
      attempt fitted.expression fitted.coercions fitted.state
    change recordSelectedCallResult source callee name [left, right] attempt
      fitted.expression fitted.coercions fitted.state = result at recorded
    rw [recorded] at after
    exact (LocalGeneralizationEvents.Progress.selectFunctionCandidateFrom selected).retained.trans
      ((LocalGeneralizationEvents.Progress.withExpected fitting).retained.trans after)

theorem callArguments
    {fuel : Nat} {context : SourceInference.Context} {source callee : Syntax.Expr}
    {arguments : Syntax.DelimitedList Syntax.Expr} {id : ExpressionId} {expected : Option Ty}
    {initial : State} {child : List InferredExpression × State} {result : InferredExpression × State}
    (nonconstructor : constructorCalleeCandidates context initial callee = .ok [])
    (childAccepted : inferExprsFuel fuel context arguments.elements initial = .ok child)
    (dispatch : CallExpressionDispatchProvenanceFacts context source callee arguments id expected fuel initial result) :
    BindersRetained child.2.nodes result.2.nodes := by
  cases dispatch with
  | constructor discovery _ _ => simp [nonconstructor] at discovery
  | @selected inferredArguments argumentState name candidates integerLiterals attempt _ actualArguments origin selected recorded =>
    cases Except.ok.inj (actualArguments.symm.trans childAccepted)
    have after := (LocalGeneralizationEvents.Progress.recordSelectedCall source callee name inferredArguments attempt).retained
    rw [recorded] at after
    exact (LocalGeneralizationEvents.Progress.selectFunctionCandidateFrom selected).retained.trans after
  | builtin _ actualArguments recorded =>
    cases Except.ok.inj (actualArguments.symm.trans childAccepted)
    exact (LocalGeneralizationEvents.Progress.recordBuiltinFunctionCall recorded).retained
  | @indirect inferredArguments argumentState calleeState inferredCallee application _ actualArguments _ calleeAccepted applicationAccepted recorded =>
    cases Except.ok.inj (actualArguments.symm.trans childAccepted)
    have after := (LocalGeneralizationEvents.Progress.recordIndirectCall source inferredCallee inferredArguments application).retained
    rw [recorded] at after
    exact (LocalGeneralizationEvents.inferExprFuel_origins_progress calleeAccepted).retained.trans
      ((LocalGeneralizationEvents.Progress.applyFunctionType applicationAccepted).retained.trans after)

end Solcore.SourceSemantics.SourceInferenceExecution.ActualBinderRetention
