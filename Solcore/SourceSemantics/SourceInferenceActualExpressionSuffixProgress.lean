import Solcore.SourceSemantics.SourceInferenceActualExpressionLifetime

/-! The remaining operator and call computation extends the inference state
returned by its actual child. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceExecution
open Frontend SourceInference TypeSystem Detail
open SourceInferenceSoundness SourceInferenceSoundness.ProtectedVariables

theorem unary_suffix_progress
    {context : SourceInference.Context} {source : Syntax.Expr} {id : ExpressionId}
    {operator : Syntax.Located Syntax.UnaryOp} {value : InferredExpression}
    {expected : Option Ty} {literals : List IntegerLiteralOrigin} {state : State}
    {result : InferredExpression × State}
    (ready : state.InferenceReady) (catalog : LifetimeInferenceContext context)
    (below : value.type.VariablesBelow state.inference.next)
    (expectedBelow : ∀ type ∈ expected, type.VariablesBelow state.inference.next)
    (dispatch : UnaryExpressionDispatchFacts context source id operator value expected literals state result) :
    state.InferenceProgress result.2 := by
  have finish (operatorResult : OperatorInferenceResult)
      (accepted : inferUnaryOperator context operator.value value.type expected literals state = .ok operatorResult)
      (recorded : recordExpressionWithExpected context source id operatorResult.type
        (.unary operator.value value.id) operatorResult.requirements expected operatorResult.state = .ok result) :
      state.InferenceProgress result.2 := by
    have properties := inferUnaryOperator_inferenceProperties ready below expectedBelow accepted
    exact properties.1.trans (recordExpressionWithExpected_inferenceProperties
      properties.2.1 properties.2.2
      (fun type member => (expectedBelow type member).weaken properties.1.next_le) recorded).1
  cases dispatch with
  | directFunction _ _ accepted recorded => exact finish _ accepted recorded
  | traitMethod _ accepted recorded => exact finish _ accepted recorded
  | @selectedFunction name head tail attempt _ lookup selected recorded =>
      have cataloged := functionsNamed_success_subset_catalog lookup
      have properties := selectFunctionCandidateFrom_inferenceProperties ready
        (by intro argument member; cases List.mem_singleton.mp member; exact below)
        (fun signature member => catalog.formation.function_scheme_body_variablesBelow
          (cataloged member) (catalog.canonical signature (cataloged member)) _) expectedBelow selected
      let callee : Syntax.Expr := {
        span := operator.span
        value := .identifier {span := operator.span, value := name} }
      have after := recordSelectedCall_inferenceProperties source callee name [value] attempt
        properties.2.1 properties.2.2
      change recordSelectedCall source callee name [value] attempt = result at recorded
      rw [recorded] at after
      exact properties.1.trans after.1

theorem binary_suffix_progress
    {context : SourceInference.Context} {source : Syntax.Expr} {id : ExpressionId}
    {operator : Syntax.Located Syntax.BinaryOp} {left right : InferredExpression}
    {expected : Option Ty} {literals : List IntegerLiteralOrigin} {state : State}
    {result : InferredExpression × State}
    (ready : state.InferenceReady) (catalog : LifetimeInferenceContext context)
    (leftBelow : left.type.VariablesBelow state.inference.next)
    (rightBelow : right.type.VariablesBelow state.inference.next)
    (expectedBelow : ∀ type ∈ expected, type.VariablesBelow state.inference.next)
    (dispatch : BinaryExpressionDispatchFacts context source id operator left right expected literals state result) :
    state.InferenceProgress result.2 := by
  have finish (operatorResult : OperatorInferenceResult)
      (accepted : inferBinaryOperator context operator.value left.type right.type expected literals state = .ok operatorResult)
      (recorded : recordExpressionWithExpected context source id operatorResult.type
        (.binary left.id operator.value right.id) operatorResult.requirements expected operatorResult.state = .ok result) :
      state.InferenceProgress result.2 := by
    have properties := inferBinaryOperator_inferenceProperties ready leftBelow rightBelow expectedBelow accepted
    exact properties.1.trans (recordExpressionWithExpected_inferenceProperties
      properties.2.1 properties.2.2
      (fun type member => (expectedBelow type member).weaken properties.1.next_le) recorded).1
  cases dispatch with
  | directFunction _ _ accepted recorded => exact finish _ accepted recorded
  | traitMethod _ accepted recorded => exact finish _ accepted recorded
  | @selectedFunction name head tail attempt fitted _ lookup selected fitting recorded =>
      have cataloged := functionsNamed_success_subset_catalog lookup
      have argumentsBelow : ∀ argument ∈ [left, right],
          argument.type.VariablesBelow state.inference.next := by
        intro argument member
        rcases List.mem_cons.mp member with rfl | member
        · exact leftBelow
        · cases List.mem_singleton.mp member
          exact rightBelow
      have boolBelow : ∀ type ∈ (some Ty.bool : Option Ty),
          type.VariablesBelow state.inference.next := by
        intro type member
        cases Option.some.inj (Option.mem_def.mp member)
        exact Ty.variablesBelow_constructor _ _
      have properties := selectFunctionCandidateFrom_inferenceProperties ready argumentsBelow
        (fun signature member => catalog.formation.function_scheme_body_variablesBelow
          (cataloged member) (catalog.canonical signature (cataloged member)) _) boolBelow selected
      have fittedProperties := withExpected_inferenceProperties properties.2.1 properties.2.2
        (fun type member => (expectedBelow type member).weaken properties.1.next_le) fitting
      let callee : Syntax.Expr := {
        span := operator.span
        value := .identifier {span := operator.span, value := name} }
      have after := recordSelectedCallResult_inferenceProperties source callee name [left, right]
        attempt fitted.expression fitted.coercions fitted.state fittedProperties.2.1 fittedProperties.2.2
      change recordSelectedCallResult source callee name [left, right] attempt
        fitted.expression fitted.coercions fitted.state = result at recorded
      rw [recorded] at after
      exact properties.1.trans (fittedProperties.1.trans after.1)

theorem call_arguments_suffix_progress
    {fuel : Nat} {context : SourceInference.Context} {source callee : Syntax.Expr}
    {arguments : Syntax.DelimitedList Syntax.Expr} {id : ExpressionId} {expected : Option Ty}
    {initial : State} {child : List InferredExpression × State} {result : InferredExpression × State}
    (ready : initial.InferenceReady) (catalog : LifetimeInferenceContext context)
    (expectedBelow : ∀ type ∈ expected, type.VariablesBelow initial.inference.next)
    (nonconstructor : constructorCalleeCandidates context initial callee = .ok [])
    (childAccepted : inferExprsFuel fuel context arguments.elements initial = .ok child)
    (dispatch : CallExpressionDispatchProvenanceFacts context source callee arguments id expected fuel initial result) :
    child.2.InferenceProgress result.2 := by
  have properties := inferExprsFuel_inferenceProperties ready catalog.formation catalog.canonical childAccepted
  have expectedAfter : ∀ type ∈ expected, type.VariablesBelow child.2.inference.next :=
    fun type member => (expectedBelow type member).weaken properties.1.next_le
  cases dispatch with
  | constructor discovery _ _ => simp [nonconstructor] at discovery
  | @selected inferredArguments argumentState name candidates integerLiterals attempt _ actualArguments origin selected recorded =>
      cases Except.ok.inj (actualArguments.symm.trans childAccepted)
      have selectedProperties := selectFunctionCandidateFrom_inferenceProperties properties.2.1 properties.2.2
        (fun signature member => catalog.formation.function_scheme_body_variablesBelow
          (origin.candidatesSubset member) (catalog.canonical signature (origin.candidatesSubset member)) _)
        expectedAfter selected
      have after := recordSelectedCall_inferenceProperties source callee name inferredArguments attempt
        selectedProperties.2.1 selectedProperties.2.2
      rw [recorded] at after
      exact selectedProperties.1.trans after.1
  | builtin _ actualArguments recorded =>
      cases Except.ok.inj (actualArguments.symm.trans childAccepted)
      exact (recordBuiltinFunctionCall_inferenceProperties properties.2.1 properties.2.2 expectedAfter recorded).1
  | @indirect inferredArguments argumentState calleeState inferredCallee application _ actualArguments _ calleeAccepted applicationAccepted recorded =>
      cases Except.ok.inj (actualArguments.symm.trans childAccepted)
      have calleeProperties := inferExprFuel_inferenceProperties properties.2.1
        catalog.formation catalog.canonical (by simp) calleeAccepted
      have applicationProperties := applyFunctionType_inferenceProperties calleeProperties.2.1 calleeProperties.2.2
        (fun argument member => (properties.2.2 argument member).weaken calleeProperties.1.next_le)
        (fun type member => (expectedAfter type member).weaken calleeProperties.1.next_le) applicationAccepted
      have after := recordIndirectCall_inferenceProperties source inferredCallee inferredArguments application
        applicationProperties.2.1 applicationProperties.2.2
      rw [recorded] at after
      exact calleeProperties.1.trans (applicationProperties.1.trans after.1)

end Solcore.SourceSemantics.SourceInferenceExecution
