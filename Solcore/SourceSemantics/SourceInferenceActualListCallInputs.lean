import Solcore.SourceSemantics.SourceInferenceActualCallProperties

/-! Exact successful prefixes supply the ordinary inputs for ordered children. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceExecution
open Frontend SourceInference TypeSystem Detail SourceInferenceSoundness.ProtectedVariables
namespace ChildStep

theorem inputs_expressions
    {fuel : Nat} {context : SourceInference.Context} {sources : List Syntax.Expr}
    {initial final : State} {values : List InferredExpression} {child : CallIndex}
    (inputs : (CallIndex.expressions fuel context sources initial values final).Inputs)
    (step : ChildStep (.expressions fuel context sources initial values final) child) : child.Inputs := by
  cases step with
  | expressions_head => exact ⟨inputs.ready, inputs.wellFormed, inputs.catalog, by simp [CallIndex.InputBounds]⟩
  | expressions_tail _ head _ =>
      have properties := inferExprFuel_inferenceProperties inputs.ready inputs.catalog.formation inputs.catalog.canonical (by simp) head
      exact ⟨properties.2.1, (inferExprFuel_direct_progress head).wellFormed inputs.wellFormed, inputs.catalog, trivial⟩

theorem inputs_statements
    {fuel : Nat} {context : SourceInference.Context} {sources : List Syntax.Statement}
    {expected : Ty} {initial : State} {result : BlockResult} {child : CallIndex}
    (inputs : (CallIndex.statements fuel context sources expected initial result).Inputs)
    (step : ChildStep (.statements fuel context sources expected initial result) child) : child.Inputs := by
  cases step with
  | statements_head => exact ⟨inputs.ready, inputs.wellFormed, inputs.catalog, inputs.bounds⟩
  | statements_tail _ _ head _ =>
      have properties := inferStatementFuel_inferenceProperties inputs.ready inputs.catalog.formation inputs.catalog.canonical inputs.bounds head
      exact ⟨properties.2.1, (inferStatementFuel_direct_progress head).wellFormed inputs.wellFormed,
        inputs.catalog, inputs.bounds.weaken properties.1.next_le⟩

theorem inputs_forItems
    {fuel : Nat} {context : SourceInference.Context} {sources : List Syntax.ForItem}
    {initial : State} {result : InferredForItems} {child : CallIndex}
    (inputs : (CallIndex.forItems fuel context sources initial result).Inputs)
    (step : ChildStep (.forItems fuel context sources initial result) child) : child.Inputs := by
  cases step with
  | forItems_head => exact ⟨inputs.ready, inputs.wellFormed, inputs.catalog, trivial⟩
  | forItems_tail _ head _ =>
      have properties := inferForItemFuel_inferenceProperties inputs.ready inputs.catalog.formation inputs.catalog.canonical head
      exact ⟨properties.2, (inferForItemFuel_direct_progress head).wellFormed inputs.wellFormed,
        inputs.catalog, trivial⟩

theorem inputs_constructorArguments
    {fuel : Nat} {context : SourceInference.Context} {sources : List Syntax.Expr}
    {expected : List Ty} {initial final : State} {values : List InferredExpression} {child : CallIndex}
    (inputs : (CallIndex.constructorArguments fuel context sources expected initial values final).Inputs)
    (step : ChildStep (.constructorArguments fuel context sources expected initial values final) child) : child.Inputs := by
  cases step with
  | constructorArguments_head =>
      refine ⟨inputs.ready, inputs.wellFormed, inputs.catalog, ?_⟩
      intro type member
      cases member
      exact inputs.ready.solved.variablesBelow_apply (inputs.bounds _ (by simp))
  | constructorArguments_tail _ head _ =>
      have properties := inferExprFuel_inferenceProperties inputs.ready inputs.catalog.formation inputs.catalog.canonical
        (by intro type member; cases member; exact inputs.ready.solved.variablesBelow_apply (inputs.bounds _ (by simp))) head
      exact ⟨properties.2.1, (inferExprFuel_direct_progress head).wellFormed inputs.wellFormed,
        inputs.catalog, fun type member => (inputs.bounds type (List.mem_cons_of_mem _ member)).weaken properties.1.next_le⟩

theorem inputs_constructorApplication
    {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Expr} {id : ExpressionId}
    {instantiation : DataConstructorInstantiation} {sources : List Syntax.Expr} {expected : Option Ty}
    {initial final : State} {value : InferredExpression} {child : CallIndex}
    (inputs : (CallIndex.constructorApplication fuel context source id instantiation sources expected initial value final).Inputs)
    (step : ChildStep (.constructorApplication fuel context source id instantiation sources expected initial value final) child) : child.Inputs := by
  cases step with
  | constructorApplication_arguments _ _ fitting _ =>
      cases expected with
      | none =>
          cases Except.ok.inj fitting
          exact ⟨inputs.ready, inputs.wellFormed, inputs.catalog, inputs.bounds.1⟩
      | some expected =>
          have expectedBelow := inputs.bounds.2.2 expected (by simp)
          have progress := unify_inferenceProgress inputs.ready.solved inputs.bounds.2.1 expectedBelow fitting
          exact ⟨unify_preserves_inferenceReady inputs.ready inputs.bounds.2.1 expectedBelow fitting,
            unify_preserves_requirementsWellFormed fitting inputs.wellFormed, inputs.catalog,
            fun type member => (inputs.bounds.1 type member).weaken progress.next_le⟩

end ChildStep
end Solcore.SourceSemantics.SourceInferenceExecution
