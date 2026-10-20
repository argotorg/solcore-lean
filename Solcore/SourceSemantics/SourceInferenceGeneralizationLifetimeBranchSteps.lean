import Solcore.SourceSemantics.SourceInferenceGeneralizationLifetimeForSteps

/-! Branch and loop continuations restore the actual saved lexical scope. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
open Frontend SourceInference TypeSystem Detail

theorem LifetimeInferenceContext.withLoopDepth {context : SourceInference.Context}
    (catalog : LifetimeInferenceContext context) (depth : Nat) :
    LifetimeInferenceContext {context with loopDepth := depth} :=
  ⟨catalog.catalog, catalog.formation, catalog.canonical⟩

private theorem allocatedStatement_properties
    {initial next : State} {id : StatementId}
    (ready : initial.InferenceReady)
    (allocation : initial.allocateStatementId = (id, next)) :
    initial.InferenceProgress next ∧ next.InferenceReady := by
  have progress := State.InferenceProgress.allocateStatementId initial ready.solved
  have nextReady := ready.allocateStatementId
  rw [allocation] at progress nextReady
  exact ⟨progress, nextReady⟩

namespace GeneralizationLifetime
variable {whole : TypedSource} {finalSubstitution : Substitution}
    {binder : TypedBinder} {initializer : ExpressionId}
    {event : RetainedGeneralization whole finalSubstitution binder initializer}

theorem recordUnit {entryNext : Nat} {state : State} {outputs : List Ty}
    (lifetime : GeneralizationLifetime event entryNext state outputs)
    (id : StatementId) (span : Syntax.SourceSpan) (form : StatementForm) :
    GeneralizationLifetime event entryNext
      (state.recordNode (.statement {id, span, type := .unit, form})) [.unit] :=
  (lifetime.recordNode _).replaceOutputs
    (by
      intro type member
      cases List.mem_singleton.mp member
      exact safe_closed _ _ (Ty.variablesBelow_constructor 0 _))

theorem while_body
    {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Statement}
    {condition : Syntax.Expr} {body : Syntax.Block} {expectedReturn : Ty}
    {initial allocated : State} {id : StatementId}
    {conditionResult : InferredExpression × State} {bodyResult : BlockResult}
    {result : StatementResult}
    (ready : initial.InferenceReady) (catalog : LifetimeInferenceContext context)
    (form : source.value = .whileLoop condition body)
    (allocation : initial.allocateStatementId = (id, allocated))
    (conditionAccepted : inferExprFuel fuel context condition (some .bool) allocated = .ok conditionResult)
    (bodyAccepted : inferStatementsFuel fuel {context with loopDepth := context.loopDepth + 1}
      body.value expectedReturn conditionResult.2 = .ok bodyResult)
    (accepted : inferStatementFuel (fuel + 1) context source expectedReturn initial = .ok result)
    (lifetime : GeneralizationLifetime event conditionResult.2.inference.next bodyResult.state [bodyResult.type]) :
    GeneralizationLifetime event initial.inference.next result.state [result.type] := by
  have allocatedProperties := allocatedStatement_properties ready allocation
  have conditionProperties := inferExprFuel_inferenceProperties allocatedProperties.2
    catalog.formation catalog.canonical (by
      intro type member; cases member; exact Ty.variablesBelow_constructor _ _) conditionAccepted
  have restored := lifetime.restoreScope conditionResult.2.lexicalScope
    (inferStatementsFuel_binders_subset bodyAccepted)
  have recorded := restored.recordUnit id source.span
    (.whileLoop conditionResult.1.id bodyResult.statements)
  have atEntry := recorded.weaken_entry
    (allocatedProperties.1.trans conditionProperties.1).next_le
  unfold inferStatementFuel at accepted
  simp only [allocation, form, conditionAccepted, bodyAccepted, bind, Except.bind,
    pure, Pure.pure, Except.pure, Except.ok.injEq] at accepted
  cases accepted
  exact atEntry

theorem while_condition
    {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Statement}
    {condition : Syntax.Expr} {body : Syntax.Block} {expectedReturn : Ty}
    {initial allocated : State} {id : StatementId}
    {conditionResult : InferredExpression × State} {bodyResult : BlockResult}
    {result : StatementResult}
    (ready : initial.InferenceReady) (wellFormed : initial.RequirementsWellFormed)
    (catalog : LifetimeInferenceContext context)
    (returnBelow : expectedReturn.VariablesBelow initial.inference.next)
    (form : source.value = .whileLoop condition body)
    (allocation : initial.allocateStatementId = (id, allocated))
    (conditionAccepted : inferExprFuel fuel context condition (some .bool) allocated = .ok conditionResult)
    (bodyAccepted : inferStatementsFuel fuel {context with loopDepth := context.loopDepth + 1}
      body.value expectedReturn conditionResult.2 = .ok bodyResult)
    (accepted : inferStatementFuel (fuel + 1) context source expectedReturn initial = .ok result)
    (lifetime : GeneralizationLifetime event allocated.inference.next conditionResult.2 [conditionResult.1.type]) :
    GeneralizationLifetime event initial.inference.next result.state [result.type] := by
  have allocatedEq : allocated = initial.allocateStatementId.2 :=
    (congrArg Prod.snd allocation).symm
  have allocatedProperties := allocatedStatement_properties ready allocation
  have conditionProperties := inferExprFuel_inferenceProperties allocatedProperties.2
    catalog.formation catalog.canonical (by
      intro type member; cases member; exact Ty.variablesBelow_constructor _ _) conditionAccepted
  have conditionWF := (inferExprFuel_direct_progress conditionAccepted).wellFormed
    (show allocated.RequirementsWellFormed by
      rw [allocatedEq]
      change initial.RequirementsWellFormed
      exact wellFormed)
  have after := lifetime.inferStatements conditionProperties.2.1 conditionWF
    (catalog.withLoopDepth (context.loopDepth + 1))
    (returnBelow.weaken (allocatedProperties.1.trans conditionProperties.1).next_le)
    (lifetime.older _ (returnBelow.weaken allocatedProperties.1.next_le)) bodyAccepted
  have restored := after.restoreScope conditionResult.2.lexicalScope
    (inferStatementsFuel_binders_subset bodyAccepted)
  have recorded := restored.recordUnit id source.span
    (.whileLoop conditionResult.1.id bodyResult.statements)
  have atEntry := recorded.weaken_entry allocatedProperties.1.next_le
  unfold inferStatementFuel at accepted
  simp only [allocation, form, conditionAccepted, bodyAccepted, bind, Except.bind,
    pure, Pure.pure, Except.pure, Except.ok.injEq] at accepted
  cases accepted
  exact atEntry

theorem if_without_else_body
    {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Statement}
    {condition : Syntax.Expr} {body : Syntax.Block} {expectedReturn : Ty}
    {initial allocated : State} {id : StatementId}
    {conditionResult : InferredExpression × State} {bodyResult : BlockResult}
    {result : StatementResult}
    (ready : initial.InferenceReady) (catalog : LifetimeInferenceContext context)
    (form : source.value = .ifThen condition body none)
    (allocation : initial.allocateStatementId = (id, allocated))
    (conditionAccepted : inferExprFuel fuel context condition (some .bool) allocated = .ok conditionResult)
    (bodyAccepted : inferStatementsFuel fuel context body.value expectedReturn conditionResult.2 = .ok bodyResult)
    (accepted : inferStatementFuel (fuel + 1) context source expectedReturn initial = .ok result)
    (lifetime : GeneralizationLifetime event conditionResult.2.inference.next bodyResult.state [bodyResult.type]) :
    GeneralizationLifetime event initial.inference.next result.state [result.type] := by
  have allocatedProperties := allocatedStatement_properties ready allocation
  have conditionProperties := inferExprFuel_inferenceProperties allocatedProperties.2
    catalog.formation catalog.canonical (by
      intro type member; cases member; exact Ty.variablesBelow_constructor _ _) conditionAccepted
  have restored := lifetime.restoreScope conditionResult.2.lexicalScope
    (inferStatementsFuel_binders_subset bodyAccepted)
  have recorded := restored.recordUnit id source.span
    (.ifThen conditionResult.1.id bodyResult.statements none)
  have atEntry := recorded.weaken_entry
    (allocatedProperties.1.trans conditionProperties.1).next_le
  unfold inferStatementFuel at accepted
  simp only [allocation, form, conditionAccepted, bodyAccepted, bind, Except.bind,
    pure, Pure.pure, Except.pure, Except.ok.injEq] at accepted
  cases accepted
  exact atEntry

theorem if_without_else_condition
    {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Statement}
    {condition : Syntax.Expr} {body : Syntax.Block} {expectedReturn : Ty}
    {initial allocated : State} {id : StatementId}
    {conditionResult : InferredExpression × State} {bodyResult : BlockResult}
    {result : StatementResult}
    (ready : initial.InferenceReady) (wellFormed : initial.RequirementsWellFormed)
    (catalog : LifetimeInferenceContext context)
    (returnBelow : expectedReturn.VariablesBelow initial.inference.next)
    (form : source.value = .ifThen condition body none)
    (allocation : initial.allocateStatementId = (id, allocated))
    (conditionAccepted : inferExprFuel fuel context condition (some .bool) allocated = .ok conditionResult)
    (bodyAccepted : inferStatementsFuel fuel context body.value expectedReturn conditionResult.2 = .ok bodyResult)
    (accepted : inferStatementFuel (fuel + 1) context source expectedReturn initial = .ok result)
    (lifetime : GeneralizationLifetime event allocated.inference.next conditionResult.2 [conditionResult.1.type]) :
    GeneralizationLifetime event initial.inference.next result.state [result.type] := by
  have allocatedEq : allocated = initial.allocateStatementId.2 :=
    (congrArg Prod.snd allocation).symm
  have allocatedProperties := allocatedStatement_properties ready allocation
  have conditionProperties := inferExprFuel_inferenceProperties allocatedProperties.2
    catalog.formation catalog.canonical (by
      intro type member; cases member; exact Ty.variablesBelow_constructor _ _) conditionAccepted
  have conditionWF := (inferExprFuel_direct_progress conditionAccepted).wellFormed
    (show allocated.RequirementsWellFormed by
      rw [allocatedEq]
      change initial.RequirementsWellFormed
      exact wellFormed)
  have after := lifetime.inferStatements conditionProperties.2.1 conditionWF catalog
    (returnBelow.weaken (allocatedProperties.1.trans conditionProperties.1).next_le)
    (lifetime.older _ (returnBelow.weaken allocatedProperties.1.next_le)) bodyAccepted
  have restored := after.restoreScope conditionResult.2.lexicalScope
    (inferStatementsFuel_binders_subset bodyAccepted)
  have recorded := restored.recordUnit id source.span
    (.ifThen conditionResult.1.id bodyResult.statements none)
  have atEntry := recorded.weaken_entry allocatedProperties.1.next_le
  unfold inferStatementFuel at accepted
  simp only [allocation, form, conditionAccepted, bodyAccepted, bind, Except.bind,
    pure, Pure.pure, Except.pure, Except.ok.injEq] at accepted
  cases accepted
  exact atEntry

end GeneralizationLifetime
end Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
