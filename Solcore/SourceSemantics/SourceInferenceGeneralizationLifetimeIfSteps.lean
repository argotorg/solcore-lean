import Solcore.SourceSemantics.SourceInferenceGeneralizationLifetimeBranchSteps

/-! The two actual branches are sequenced through their real saved scope. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
open Frontend SourceInference TypeSystem Detail
namespace GeneralizationLifetime
variable {whole : TypedSource} {finalSubstitution : Substitution}
    {binder : TypedBinder} {initializer : ExpressionId}
    {event : RetainedGeneralization whole finalSubstitution binder initializer}

private theorem finishIf
    {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Statement}
    {condition : Syntax.Expr} {thenBody elseBody : Syntax.Block} {expectedReturn : Ty}
    {initial allocated : State} {id : StatementId}
    {conditionResult : InferredExpression × State} {thenResult elseResult : BlockResult}
    {result : StatementResult} {entryNext : Nat} {outputs : List Ty}
    (form : source.value = .ifThen condition thenBody (some elseBody))
    (allocation : initial.allocateStatementId = (id, allocated))
    (conditionAccepted : inferExprFuel fuel context condition (some .bool) allocated = .ok conditionResult)
    (thenAccepted : inferStatementsFuel fuel context thenBody.value expectedReturn conditionResult.2 = .ok thenResult)
    (elseAccepted : inferStatementsFuel fuel context elseBody.value expectedReturn
      (thenResult.state.restoreLexicalScope conditionResult.2.lexicalScope) = .ok elseResult)
    (accepted : inferStatementFuel (fuel + 1) context source expectedReturn initial = .ok result)
    (lifetime : GeneralizationLifetime event entryNext elseResult.state outputs)
    (returnSafe : Safe binder.scheme.quantified elseResult.state (elseResult.state.resolve expectedReturn)) :
    GeneralizationLifetime event entryNext result.state [result.type] := by
  have savedSubset : conditionResult.2.localBinders ⊆ elseResult.state.localBinders :=
    by simpa only [State.restoreLexicalScope, State.lexicalScope] using
      (inferStatementsFuel_binders_subset elseAccepted)
  have restored := lifetime.restoreScope conditionResult.2.lexicalScope savedSubset
  let type := if thenResult.sawReturn && elseResult.sawReturn then
    elseResult.state.resolve expectedReturn else .unit
  have recorded := restored.recordNode (.statement {
    id, span := source.span, type := type,
    form := .ifThen conditionResult.1.id thenResult.statements (some elseResult.statements)})
  have resultSafe : Safe binder.scheme.quantified
      ((elseResult.state.restoreLexicalScope conditionResult.2.lexicalScope).recordNode
        (.statement {
          id, span := source.span, type := type,
          form := .ifThen conditionResult.1.id thenResult.statements (some elseResult.statements)})) type := by
    dsimp only [type]
    split
    · exact returnSafe
    · exact safe_closed _ _ (Ty.variablesBelow_constructor 0 _)
  have final := recorded.replaceOutputs (by
    intro ty member
    cases List.mem_singleton.mp member
    exact resultSafe)
  unfold inferStatementFuel at accepted
  simp only [allocation, form, conditionAccepted, thenAccepted, elseAccepted,
    bind, Except.bind, pure, Pure.pure, Except.pure, Except.ok.injEq] at accepted
  cases accepted
  exact final

private theorem prefixProperties
    {fuel : Nat} {context : SourceInference.Context}
    {condition : Syntax.Expr} {thenBody : Syntax.Block} {expectedReturn : Ty}
    {initial allocated : State} {id : StatementId}
    {conditionResult : InferredExpression × State} {thenResult : BlockResult}
    (ready : initial.InferenceReady) (catalog : LifetimeInferenceContext context)
    (returnBelow : expectedReturn.VariablesBelow initial.inference.next)
    (allocation : initial.allocateStatementId = (id, allocated))
    (conditionAccepted : inferExprFuel fuel context condition (some .bool) allocated = .ok conditionResult)
    (thenAccepted : inferStatementsFuel fuel context thenBody.value expectedReturn conditionResult.2 = .ok thenResult) :
    initial.InferenceProgress conditionResult.2 ∧ conditionResult.2.InferenceReady ∧
      conditionResult.2.InferenceProgress (thenResult.state.restoreLexicalScope conditionResult.2.lexicalScope) ∧
      (thenResult.state.restoreLexicalScope conditionResult.2.lexicalScope).InferenceReady := by
  have allocationProgress := State.InferenceProgress.allocateStatementId initial ready.solved
  have allocationReady := ready.allocateStatementId
  rw [allocation] at allocationProgress allocationReady
  have conditionProperties := inferExprFuel_inferenceProperties allocationReady
    catalog.formation catalog.canonical (by
      intro ty member; cases member; exact Ty.variablesBelow_constructor _ _) conditionAccepted
  have before := allocationProgress.trans conditionProperties.1
  have thenProperties := inferStatementsFuel_inferenceProperties conditionProperties.2.1
    catalog.formation catalog.canonical (returnBelow.weaken before.next_le) thenAccepted
  have restored := State.restoreLexicalScope_inferenceProperties conditionProperties.2.1 thenProperties.1
  exact ⟨before, conditionProperties.2.1, restored.1, restored.2⟩

theorem if_with_else_else
    {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Statement}
    {condition : Syntax.Expr} {thenBody elseBody : Syntax.Block} {expectedReturn : Ty}
    {initial allocated : State} {id : StatementId}
    {conditionResult : InferredExpression × State} {thenResult elseResult : BlockResult}
    {result : StatementResult}
    (ready : initial.InferenceReady) (catalog : LifetimeInferenceContext context)
    (returnBelow : expectedReturn.VariablesBelow initial.inference.next)
    (form : source.value = .ifThen condition thenBody (some elseBody))
    (allocation : initial.allocateStatementId = (id, allocated))
    (conditionAccepted : inferExprFuel fuel context condition (some .bool) allocated = .ok conditionResult)
    (thenAccepted : inferStatementsFuel fuel context thenBody.value expectedReturn conditionResult.2 = .ok thenResult)
    (elseAccepted : inferStatementsFuel fuel context elseBody.value expectedReturn
      (thenResult.state.restoreLexicalScope conditionResult.2.lexicalScope) = .ok elseResult)
    (accepted : inferStatementFuel (fuel + 1) context source expectedReturn initial = .ok result)
    (lifetime : GeneralizationLifetime event thenResult.state.inference.next elseResult.state [elseResult.type]) :
    GeneralizationLifetime event initial.inference.next result.state [result.type] := by
  have beforeProperties := prefixProperties ready catalog returnBelow allocation conditionAccepted thenAccepted
  have throughThen := beforeProperties.1.trans beforeProperties.2.2.1
  have elseProperties := inferStatementsFuel_inferenceProperties beforeProperties.2.2.2
    catalog.formation catalog.canonical (returnBelow.weaken throughThen.next_le) elseAccepted
  have safe := safe_resolved elseProperties.2.1
    (lifetime.older _ (returnBelow.weaken throughThen.next_le))
  exact (finishIf form allocation conditionAccepted thenAccepted elseAccepted accepted lifetime safe).weaken_entry
    throughThen.next_le

theorem if_with_else_then
    {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Statement}
    {condition : Syntax.Expr} {thenBody elseBody : Syntax.Block} {expectedReturn : Ty}
    {initial allocated : State} {id : StatementId}
    {conditionResult : InferredExpression × State} {thenResult elseResult : BlockResult}
    {result : StatementResult}
    (ready : initial.InferenceReady) (wellFormed : initial.RequirementsWellFormed)
    (catalog : LifetimeInferenceContext context)
    (returnBelow : expectedReturn.VariablesBelow initial.inference.next)
    (form : source.value = .ifThen condition thenBody (some elseBody))
    (allocation : initial.allocateStatementId = (id, allocated))
    (conditionAccepted : inferExprFuel fuel context condition (some .bool) allocated = .ok conditionResult)
    (thenAccepted : inferStatementsFuel fuel context thenBody.value expectedReturn conditionResult.2 = .ok thenResult)
    (elseAccepted : inferStatementsFuel fuel context elseBody.value expectedReturn
      (thenResult.state.restoreLexicalScope conditionResult.2.lexicalScope) = .ok elseResult)
    (accepted : inferStatementFuel (fuel + 1) context source expectedReturn initial = .ok result)
    (lifetime : GeneralizationLifetime event conditionResult.2.inference.next thenResult.state [thenResult.type]) :
    GeneralizationLifetime event initial.inference.next result.state [result.type] := by
  have beforeProperties := prefixProperties ready catalog returnBelow allocation conditionAccepted thenAccepted
  have allocatedEq : allocated = initial.allocateStatementId.2 := (congrArg Prod.snd allocation).symm
  have allocatedWF : allocated.RequirementsWellFormed := by
    rw [allocatedEq]; change initial.RequirementsWellFormed; exact wellFormed
  have conditionWF := (inferExprFuel_direct_progress conditionAccepted).wellFormed allocatedWF
  have thenWF := (inferStatementsFuel_direct_progress thenAccepted).wellFormed conditionWF
  have restored := lifetime.restoreScope conditionResult.2.lexicalScope
    (inferStatementsFuel_binders_subset thenAccepted)
  have after := restored.inferStatements beforeProperties.2.2.2 thenWF catalog
    (returnBelow.weaken (beforeProperties.1.trans beforeProperties.2.2.1).next_le)
    (restored.older _ (returnBelow.weaken beforeProperties.1.next_le)) elseAccepted
  have elseProperties := inferStatementsFuel_inferenceProperties beforeProperties.2.2.2
    catalog.formation catalog.canonical
    (returnBelow.weaken (beforeProperties.1.trans beforeProperties.2.2.1).next_le) elseAccepted
  have safe := safe_resolved elseProperties.2.1
    (after.older _ (returnBelow.weaken beforeProperties.1.next_le))
  exact (finishIf form allocation conditionAccepted thenAccepted elseAccepted accepted after safe).weaken_entry
    beforeProperties.1.next_le

theorem if_with_else_condition
    {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Statement}
    {condition : Syntax.Expr} {thenBody elseBody : Syntax.Block} {expectedReturn : Ty}
    {initial allocated : State} {id : StatementId}
    {conditionResult : InferredExpression × State} {thenResult elseResult : BlockResult}
    {result : StatementResult}
    (ready : initial.InferenceReady) (wellFormed : initial.RequirementsWellFormed)
    (catalog : LifetimeInferenceContext context)
    (returnBelow : expectedReturn.VariablesBelow initial.inference.next)
    (form : source.value = .ifThen condition thenBody (some elseBody))
    (allocation : initial.allocateStatementId = (id, allocated))
    (conditionAccepted : inferExprFuel fuel context condition (some .bool) allocated = .ok conditionResult)
    (thenAccepted : inferStatementsFuel fuel context thenBody.value expectedReturn conditionResult.2 = .ok thenResult)
    (elseAccepted : inferStatementsFuel fuel context elseBody.value expectedReturn
      (thenResult.state.restoreLexicalScope conditionResult.2.lexicalScope) = .ok elseResult)
    (accepted : inferStatementFuel (fuel + 1) context source expectedReturn initial = .ok result)
    (lifetime : GeneralizationLifetime event allocated.inference.next conditionResult.2 [conditionResult.1.type]) :
    GeneralizationLifetime event initial.inference.next result.state [result.type] := by
  have beforeProperties := prefixProperties ready catalog returnBelow allocation conditionAccepted thenAccepted
  have allocatedEq : allocated = initial.allocateStatementId.2 := (congrArg Prod.snd allocation).symm
  have sameNext : allocated.inference.next = initial.inference.next := by rw [allocatedEq]; rfl
  have allocatedWF : allocated.RequirementsWellFormed := by
    rw [allocatedEq]; change initial.RequirementsWellFormed; exact wellFormed
  have conditionWF := (inferExprFuel_direct_progress conditionAccepted).wellFormed allocatedWF
  have thenWF := (inferStatementsFuel_direct_progress thenAccepted).wellFormed conditionWF
  have afterThen := lifetime.inferStatements beforeProperties.2.1 conditionWF catalog
    (returnBelow.weaken beforeProperties.1.next_le) (lifetime.older _ (sameNext ▸ returnBelow)) thenAccepted
  have restored := afterThen.restoreScope conditionResult.2.lexicalScope
    (inferStatementsFuel_binders_subset thenAccepted)
  have after := restored.inferStatements beforeProperties.2.2.2 thenWF catalog
    (returnBelow.weaken (beforeProperties.1.trans beforeProperties.2.2.1).next_le)
    (restored.older _ (sameNext ▸ returnBelow)) elseAccepted
  have elseProperties := inferStatementsFuel_inferenceProperties beforeProperties.2.2.2
    catalog.formation catalog.canonical
    (returnBelow.weaken (beforeProperties.1.trans beforeProperties.2.2.1).next_le) elseAccepted
  have safe := safe_resolved elseProperties.2.1 (after.older _ (sameNext ▸ returnBelow))
  have resultLifetime := finishIf form allocation conditionAccepted thenAccepted elseAccepted accepted after safe
  rw [sameNext] at resultLifetime
  exact resultLifetime

end GeneralizationLifetime
end Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
