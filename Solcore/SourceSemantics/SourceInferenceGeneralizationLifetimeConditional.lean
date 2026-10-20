import Solcore.SourceSemantics.SourceInferenceGeneralizationLifetimeStateSteps

/-! Each conditional child is followed by the original remaining calls and unifier. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
open Frontend SourceInference TypeSystem Detail
namespace GeneralizationLifetime
variable {whole : TypedSource} {finalSubstitution : Substitution}
    {binder : TypedBinder} {initializer : ExpressionId}
    {event : RetainedGeneralization whole finalSubstitution binder initializer}
    {fuel : Nat} {context : SourceInference.Context} {source condition thenBranch elseBranch : Syntax.Expr}
    {question colon : Syntax.SourceSpan} {expected : Option Ty} {initial allocated : State} {id : ExpressionId}
    {conditionResult thenResult elseResult final : InferredExpression × State}

private theorem finishConditional
    {entryNext : Nat}
    (ready : elseResult.2.InferenceReady) (catalog : LifetimeInferenceContext context)
    (thenBelow : thenResult.1.type.VariablesBelow elseResult.2.inference.next)
    (elseBelow : elseResult.1.type.VariablesBelow elseResult.2.inference.next)
    (expectedBelow : ∀ type ∈ expected, type.VariablesBelow elseResult.2.inference.next)
    (expectedBefore : ∀ type ∈ expected, type.VariablesBelow entryNext)
    (form : source.value = .conditional condition question thenBranch colon elseBranch)
    (allocation : initial.allocateExpressionId = (id, allocated))
    (conditionAccepted : inferExprFuel fuel context condition (some .bool) allocated = .ok conditionResult)
    (thenAccepted : inferExprFuel fuel context thenBranch expected conditionResult.2 = .ok thenResult)
    (elseAccepted : inferExprFuel fuel context elseBranch expected thenResult.2 = .ok elseResult)
    (accepted : inferExprFuel (fuel + 1) context source expected initial = .ok final)
    (lifetime : GeneralizationLifetime event entryNext elseResult.2 [thenResult.1.type, elseResult.1.type]) :
    GeneralizationLifetime event entryNext final.2 [final.1.type] := by
  unfold inferExprFuel at accepted
  simp only [allocation, form, conditionAccepted, thenAccepted, elseAccepted, bind, Except.bind] at accepted
  cases fitting : Detail.unify elseResult.2 thenResult.1.type elseResult.1.type with
  | error error => simp [fitting] at accepted
  | ok fitted =>
      have properties := unify_inferenceProgress ready.solved thenBelow elseBelow fitting
      have fittedReady := unify_preserves_inferenceReady ready thenBelow elseBelow fitting
      have after := lifetime.unify ready thenBelow elseBelow
        (lifetime.values _ (by simp)) (lifetime.values _ (by simp)) fitting
      have recorded : recordExpressionWithExpected context source id
          (fitted.resolve thenResult.1.type)
          (.conditional conditionResult.1.id thenResult.1.id elseResult.1.id) [] expected fitted = .ok final := by
        simpa only [fitting] using accepted
      have done := after.recordExpression catalog.catalog fittedReady
        (fittedReady.solved.variablesBelow_apply (thenBelow.weaken properties.next_le))
        (fun type member => (expectedBelow type member).weaken properties.next_le)
        (safe_resolved fittedReady (after.values _ (by simp)))
        (fun type member => after.older type (expectedBefore type member)) recorded
      exact done.restrict_outputs (by intro type member; exact List.mem_append_right _ member)

private theorem conditionalPrefix
    (ready : initial.InferenceReady) (catalog : LifetimeInferenceContext context)
    (expectedBelow : ∀ type ∈ expected, type.VariablesBelow initial.inference.next)
    (allocation : initial.allocateExpressionId = (id, allocated))
    (conditionAccepted : inferExprFuel fuel context condition (some .bool) allocated = .ok conditionResult)
    (thenAccepted : inferExprFuel fuel context thenBranch expected conditionResult.2 = .ok thenResult)
    (elseAccepted : inferExprFuel fuel context elseBranch expected thenResult.2 = .ok elseResult) :
    initial.InferenceProgress conditionResult.2 ∧ conditionResult.2.InferenceReady ∧
    conditionResult.2.InferenceProgress thenResult.2 ∧ thenResult.2.InferenceReady ∧
    thenResult.1.type.VariablesBelow thenResult.2.inference.next ∧
    thenResult.2.InferenceProgress elseResult.2 ∧ elseResult.2.InferenceReady ∧
    elseResult.1.type.VariablesBelow elseResult.2.inference.next := by
  have allocatedProgress := State.InferenceProgress.allocateExpressionId initial ready.solved
  have allocatedReady := ready.allocateExpressionId
  rw [allocation] at allocatedProgress allocatedReady
  have c := inferExprFuel_inferenceProperties allocatedReady catalog.formation catalog.canonical
    (by intro type member; cases member; exact Ty.variablesBelow_constructor _ _) conditionAccepted
  have first := allocatedProgress.trans c.1
  have t := inferExprFuel_inferenceProperties c.2.1 catalog.formation catalog.canonical
    (fun type member => (expectedBelow type member).weaken first.next_le) thenAccepted
  have e := inferExprFuel_inferenceProperties t.2.1 catalog.formation catalog.canonical
    (fun type member => (expectedBelow type member).weaken (first.trans t.1).next_le) elseAccepted
  exact ⟨first, c.2.1, t.1, t.2.1, t.2.2, e.1, e.2.1, e.2.2⟩

theorem conditional_else
    (ready : initial.InferenceReady) (catalog : LifetimeInferenceContext context)
    (expectedBelow : ∀ type ∈ expected, type.VariablesBelow initial.inference.next)
    (form : source.value = .conditional condition question thenBranch colon elseBranch)
    (allocation : initial.allocateExpressionId = (id, allocated))
    (conditionAccepted : inferExprFuel fuel context condition (some .bool) allocated = .ok conditionResult)
    (thenAccepted : inferExprFuel fuel context thenBranch expected conditionResult.2 = .ok thenResult)
    (elseAccepted : inferExprFuel fuel context elseBranch expected thenResult.2 = .ok elseResult)
    (accepted : inferExprFuel (fuel + 1) context source expected initial = .ok final)
    (lifetime : GeneralizationLifetime event thenResult.2.inference.next elseResult.2 [elseResult.1.type]) :
    GeneralizationLifetime event initial.inference.next final.2 [final.1.type] := by
  obtain ⟨throughCondition, _, throughThen, _, thenBelow, throughElse, elseReady, elseBelow⟩ :=
    conditionalPrefix ready catalog expectedBelow allocation conditionAccepted thenAccepted elseAccepted
  have both := lifetime.replaceOutputs (values := [thenResult.1.type, elseResult.1.type]) (by
    intro type member
    rcases List.mem_cons.mp member with rfl | member
    · exact lifetime.older _ thenBelow
    · exact lifetime.values _ member)
  have result := finishConditional elseReady catalog (thenBelow.weaken throughElse.next_le) elseBelow
    (fun type member => (expectedBelow type member).weaken ((throughCondition.trans throughThen).trans throughElse).next_le)
    (fun type member => (expectedBelow type member).weaken (throughCondition.trans throughThen).next_le)
    form allocation conditionAccepted thenAccepted elseAccepted accepted both
  exact result.weaken_entry (throughCondition.trans throughThen).next_le

theorem conditional_then
    (ready : initial.InferenceReady) (wellFormed : initial.RequirementsWellFormed)
    (catalog : LifetimeInferenceContext context)
    (expectedBelow : ∀ type ∈ expected, type.VariablesBelow initial.inference.next)
    (form : source.value = .conditional condition question thenBranch colon elseBranch)
    (allocation : initial.allocateExpressionId = (id, allocated))
    (conditionAccepted : inferExprFuel fuel context condition (some .bool) allocated = .ok conditionResult)
    (thenAccepted : inferExprFuel fuel context thenBranch expected conditionResult.2 = .ok thenResult)
    (elseAccepted : inferExprFuel fuel context elseBranch expected thenResult.2 = .ok elseResult)
    (accepted : inferExprFuel (fuel + 1) context source expected initial = .ok final)
    (lifetime : GeneralizationLifetime event conditionResult.2.inference.next thenResult.2 [thenResult.1.type]) :
    GeneralizationLifetime event initial.inference.next final.2 [final.1.type] := by
  obtain ⟨throughCondition, _, throughThen, thenReady, thenBelow, throughElse, elseReady, elseBelow⟩ :=
    conditionalPrefix ready catalog expectedBelow allocation conditionAccepted thenAccepted elseAccepted
  have allocatedEq : allocated = initial.allocateExpressionId.2 := (congrArg Prod.snd allocation).symm
  have allocatedWF : allocated.RequirementsWellFormed := by rw [allocatedEq]; exact wellFormed
  have thenWF := (inferExprFuel_direct_progress thenAccepted).wellFormed
    ((inferExprFuel_direct_progress conditionAccepted).wellFormed allocatedWF)
  have after := lifetime.inferExpr thenReady thenWF catalog
    (fun type member => (expectedBelow type member).weaken (throughCondition.trans throughThen).next_le)
    (fun type member => lifetime.older _ ((expectedBelow type member).weaken throughCondition.next_le)) elseAccepted
  have result := finishConditional elseReady catalog (thenBelow.weaken throughElse.next_le) elseBelow
    (fun type member => (expectedBelow type member).weaken ((throughCondition.trans throughThen).trans throughElse).next_le)
    (fun type member => (expectedBelow type member).weaken throughCondition.next_le)
    form allocation conditionAccepted thenAccepted elseAccepted accepted after
  exact result.weaken_entry throughCondition.next_le

theorem conditional_condition
    (ready : initial.InferenceReady) (wellFormed : initial.RequirementsWellFormed)
    (catalog : LifetimeInferenceContext context)
    (expectedBelow : ∀ type ∈ expected, type.VariablesBelow initial.inference.next)
    (form : source.value = .conditional condition question thenBranch colon elseBranch)
    (allocation : initial.allocateExpressionId = (id, allocated))
    (conditionAccepted : inferExprFuel fuel context condition (some .bool) allocated = .ok conditionResult)
    (thenAccepted : inferExprFuel fuel context thenBranch expected conditionResult.2 = .ok thenResult)
    (elseAccepted : inferExprFuel fuel context elseBranch expected thenResult.2 = .ok elseResult)
    (accepted : inferExprFuel (fuel + 1) context source expected initial = .ok final)
    (lifetime : GeneralizationLifetime event allocated.inference.next conditionResult.2 [conditionResult.1.type]) :
    GeneralizationLifetime event initial.inference.next final.2 [final.1.type] := by
  obtain ⟨throughCondition, conditionReady, throughThen, thenReady, thenBelow, throughElse, elseReady, elseBelow⟩ :=
    conditionalPrefix ready catalog expectedBelow allocation conditionAccepted thenAccepted elseAccepted
  have allocatedEq : allocated = initial.allocateExpressionId.2 := (congrArg Prod.snd allocation).symm
  have sameNext : allocated.inference.next = initial.inference.next := by rw [allocatedEq]; rfl
  have allocatedWF : allocated.RequirementsWellFormed := by rw [allocatedEq]; exact wellFormed
  have conditionWF := (inferExprFuel_direct_progress conditionAccepted).wellFormed allocatedWF
  have thenWF := (inferExprFuel_direct_progress thenAccepted).wellFormed conditionWF
  have afterThen := lifetime.inferExpr conditionReady conditionWF catalog
    (fun type member => (expectedBelow type member).weaken throughCondition.next_le)
    (fun type member => lifetime.older _ (sameNext ▸ expectedBelow type member)) thenAccepted
  have afterElse := afterThen.inferExpr thenReady thenWF catalog
    (fun type member => (expectedBelow type member).weaken (throughCondition.trans throughThen).next_le)
    (fun type member => afterThen.older _ (sameNext ▸ expectedBelow type member)) elseAccepted
  have both := afterElse.restrict_outputs (selected := [thenResult.1.type, elseResult.1.type]) (by simp)
  have result := finishConditional elseReady catalog (thenBelow.weaken throughElse.next_le) elseBelow
    (fun type member => (expectedBelow type member).weaken ((throughCondition.trans throughThen).trans throughElse).next_le)
    (fun type member => sameNext ▸ expectedBelow type member)
    form allocation conditionAccepted thenAccepted elseAccepted accepted both
  simpa only [sameNext] using result

end GeneralizationLifetime
end Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
