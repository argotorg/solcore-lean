import Solcore.SourceSemantics.SourceInferenceGeneralizationLifetimeStateSteps

/-! Actual non-declaration header completion and ordered header suffixes. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
open Frontend SourceInference TypeSystem Detail
namespace GeneralizationLifetime
variable {whole : TypedSource} {finalSubstitution : Substitution}
    {binder : TypedBinder} {initializer : ExpressionId}
    {event : RetainedGeneralization whole finalSubstitution binder initializer}

theorem forItems_head
    {fuel : Nat} {context : SourceInference.Context} {source : Syntax.ForItem}
    {sources : List Syntax.ForItem} {initial : State}
    {head : ForItemForm × State} {tail result : InferredForItems}
    (ready : initial.InferenceReady) (wellFormed : initial.RequirementsWellFormed)
    (catalog : LifetimeInferenceContext context)
    (headAccepted : inferForItemFuel fuel context source initial = .ok head)
    (tailAccepted : inferForItemsFuel fuel context sources head.2 = .ok tail)
    (accepted : inferForItemsFuel fuel context (source :: sources) initial = .ok result)
    (lifetime : GeneralizationLifetime event initial.inference.next head.2 []) :
    GeneralizationLifetime event initial.inference.next result.state [] := by
  have properties := inferForItemFuel_inferenceProperties ready catalog.formation
    catalog.canonical headAccepted
  have after := lifetime.inferForItems properties.2
    ((inferForItemFuel_direct_progress headAccepted).wellFormed wellFormed) catalog tailAccepted
  have resultEq : ({ items := head.1 :: tail.items, state := tail.state } : InferredForItems) = result := by
    simpa only [inferForItemsFuel, headAccepted, tailAccepted, bind, Except.bind,
      pure, Pure.pure, Except.pure, Except.ok.injEq] using accepted
  cases resultEq
  exact after

theorem forItems_tail
    {fuel : Nat} {context : SourceInference.Context} {source : Syntax.ForItem}
    {sources : List Syntax.ForItem} {initial : State}
    {head : ForItemForm × State} {tail result : InferredForItems}
    (ready : initial.InferenceReady) (catalog : LifetimeInferenceContext context)
    (headAccepted : inferForItemFuel fuel context source initial = .ok head)
    (tailAccepted : inferForItemsFuel fuel context sources head.2 = .ok tail)
    (accepted : inferForItemsFuel fuel context (source :: sources) initial = .ok result)
    (lifetime : GeneralizationLifetime event head.2.inference.next tail.state []) :
    GeneralizationLifetime event initial.inference.next result.state [] := by
  have properties := inferForItemFuel_inferenceProperties ready catalog.formation
    catalog.canonical headAccepted
  have resultEq : ({ items := head.1 :: tail.items, state := tail.state } : InferredForItems) = result := by
    simpa only [inferForItemsFuel, headAccepted, tailAccepted, bind, Except.bind,
      pure, Pure.pure, Except.pure, Except.ok.injEq] using accepted
  cases resultEq
  exact lifetime.weaken_entry properties.1.next_le

theorem forItem_expression
    {fuel : Nat} {context : SourceInference.Context} {source : Syntax.ForItem}
    {expression : Syntax.Expr} {initial : State}
    {child : InferredExpression × State} {result : ForItemForm × State}
    (form : source.value = .expression expression)
    (childAccepted : inferExprFuel fuel context expression none initial = .ok child)
    (accepted : inferForItemFuel (fuel + 1) context source initial = .ok result)
    (lifetime : GeneralizationLifetime event initial.inference.next child.2 [child.1.type]) :
    GeneralizationLifetime event initial.inference.next result.2 [] := by
  have resultEq : (.expression child.1.id, child.2) = result := by
    simpa only [inferForItemFuel, form, childAccepted, bind, Except.bind,
      pure, Pure.pure, Except.pure, Except.ok.injEq] using accepted
  cases resultEq
  exact lifetime.restrict_outputs (by simp)

theorem forItem_assignment
    {fuel : Nat} {context : SourceInference.Context} {source : Syntax.ForItem}
    {target value : Syntax.Expr} {operator : Syntax.Located Syntax.ValueAssignOp}
    {initial : State} {child : AssignmentResolution × InferredExpression × State}
    {result : ForItemForm × State}
    (form : source.value = .assignValue target operator value)
    (childAccepted : inferAssignedValueFuel fuel context target operator.value value initial = .ok child)
    (accepted : inferForItemFuel (fuel + 1) context source initial = .ok result)
    (lifetime : GeneralizationLifetime event initial.inference.next child.2.2
      [child.1.target.type, child.2.1.type]) :
    GeneralizationLifetime event initial.inference.next result.2 [] := by
  have resultEq : (.assignValue child.1 operator.value child.2.1.id, child.2.2) = result := by
    simpa only [inferForItemFuel, form, childAccepted, bind, Except.bind,
      pure, Pure.pure, Except.pure, Except.ok.injEq] using accepted
  cases resultEq
  exact lifetime.restrict_outputs (by simp)

theorem forItem_bitnot
    {fuel : Nat} {context : SourceInference.Context} {source : Syntax.ForItem}
    {target : Syntax.Expr} {operator : Syntax.SourceSpan} {initial fitted : State}
    {child : PlaceResolution × State} {result : ForItemForm × State}
    (ready : initial.InferenceReady) (catalog : LifetimeInferenceContext context)
    (form : source.value = .assignBitNot target operator)
    (childAccepted : inferPlaceFuel fuel context target initial = .ok child)
    (fitting : Detail.unify child.2 child.1.type .word = .ok fitted)
    (accepted : inferForItemFuel (fuel + 1) context source initial = .ok result)
    (lifetime : GeneralizationLifetime event initial.inference.next child.2 [child.1.type]) :
    GeneralizationLifetime event initial.inference.next result.2 [] := by
  have properties := inferPlaceFuel_inferenceProperties ready catalog.formation catalog.canonical childAccepted
  have after := lifetime.unify properties.2.1 properties.2.2
    (Ty.variablesBelow_constructor _ _) (lifetime.values _ (List.mem_singleton_self _))
    (safe_closed _ _ (Ty.variablesBelow_constructor 0 _)) fitting
  have resultEq :
      (.assignBitNot { target := { child.1 with type := fitted.resolve child.1.type } }, fitted) = result := by
    simpa only [inferForItemFuel, form, childAccepted, fitting, bind, Except.bind,
      pure, Pure.pure, Except.pure, Except.ok.injEq] using accepted
  cases resultEq
  exact after.restrict_outputs (by simp)

end GeneralizationLifetime
end Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
