import Solcore.SourceSemantics.SourceInferenceGeneralizationLifetimeArgumentContinuation

/-! Constructor arguments preserve their actual left-to-right call order. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
open Frontend SourceInference TypeSystem Detail
namespace GeneralizationLifetime
variable {whole : TypedSource} {finalSubstitution : Substitution}
    {binder : TypedBinder} {initializer : ExpressionId}
    {event : RetainedGeneralization whole finalSubstitution binder initializer}

theorem constructorArguments_head
    {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Expr}
    {sources : List Syntax.Expr} {expected : Ty} {expectedTypes : List Ty} {initial : State}
    {head : InferredExpression × State} {tail result : List InferredExpression × State}
    (ready : initial.InferenceReady) (wellFormed : initial.RequirementsWellFormed)
    (catalog : LifetimeInferenceContext context)
    (expectedBelow : ∀ type ∈ expected :: expectedTypes, type.VariablesBelow initial.inference.next)
    (headAccepted : inferExprFuel fuel context source (some (initial.resolve expected)) initial = .ok head)
    (tailAccepted : inferConstructorArgumentsFuel fuel context sources expectedTypes head.2 = .ok tail)
    (accepted : inferConstructorArgumentsFuel fuel context (source :: sources) (expected :: expectedTypes) initial = .ok result)
    (lifetime : GeneralizationLifetime event initial.inference.next head.2 [head.1.type]) :
    GeneralizationLifetime event initial.inference.next result.2 (result.1.map (·.type)) := by
  have headProperties := inferExprFuel_inferenceProperties ready catalog.formation catalog.canonical
    (by intro type member; cases member; exact ready.solved.variablesBelow_apply (expectedBelow _ (by simp))) headAccepted
  have after := lifetime.inferConstructorArguments headProperties.2.1
    ((inferExprFuel_direct_progress headAccepted).wellFormed wellFormed) catalog
    (fun type member => (expectedBelow type (List.mem_cons_of_mem _ member)).weaken headProperties.1.next_le)
    (fun type member => lifetime.older type (expectedBelow type (List.mem_cons_of_mem _ member))) tailAccepted
  have resultEq : (head.1 :: tail.1, tail.2) = result := by
    simpa only [inferConstructorArgumentsFuel, headAccepted, tailAccepted, bind, Except.bind,
      pure, Pure.pure, Except.pure, Except.ok.injEq] using accepted
  cases resultEq
  simpa only [List.map_cons, List.singleton_append] using after

theorem constructorArguments_tail
    {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Expr}
    {sources : List Syntax.Expr} {expected : Ty} {expectedTypes : List Ty} {initial : State}
    {head : InferredExpression × State} {tail result : List InferredExpression × State}
    (ready : initial.InferenceReady) (catalog : LifetimeInferenceContext context)
    (expectedBelow : ∀ type ∈ expected :: expectedTypes, type.VariablesBelow initial.inference.next)
    (headAccepted : inferExprFuel fuel context source (some (initial.resolve expected)) initial = .ok head)
    (tailAccepted : inferConstructorArgumentsFuel fuel context sources expectedTypes head.2 = .ok tail)
    (accepted : inferConstructorArgumentsFuel fuel context (source :: sources) (expected :: expectedTypes) initial = .ok result)
    (lifetime : GeneralizationLifetime event head.2.inference.next tail.2 (tail.1.map (·.type))) :
    GeneralizationLifetime event initial.inference.next result.2 (result.1.map (·.type)) := by
  have headProperties := inferExprFuel_inferenceProperties ready catalog.formation catalog.canonical
    (by intro type member; cases member; exact ready.solved.variablesBelow_apply (expectedBelow _ (by simp))) headAccepted
  have resultEq : (head.1 :: tail.1, tail.2) = result := by
    simpa only [inferConstructorArgumentsFuel, headAccepted, tailAccepted, bind, Except.bind,
      pure, Pure.pure, Except.pure, Except.ok.injEq] using accepted
  cases resultEq
  have tailLifetime := lifetime.weaken_entry headProperties.1.next_le
  refine {tailLifetime with values := ?_}
  intro type member
  rcases List.mem_cons.mp member with rfl | member
  · exact lifetime.older _ headProperties.2.2
  · exact lifetime.values _ member

theorem constructorApplication_arguments
    {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Expr} {id : ExpressionId}
    {instantiation : DataConstructorInstantiation} {arguments : List Syntax.Expr} {expected : Option Ty}
    {initial fitted : State} {child : List InferredExpression × State} {result : InferredExpression × State}
    (ready : initial.InferenceReady) (catalog : LifetimeInferenceContext context)
    (payloadBelow : ∀ type ∈ instantiation.payloadTypes, type.VariablesBelow initial.inference.next)
    (resultBelow : instantiation.resultType.VariablesBelow initial.inference.next)
    (expectedBelow : ∀ type ∈ expected, type.VariablesBelow initial.inference.next)
    (fitting : (match expected with
      | none => Except.ok initial
      | some type => Detail.unify initial instantiation.resultType type) = .ok fitted)
    (childAccepted : inferConstructorArgumentsFuel fuel context arguments instantiation.payloadTypes fitted = .ok child)
    (accepted : inferConstructorApplicationFuel fuel context source id instantiation arguments expected initial = .ok result)
    (lifetime : GeneralizationLifetime event fitted.inference.next child.2 (child.1.map (·.type))) :
    GeneralizationLifetime event initial.inference.next result.2 [result.1.type] := by
  have fittingProperties : initial.InferenceProgress fitted ∧ fitted.InferenceReady := by
    cases expected with
    | none =>
        simp only [Except.ok.injEq] at fitting
        cases fitting
        exact ⟨.refl ready.solved, ready⟩
    | some type =>
        exact ⟨unify_inferenceProgress ready.solved resultBelow (expectedBelow _ (by simp)) fitting,
          unify_preserves_inferenceReady ready resultBelow (expectedBelow _ (by simp)) fitting⟩
  have childProperties := inferConstructorArgumentsFuel_inferenceProperties fittingProperties.2
    catalog.formation catalog.canonical
    (fun type member => (payloadBelow type member).weaken fittingProperties.1.next_le) childAccepted
  have recorded : recordExpressionWithExpected context source id
      (child.2.resolve instantiation.resultType) (.constructor instantiation (child.1.map (·.id))) [] expected child.2 = .ok result := by
    unfold inferConstructorApplicationFuel at accepted
    by_cases arity : arguments.length = instantiation.payloadTypes.length
    · cases expected with
      | none =>
          simp only [Except.ok.injEq] at fitting
          cases fitting
          simpa [arity, childAccepted, bind, Except.bind, pure, Pure.pure, Except.pure] using accepted
      | some type =>
          simpa [arity, fitting, childAccepted, bind, Except.bind] using accepted
    · simp [arity, bind, Except.bind] at accepted
  have after := lifetime.recordExpression catalog.catalog childProperties.2.1
    (childProperties.2.1.solved.variablesBelow_apply
      (resultBelow.weaken (fittingProperties.1.trans childProperties.1).next_le))
    (fun type member => (expectedBelow type member).weaken (fittingProperties.1.trans childProperties.1).next_le)
    (safe_resolved childProperties.2.1 (lifetime.older _ (resultBelow.weaken fittingProperties.1.next_le)))
    (fun type member => lifetime.older _ ((expectedBelow type member).weaken fittingProperties.1.next_le)) recorded
  exact (after.restrict_outputs (by intro type member; exact List.mem_append_right _ member)).weaken_entry
    fittingProperties.1.next_le

end GeneralizationLifetime
end Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
