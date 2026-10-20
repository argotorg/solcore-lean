import Solcore.SourceSemantics.SourceInferenceGeneralizationLifetimeContinuation
import Solcore.SourceSemantics.SourceInferenceActualCallGraph

/-! Lift a newly created event through real expression and list continuations.
These steps use accepted child and parent computations; the privacy of an
arbitrary continuation is never an input. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
open Frontend SourceInference TypeSystem Detail

namespace GeneralizationLifetime
variable {whole : TypedSource} {finalSubstitution : Substitution}
    {binder : TypedBinder} {initializer : ExpressionId}
    {event : RetainedGeneralization whole finalSubstitution binder initializer}

theorem recordExpression
    {entryNext : Nat} {state : State} {outputs : List Ty}
    (lifetime : GeneralizationLifetime event entryNext state outputs)
    {context : SourceInference.Context} {source : Syntax.Expr} {id : ExpressionId}
    {type : Ty} {form : ExpressionForm} {requirements : List RequirementId}
    {expected : Option Ty} {start : Option Nat} {result : InferredExpression × State}
    (catalog : SignatureCatalogWellFormed context.signatures)
    (ready : state.InferenceReady)
    (typeBelow : type.VariablesBelow state.inference.next)
    (expectedBelow : ∀ type ∈ expected, type.VariablesBelow state.inference.next)
    (typeSafe : Safe binder.scheme.quantified state type)
    (expectedSafe : ∀ type ∈ expected, Safe binder.scheme.quantified state type)
    (accepted : recordExpressionWithExpected context source id type form requirements
      expected state start = .ok result) :
    GeneralizationLifetime event entryNext result.2 (outputs ++ [result.1.type]) := by
  have privacy := recordExpressionWithExpected_private catalog ready typeBelow
    expectedBelow typeSafe expectedSafe lifetime.live accepted
  have properties := recordExpressionWithExpected_inferenceProperties ready typeBelow
    expectedBelow accepted
  exact lifetime.append properties.1.next_le privacy.1 privacy.2.2.1
    (fun type member => (List.mem_singleton.mp member) ▸ privacy.2.1) privacy.2.2.2

theorem group
    {fuel : Nat} {context : SourceInference.Context}
    {source inner : Syntax.Expr} {expected : Option Ty} {initial allocated : State}
    {id : ExpressionId} {child final : InferredExpression × State}
    (ready : initial.InferenceReady) (catalog : LifetimeInferenceContext context)
    (expectedBelow : ∀ type ∈ expected, type.VariablesBelow initial.inference.next)
    (form : source.value = .group inner)
    (allocation : initial.allocateExpressionId = (id, allocated))
    (childAccepted : inferExprFuel fuel context inner expected allocated = .ok child)
    (accepted : inferExprFuel (fuel + 1) context source expected initial = .ok final)
    (lifetime : GeneralizationLifetime event allocated.inference.next child.2 [child.1.type]) :
    GeneralizationLifetime event initial.inference.next final.2 [final.1.type] := by
  have allocatedEq : allocated = initial.allocateExpressionId.2 :=
    (congrArg Prod.snd allocation).symm
  have sameNext : allocated.inference.next = initial.inference.next := by
    rw [allocatedEq]; rfl
  have childProperties := inferExprFuel_inferenceProperties
    (allocatedEq ▸ ready.allocateExpressionId) catalog.formation catalog.canonical
    (fun type member => sameNext ▸ expectedBelow type member) childAccepted
  have recorded : recordExpressionWithExpected context source id child.1.type
      (.group child.1.id) [] expected child.2 = .ok final := by
    simpa only [inferExprFuel, allocation, form, childAccepted, bind, Except.bind] using accepted
  have result := lifetime.recordExpression catalog.catalog childProperties.2.1
    childProperties.2.2
    (fun type member => (sameNext ▸ expectedBelow type member).weaken childProperties.1.next_le)
    (lifetime.values _ (List.mem_singleton_self _))
    (fun type member => lifetime.older type (sameNext ▸ expectedBelow type member)) recorded
  have finalLifetime := result.restrict_outputs (selected := [final.1.type])
    (by intro type member; exact List.mem_append_right _ member)
  simpa only [sameNext] using finalLifetime

theorem tuple
    {fuel : Nat} {context : SourceInference.Context}
    {source : Syntax.Expr} {elements : Syntax.DelimitedList Syntax.Expr}
    {expected : Option Ty} {initial allocated : State} {id : ExpressionId}
    {child : List InferredExpression × State} {final : InferredExpression × State}
    (ready : initial.InferenceReady) (catalog : LifetimeInferenceContext context)
    (expectedBelow : ∀ type ∈ expected, type.VariablesBelow initial.inference.next)
    (form : source.value = .tuple elements)
    (allocation : initial.allocateExpressionId = (id, allocated))
    (childAccepted : inferExprsFuel fuel context elements.elements allocated = .ok child)
    (accepted : inferExprFuel (fuel + 1) context source expected initial = .ok final)
    (lifetime : GeneralizationLifetime event allocated.inference.next child.2
      (child.1.map (·.type))) :
    GeneralizationLifetime event initial.inference.next final.2 [final.1.type] := by
  have allocatedEq : allocated = initial.allocateExpressionId.2 :=
    (congrArg Prod.snd allocation).symm
  have sameNext : allocated.inference.next = initial.inference.next := by
    rw [allocatedEq]; rfl
  have childProperties := inferExprsFuel_inferenceProperties
    (allocatedEq ▸ ready.allocateExpressionId) catalog.formation catalog.canonical childAccepted
  have typeBelow : (Ty.productMany (child.1.map (·.type))).VariablesBelow child.2.inference.next := by
    apply Ty.variablesBelow_productMany
    intro type member
    obtain ⟨value, present, rfl⟩ := List.mem_map.mp member
    exact childProperties.2.2 value present
  have recorded : recordExpressionWithExpected context source id
      (Ty.productMany (child.1.map (·.type))) (.tuple (child.1.map (·.id)))
      [] expected child.2 = .ok final := by
    simpa only [inferExprFuel, allocation, form, childAccepted, bind, Except.bind] using accepted
  have result := lifetime.recordExpression catalog.catalog childProperties.2.1 typeBelow
    (fun type member => (sameNext ▸ expectedBelow type member).weaken childProperties.1.next_le)
    (safe_productMany _ _ _ lifetime.values)
    (fun type member => lifetime.older type (sameNext ▸ expectedBelow type member)) recorded
  have finalLifetime := result.restrict_outputs (selected := [final.1.type])
    (by intro type member; exact List.mem_append_right _ member)
  simpa only [sameNext] using finalLifetime

theorem expressions_head
    {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Expr}
    {sources : List Syntax.Expr} {initial : State}
    {head : InferredExpression × State} {tail result : List InferredExpression × State}
    (ready : initial.InferenceReady) (wellFormed : initial.RequirementsWellFormed)
    (catalog : LifetimeInferenceContext context)
    (headAccepted : inferExprFuel fuel context source none initial = .ok head)
    (tailAccepted : inferExprsFuel fuel context sources head.2 = .ok tail)
    (accepted : inferExprsFuel (fuel + 1) context (source :: sources) initial = .ok result)
    (lifetime : GeneralizationLifetime event initial.inference.next head.2 [head.1.type]) :
    GeneralizationLifetime event initial.inference.next result.2 (result.1.map (·.type)) := by
  have headProperties := inferExprFuel_inferenceProperties ready catalog.formation catalog.canonical
    (by simp) headAccepted
  have headWellFormed := (inferExprFuel_direct_progress headAccepted).wellFormed wellFormed
  have after := lifetime.inferExprs headProperties.2.1 headWellFormed catalog tailAccepted
  have resultEq : (head.1 :: tail.1, tail.2) = result := by
    simpa only [inferExprsFuel, headAccepted, tailAccepted, bind, Except.bind,
      pure, Pure.pure, Except.pure, Except.ok.injEq] using accepted
  cases resultEq
  simpa only [List.map_cons, List.singleton_append] using after

theorem expressions_tail
    {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Expr}
    {sources : List Syntax.Expr} {initial : State}
    {head : InferredExpression × State} {tail result : List InferredExpression × State}
    (ready : initial.InferenceReady) (catalog : LifetimeInferenceContext context)
    (headAccepted : inferExprFuel fuel context source none initial = .ok head)
    (tailAccepted : inferExprsFuel fuel context sources head.2 = .ok tail)
    (accepted : inferExprsFuel (fuel + 1) context (source :: sources) initial = .ok result)
    (lifetime : GeneralizationLifetime event head.2.inference.next tail.2 (tail.1.map (·.type))) :
    GeneralizationLifetime event initial.inference.next result.2 (result.1.map (·.type)) := by
  have headProperties := inferExprFuel_inferenceProperties ready catalog.formation catalog.canonical
    (by simp) headAccepted
  have resultEq : (head.1 :: tail.1, tail.2) = result := by
    simpa only [inferExprsFuel, headAccepted, tailAccepted, bind, Except.bind,
      pure, Pure.pure, Except.pure, Except.ok.injEq] using accepted
  cases resultEq
  have tailLifetime := lifetime.weaken_entry headProperties.1.next_le
  refine { tailLifetime with values := ?_ }
  intro type member
  rcases List.mem_cons.mp member with rfl | member
  · exact lifetime.older _ headProperties.2.2
  · exact lifetime.values _ member

end GeneralizationLifetime
end Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
