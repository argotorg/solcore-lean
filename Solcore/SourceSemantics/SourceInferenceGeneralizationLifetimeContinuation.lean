import Solcore.SourceSemantics.SourceInferenceGeneralizationLifetimes

/-! Existing events survive the actual next inference call. Newly created
events are handled by the recursive traversal of that call. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
open Frontend SourceInference TypeSystem Detail

structure LifetimeInferenceContext (context : SourceInference.Context) : Prop where
  catalog : SignatureCatalogWellFormed context.signatures
  formation : ProgramSignatureFormationValidated context.signatures
  canonical : ∀ signature ∈ context.signatures.functions,
    signature.scheme.body = .function (Ty.productMany signature.parameterTypes)
      (Ty.productMany signature.returnTypes)

namespace GeneralizationLifetime
variable {whole : TypedSource} {finalSubstitution : Substitution}
    {binder : TypedBinder} {initializer : ExpressionId}
    {event : RetainedGeneralization whole finalSubstitution binder initializer}
    {entryNext : Nat} {state : State} {outputs : List Ty}
    {fuel : Nat} {context : SourceInference.Context}

theorem inferExpr
    (lifetime : GeneralizationLifetime event entryNext state outputs)
    (ready : state.InferenceReady) (wellFormed : state.RequirementsWellFormed)
    (catalog : LifetimeInferenceContext context)
    {source : Syntax.Expr} {expected : Option Ty} {result : InferredExpression × State}
    (expectedBelow : ∀ type ∈ expected, type.VariablesBelow state.inference.next)
    (expectedSafe : ∀ type ∈ expected, Safe binder.scheme.quantified state type)
    (accepted : inferExprFuel fuel context source expected state = .ok result) :
    GeneralizationLifetime event entryNext result.2 (outputs ++ [result.1.type]) := by
  have privacy := inferExprFuel_private binder.scheme.quantified fuel context source expected state
    ready wellFormed lifetime.bound lifetime.live catalog.catalog catalog.formation catalog.canonical
    expectedBelow expectedSafe result accepted
  have progress := inferExprFuel_inferenceProperties ready catalog.formation catalog.canonical expectedBelow accepted
  exact lifetime.append progress.1.next_le privacy.1 privacy.2.2.1
    (fun type member => (List.mem_singleton.mp member) ▸ privacy.2.1) privacy.2.2.2

theorem inferExprs
    (lifetime : GeneralizationLifetime event entryNext state outputs)
    (ready : state.InferenceReady) (wellFormed : state.RequirementsWellFormed)
    (catalog : LifetimeInferenceContext context)
    {sources : List Syntax.Expr} {result : List InferredExpression × State}
    (accepted : inferExprsFuel fuel context sources state = .ok result) :
    GeneralizationLifetime event entryNext result.2 (outputs ++ result.1.map (·.type)) := by
  have privacy := inferExprsFuel_private binder.scheme.quantified fuel context sources state
    ready wellFormed lifetime.bound lifetime.live catalog.catalog catalog.formation catalog.canonical result accepted
  have progress := inferExprsFuel_inferenceProperties ready catalog.formation catalog.canonical accepted
  refine lifetime.append progress.1.next_le privacy.1 privacy.2.2.1 ?_ privacy.2.2.2
  intro type member
  obtain ⟨expression, present, rfl⟩ := List.mem_map.mp member
  exact privacy.2.1 expression present

theorem inferStatement
    (lifetime : GeneralizationLifetime event entryNext state outputs)
    (ready : state.InferenceReady) (wellFormed : state.RequirementsWellFormed)
    (catalog : LifetimeInferenceContext context)
    {source : Syntax.Statement} {expected : Ty} {result : StatementResult}
    (expectedBelow : expected.VariablesBelow state.inference.next)
    (expectedSafe : Safe binder.scheme.quantified state expected)
    (accepted : inferStatementFuel fuel context source expected state = .ok result) :
    GeneralizationLifetime event entryNext result.state (outputs ++ [result.type]) := by
  have privacy := inferStatementFuel_private binder.scheme.quantified fuel context source expected state
    ready wellFormed lifetime.bound lifetime.live catalog.catalog catalog.formation catalog.canonical
    expectedBelow expectedSafe result accepted
  have progress := inferStatementFuel_inferenceProperties ready catalog.formation catalog.canonical expectedBelow accepted
  exact lifetime.append progress.1.next_le privacy.1 privacy.2.2.1
    (fun type member => (List.mem_singleton.mp member) ▸ privacy.2.1) privacy.2.2.2

theorem inferStatements
    (lifetime : GeneralizationLifetime event entryNext state outputs)
    (ready : state.InferenceReady) (wellFormed : state.RequirementsWellFormed)
    (catalog : LifetimeInferenceContext context)
    {sources : List Syntax.Statement} {expected : Ty} {result : BlockResult}
    (expectedBelow : expected.VariablesBelow state.inference.next)
    (expectedSafe : Safe binder.scheme.quantified state expected)
    (accepted : inferStatementsFuel fuel context sources expected state = .ok result) :
    GeneralizationLifetime event entryNext result.state (outputs ++ [result.type]) := by
  have privacy := inferStatementsFuel_private binder.scheme.quantified fuel context sources expected state
    ready wellFormed lifetime.bound lifetime.live catalog.catalog catalog.formation catalog.canonical
    expectedBelow expectedSafe result accepted
  have progress := inferStatementsFuel_inferenceProperties ready catalog.formation catalog.canonical expectedBelow accepted
  exact lifetime.append progress.1.next_le privacy.1 privacy.2.2.1
    (fun type member => (List.mem_singleton.mp member) ▸ privacy.2.1) privacy.2.2.2

theorem inferForItem
    (lifetime : GeneralizationLifetime event entryNext state outputs)
    (ready : state.InferenceReady) (wellFormed : state.RequirementsWellFormed)
    (catalog : LifetimeInferenceContext context)
    {source : Syntax.ForItem} {result : ForItemForm × State}
    (accepted : inferForItemFuel fuel context source state = .ok result) :
    GeneralizationLifetime event entryNext result.2 outputs := by
  have privacy := inferForItemFuel_private binder.scheme.quantified fuel context source state
    ready wellFormed lifetime.bound lifetime.live catalog.catalog catalog.formation catalog.canonical result accepted
  have progress := inferForItemFuel_inferenceProperties ready catalog.formation catalog.canonical accepted
  simpa only [List.append_nil] using lifetime.append (newOutputs := [])
    progress.1.next_le privacy.1 privacy.2.1 (by simp) privacy.2.2

theorem inferForItems
    (lifetime : GeneralizationLifetime event entryNext state outputs)
    (ready : state.InferenceReady) (wellFormed : state.RequirementsWellFormed)
    (catalog : LifetimeInferenceContext context)
    {sources : List Syntax.ForItem} {result : InferredForItems}
    (accepted : inferForItemsFuel fuel context sources state = .ok result) :
    GeneralizationLifetime event entryNext result.state outputs := by
  have privacy := inferForItemsFuel_private binder.scheme.quantified fuel context sources state
    ready wellFormed lifetime.bound lifetime.live catalog.catalog catalog.formation catalog.canonical result accepted
  have progress := inferForItemsFuel_inferenceProperties ready catalog.formation catalog.canonical accepted
  simpa only [List.append_nil] using lifetime.append (newOutputs := [])
    progress.1.next_le privacy.1 privacy.2.1 (by simp) privacy.2.2

end GeneralizationLifetime
end Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
