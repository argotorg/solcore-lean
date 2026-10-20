import Solcore.SourceSemantics.SourceInferenceGeneralizationLifetimeStatementSteps

/-! Actual allocator and unifier steps used after a nested event. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
open Frontend SourceInference TypeSystem Detail
namespace GeneralizationLifetime
variable {whole : TypedSource} {finalSubstitution : Substitution}
    {binder : TypedBinder} {initializer : ExpressionId}
    {event : RetainedGeneralization whole finalSubstitution binder initializer}
    {entryNext : Nat} {state : State} {outputs : List Ty}

theorem replaceOutputs
    (lifetime : GeneralizationLifetime event entryNext state outputs)
    {values : List Ty}
    (safe : ∀ type ∈ values, Safe binder.scheme.quantified state type) :
    GeneralizationLifetime event entryNext state values :=
  { lifetime with values := safe }

theorem unify
    (lifetime : GeneralizationLifetime event entryNext state outputs)
    {left right : Ty} {after : State}
    (ready : state.InferenceReady)
    (leftBelow : left.VariablesBelow state.inference.next)
    (rightBelow : right.VariablesBelow state.inference.next)
    (leftSafe : Safe binder.scheme.quantified state left)
    (rightSafe : Safe binder.scheme.quantified state right)
    (accepted : Detail.unify state left right = .ok after) :
    GeneralizationLifetime event entryNext after outputs := by
  have progress := unify_inferenceProgress ready.solved leftBelow rightBelow accepted
  have transport := ProtectedVariables.unify leftSafe rightSafe accepted
  have live := lifetime.live.unify leftSafe rightSafe accepted
  have result := lifetime.append (newOutputs := []) progress.next_le transport live
    (by simp) (by
      intro row present fresh
      exact False.elim (fresh ((unify_requirements_eq accepted) ▸ present)))
  simpa only [List.append_nil] using result

theorem fresh
    (lifetime : GeneralizationLifetime event entryNext state outputs)
    (ready : state.InferenceReady) :
    GeneralizationLifetime event entryNext state.fresh.2 (outputs ++ [state.fresh.1]) := by
  have transport : SafeTransport binder.scheme.quantified state state.fresh.2 :=
    ProtectedVariables.fresh
  exact lifetime.append (Nat.le_succ _) transport
    (lifetime.live.transport rfl transport)
    (fun type member => (List.mem_singleton.mp member) ▸ fresh_type ready lifetime.bound)
    (by intro row present fresh; exact False.elim (fresh present))

end GeneralizationLifetime
end Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
