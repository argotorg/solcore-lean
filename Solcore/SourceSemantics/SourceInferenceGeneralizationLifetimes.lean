import Solcore.SourceSemantics.SourceInferenceSelectedPrivacyInference
import Solcore.SourceSemantics.Ownership
import Solcore.Frontend.SourceInference.LocalHeaderRequirementTiming

/-! Generalization lifetimes retain actual initialized statement or header
computations. Their privacy is indexed by the reached state and the output
types of the containing computation, including after the binder leaves scope. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
open Frontend SourceInference TypeSystem

inductive GeneralizationComputation :
    SourceInference.Context → State → State → InferredExpression → TypedBinder → Prop where
  | statement {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Statement}
      {initial : State} {result : Detail.StatementResult}
      (receipt : LocalLetRequirementTiming.Receipt fuel context source initial result) :
      GeneralizationComputation context initial receipt.ready receipt.value receipt.binding.1
  | header {fuel : Nat} {context : SourceInference.Context} {source : Syntax.ForItem}
      {initial : State} {result : ForItemForm × State}
      (receipt : LocalHeaderRequirementTiming.Receipt fuel context source initial result) :
      GeneralizationComputation context initial receipt.ready receipt.value receipt.binding.1

structure RetainedGeneralization (whole : TypedSource) (finalSubstitution : Substitution)
    (binder : TypedBinder) (initializer : ExpressionId) where
  context : SourceInference.Context
  entry : State
  readyState : State
  value : InferredExpression
  valueId : value.id = initializer
  computation : GeneralizationComputation context entry readyState value binder
  ready : readyState.InferenceReady
  extension : finalSubstitution.SemanticallyExtends readyState.inference.substitution
  retained : ({binder, initializer := .expression initializer} : InitializedLetBinding) ∈
    initializedLetBindings whole
  binderRetained : binder ∈ whole.initializedLetBinders

structure GeneralizationLifetime
    {whole : TypedSource} {finalSubstitution : Substitution}
    {binder : TypedBinder} {initializer : ExpressionId}
    (event : RetainedGeneralization whole finalSubstitution binder initializer)
    (entryNext : Nat) (state : State) (outputs : List Ty) : Prop where
  createdAfter : entryNext ≤ event.entry.inference.next
  allocated : ∀ q ∈ binder.scheme.quantified, event.entry.inference.next ≤ q.index
  bound : ∀ q ∈ binder.scheme.quantified, q.index < state.inference.next
  transport : SafeTransport binder.scheme.quantified event.readyState state
  live : LiveBindersSafe binder.scheme.quantified state
  values : ∀ type ∈ outputs, Safe binder.scheme.quantified state type
  older : ∀ type, type.VariablesBelow entryNext → Safe binder.scheme.quantified state type
  newRows : ∀ requirement ∈ state.requirements, requirement ∉ event.readyState.requirements →
    PredicateSafe binder.scheme.quantified state requirement.predicate

namespace GeneralizationLifetime
variable {whole : TypedSource} {finalSubstitution : Substitution}
    {binder : TypedBinder} {initializer : ExpressionId}
    {event : RetainedGeneralization whole finalSubstitution binder initializer}
    {entryNext : Nat} {before after : State} {outputs : List Ty}

/-- This composition only moves an already produced event. New events in the
second call must be supplied separately by that call's actual traversal. -/
theorem append
    (lifetime : GeneralizationLifetime event entryNext before outputs)
    (next : before.inference.next ≤ after.inference.next)
    (transport : SafeTransport binder.scheme.quantified before after)
    (live : LiveBindersSafe binder.scheme.quantified after)
    {newOutputs : List Ty}
    (values : ∀ type ∈ newOutputs, Safe binder.scheme.quantified after type)
    (newRows : ∀ requirement ∈ after.requirements, requirement ∉ before.requirements →
      PredicateSafe binder.scheme.quantified after requirement.predicate) :
    GeneralizationLifetime event entryNext after (outputs ++ newOutputs) where
  createdAfter := lifetime.createdAfter
  allocated := lifetime.allocated
  bound := fun q member => Nat.lt_of_lt_of_le (lifetime.bound q member) next
  transport := lifetime.transport.trans transport
  live
  values := by
    intro type member
    rcases List.mem_append.mp member with old | fresh
    · exact transport type (lifetime.values type old)
    · exact values type fresh
  older := fun type below => transport type (lifetime.older type below)
  newRows := new_requirements_trans lifetime.newRows newRows transport

theorem weaken_entry (lifetime : GeneralizationLifetime event entryNext before outputs)
    {earlier : Nat} (bound : earlier ≤ entryNext) :
    GeneralizationLifetime event earlier before outputs :=
  { lifetime with
    createdAfter := Nat.le_trans bound lifetime.createdAfter
    older := fun type below => lifetime.older type (below.weaken bound) }

theorem restrict_outputs (lifetime : GeneralizationLifetime event entryNext before outputs)
    {selected : List Ty} (subset : selected ⊆ outputs) :
    GeneralizationLifetime event entryNext before selected :=
  { lifetime with values := fun type member => lifetime.values type (subset member) }

/-- Sequential declarations cannot reuse a quantified variable which was
already allocated before the later initializer began. -/
theorem excludes_earlier (lifetime : GeneralizationLifetime event entryNext before outputs)
    {q : TypeVarId} (earlier : q.index < entryNext) : q ∉ binder.scheme.quantified := by
  intro quantified
  exact Nat.not_lt_of_ge (Nat.le_trans lifetime.createdAfter (lifetime.allocated q quantified)) earlier

end GeneralizationLifetime
end Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
