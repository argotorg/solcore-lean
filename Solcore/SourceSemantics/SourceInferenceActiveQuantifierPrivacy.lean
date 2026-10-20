import Solcore.SourceSemantics.SourceInferenceBackedStatementPrivacy
import Solcore.SourceSemantics.SourceInferenceGeneralizedPrivacyBoundary

/-! Each active generalized binder has a privacy invariant for its own variables.
Older binders use actual inference preservation; a new binder uses the real
executable generalizer and finalizer capture checks. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
open Frontend SourceInference TypeSystem Detail

def ActiveQuantifiersPrivate (state : State) : Prop :=
  ∀ binder ∈ state.localBinders, LiveBindersSafe binder.scheme.quantified state

theorem liveBindersSafe_nil (state : State) : LiveBindersSafe [] state := by
  intro binder member
  constructor
  · intro v occurs q image protectedMember
    exact List.not_mem_nil protectedMember
  · intro requirement present type typeMember v occurs outside q image protectedMember
    exact List.not_mem_nil protectedMember

theorem ActiveQuantifiersPrivate.initial (owner : Resolved.DeclarationId)
    (locals : Environment) (comptime : List Bool)
    (monomorphic : ∀ entry ∈ locals, entry.2.quantified = []) :
    ActiveQuantifiersPrivate (State.initial owner locals comptime) := by
  intro binder member
  rw [← State.initial_inputs_eq_localBinders, State.initial_inputs_definition] at member
  obtain ⟨index, indexLt, binderEq⟩ := List.exists_of_mem_mapIdx member
  subst binder
  have empty := monomorphic locals[index] (List.getElem_mem indexLt)
  change LiveBindersSafe locals[index].2.quantified _
  rw [empty]
  exact liveBindersSafe_nil _

namespace LocalLetRequirementTiming.Receipt

/-- The exact initialized statement supplies the newly generalized binder and
all old-template provenance needed by its actual finalizer capture checks. -/
theorem active_privacy
    {wholeContext : SourceInference.Context} {wholeReturn : Ty}
    {evidenceState : State} {roots : List NodeId} {finalized : SourceInference.Result}
    (resources : FinalInferenceResources wholeContext wholeReturn evidenceState roots finalized)
    {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Statement}
    {initial : State} {result : StatementResult}
    (receipt : SourceInference.LocalLetRequirementTiming.Receipt fuel context source initial result)
    (ready : initial.InferenceReady) (wellFormed : initial.RequirementsWellFormed)
    (formation : ProgramSignatureFormationValidated context.signatures)
    (canonical : ∀ signature ∈ context.signatures.functions,
      signature.scheme.body = .function (Ty.productMany signature.parameterTypes) (Ty.productMany signature.returnTypes))
    (backed : LiveTemplatesBacked initial)
    (origins : ActiveBinderCaptureOrigins initial (evidenceState.toTypedSource roots))
    (retained : result.state.nodes <+: evidenceState.nodes)
    (extension : finalized.substitution.SemanticallyExtends result.state.inference.substitution) :
    LiveBindersSafe receipt.binding.1.scheme.quantified result.state := by
  have readyOrigins := origins.congr_localBinders receipt.ready_binders
  have templates := templates_before receipt backed ready wellFormed formation canonical
  have readyExtension : finalized.substitution.SemanticallyExtends receipt.ready.inference.substitution := by
    rwa [receipt.inference_eq] at extension
  have retainedBinder : receipt.binding.1 ∈ (evidenceState.toTypedSource roots).initializedLetBinders := by
    unfold TypedSource.initializedLetBinders
    exact List.mem_flatMap.mpr ⟨_,retained.subset receipt.recorded,List.mem_singleton_self _⟩
  have live := allocate_generalized_live_from_finalizer resources initial.nextRequirement
    (receipt.ready.resolve receipt.value.type) receipt.name.value (some receipt.name.span) false
    (readyOrigins.withLocals receipt.locals) readyExtension templates retainedBinder
  have same : result.state.inference = receipt.binding.2.inference :=
    congrArg (fun result : StatementResult => result.state.inference) receipt.completed
  have binders : result.state.localBinders = receipt.binding.2.localBinders :=
    congrArg (fun result : StatementResult => result.state.localBinders) receipt.completed
  intro binder member
  exact (live binder (binders ▸ member)).transport (.of_substitution_eq (congrArg InferState.substitution same))

/-- Inference of this actual initializer avoids every currently active scheme
quantifier when the prefix has established their live privacy. -/
theorem value_avoids_active
    {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Statement}
    {initial : State} {result : StatementResult}
    (receipt : SourceInference.LocalLetRequirementTiming.Receipt fuel context source initial result)
    (ready : initial.InferenceReady) (wellFormed : initial.RequirementsWellFormed)
    (bound : ActiveQuantifiersBelowNext initial) (privateVars : ActiveQuantifiersPrivate initial)
    (catalog : SignatureCatalogWellFormed context.signatures)
    (formation : ProgramSignatureFormationValidated context.signatures)
    (canonical : ∀ signature ∈ context.signatures.functions,
      signature.scheme.body = .function (Ty.productMany signature.parameterTypes) (Ty.productMany signature.returnTypes)) :
    Avoids (activeSchemeQuantifiers initial) (receipt.ready.resolve receipt.value.type) := by
  intro q occurs active
  obtain ⟨binder,member,quantified⟩ := List.mem_flatMap.mp active
  have allocatedLive : LiveBindersSafe binder.scheme.quantified initial.allocateStatementId.2 :=
    (privateVars binder member).transport rfl (.of_substitution_eq rfl)
  have expectedSafe : ∀ type ∈ receipt.expected, Safe binder.scheme.quantified initial.allocateStatementId.2 type := by
    intro type present
    exact safe_closed _ _ (receipt.annotationAccepted.variablesBelow 0 type present)
  have actual := inferExprFuel_private binder.scheme.quantified fuel context receipt.initializer receipt.expected
    initial.allocateStatementId.2 ready.allocateStatementId
    wellFormed
    (bound binder member) allocatedLive catalog formation canonical
    (receipt.annotationAccepted.variablesBelow _) expectedSafe _ receipt.child
  exact actual.2.1 q occurs quantified

end LocalLetRequirementTiming.Receipt
end Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
