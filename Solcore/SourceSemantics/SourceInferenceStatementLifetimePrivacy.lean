import Solcore.SourceSemantics.SourceInferenceNewQuantifierFrame
import Solcore.SourceSemantics.SourceInferenceLiveTemplateBacking
import Solcore.SourceSemantics.SourceInferenceGeneralizedPrivacyBoundary

set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
open Frontend SourceInference TypeSystem Detail

namespace LocalLetRequirementTiming.Receipt

variable {wholeContext : SourceInference.Context} {wholeReturn : Ty}
    {evidenceState : State} {roots : List NodeId} {finalized : SourceInference.Result}
    {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Statement}
    {initial : State} {result : StatementResult}

/-- The new statement scheme quantifies only variables created by its initializer. -/
theorem lifetime_quantified_lower_bound
    (resources : FinalInferenceResources wholeContext wholeReturn evidenceState roots finalized)
    (receipt : SourceInference.LocalLetRequirementTiming.Receipt fuel context source initial result)
    (ready : initial.InferenceReady) (wellFormed : initial.RequirementsWellFormed)
    (catalog : SignatureCatalogWellFormed context.signatures)
    (formation : ProgramSignatureFormationValidated context.signatures)
    (canonical : ∀ signature ∈ context.signatures.functions,
      signature.scheme.body = .function (Ty.productMany signature.parameterTypes)
        (Ty.productMany signature.returnTypes))
    (backed : LiveTemplatesBacked initial)
    (origins : ActiveBinderCaptureOrigins initial (evidenceState.toTypedSource roots))
    (retained : receipt.binding.1 ∈ (evidenceState.toTypedSource roots).initializedLetBinders)
    (extension : finalized.substitution.SemanticallyExtends result.state.inference.substitution) :
    ∀ q ∈ receipt.binding.1.scheme.quantified, initial.inference.next ≤ q.index := by
  have inferred := receipt.initializer_inference ready formation canonical
  have templates := templates_before receipt backed ready wellFormed formation canonical
  have readyExtension : finalized.substitution.SemanticallyExtends receipt.ready.inference.substitution := by
    rwa [receipt.inference_eq] at extension
  have live : LiveBindersSafe receipt.binding.1.scheme.quantified receipt.ready :=
    generalized_live_from_finalizer resources (origins.congr_localBinders receipt.ready_binders)
      readyExtension retained rfl templates
  intro q quantified
  by_cases later : initial.inference.next ≤ q.index
  · exact later
  exfalso
  have earlier : q.index < initial.inference.next := Nat.lt_of_not_ge later
  have occurs : q ∈ (receipt.ready.resolve receipt.value.type).freeVariables :=
    (List.mem_filter.mp quantified).1
  have outside := inferred.2.1.solved.apply_variables_outside_domain receipt.value.type q occurs
  have fixed : receipt.ready.inference.substitution.apply (.variable q) = .variable q := by
    simp only [Substitution.apply,
      (Substitution.lookup?_eq_none_iff_not_mem_domain _ _).mpr outside, Option.getD_none]
  have backwards : ∀ type, Safe receipt.binding.1.scheme.quantified receipt.ready type →
      Safe [q] initial.allocateStatementId.2 type := by
    intro type privateType v present member
    have same : v = q := List.mem_singleton.mp member
    subst v
    exact privateType q (fixed_variable_occurs_at_final inferred.1.substitution_extends fixed present) quantified
  have entryLive : LiveBindersSafe [q] initial.allocateStatementId.2 := by
    intro binder member
    have readyMember : binder ∈ receipt.ready.localBinders := by
      rw [receipt.ready_binders]
      exact member
    have prior := live binder readyMember
    constructor
    · intro v free
      exact backwards _ (prior.1 v free)
    · intro requirement present type typeMember v free unbound
      exact backwards _ (prior.2 requirement present type typeMember v free unbound)
  have actual := inferExprFuel_private [q] fuel context receipt.initializer receipt.expected
    initial.allocateStatementId.2 ready.allocateStatementId wellFormed
    (by intro v member; obtain rfl := List.mem_singleton.mp member; exact earlier)
    entryLive catalog formation canonical (receipt.annotationAccepted.variablesBelow _)
    (fun type present => safe_closed _ _ (receipt.annotationAccepted.variablesBelow 0 type present))
    _ receipt.child
  exact actual.2.1 q occurs (List.mem_singleton_self _)

/-- A statement initializer keeps its new quantifiers out of every entering type. -/
theorem lifetime_older_type_safe
    (resources : FinalInferenceResources wholeContext wholeReturn evidenceState roots finalized)
    (receipt : SourceInference.LocalLetRequirementTiming.Receipt fuel context source initial result)
    (ready : initial.InferenceReady) (wellFormed : initial.RequirementsWellFormed)
    (catalog : SignatureCatalogWellFormed context.signatures)
    (formation : ProgramSignatureFormationValidated context.signatures)
    (canonical : ∀ signature ∈ context.signatures.functions,
      signature.scheme.body = .function (Ty.productMany signature.parameterTypes)
        (Ty.productMany signature.returnTypes))
    (backed : LiveTemplatesBacked initial)
    (origins : ActiveBinderCaptureOrigins initial (evidenceState.toTypedSource roots))
    (retained : receipt.binding.1 ∈ (evidenceState.toTypedSource roots).initializedLetBinders)
    (extension : finalized.substitution.SemanticallyExtends result.state.inference.substitution)
    {type : Ty} (typeBelow : type.VariablesBelow initial.inference.next) :
    Safe receipt.binding.1.scheme.quantified result.state type := by
  have templates := templates_before receipt backed ready wellFormed formation canonical
  have readyExtension : finalized.substitution.SemanticallyExtends receipt.ready.inference.substitution := by
    rwa [receipt.inference_eq] at extension
  have live : LiveBindersSafe receipt.binding.1.scheme.quantified receipt.ready :=
    generalized_live_from_finalizer resources (origins.congr_localBinders receipt.ready_binders)
      readyExtension retained rfl templates
  have safe := inferExprFuel_fresh_quantifiers_safe ready.allocateStatementId wellFormed catalog formation canonical
    (receipt.annotationAccepted.variablesBelow 0) receipt.child
    (lifetime_quantified_lower_bound resources receipt ready wellFormed catalog formation canonical
      backed origins retained extension) live typeBelow
  simpa only [Safe, State.resolve, InferState.resolve, receipt.inference_eq] using safe

end LocalLetRequirementTiming.Receipt

end Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
