import Solcore.SourceSemantics.SourceCompiledBodySelectionFormation
import Solcore.SourceSemantics.SourceCompiledInitializerOccurrenceInvariant

set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledLocalFinalization.BodyInitializerOccurrence
open Frontend SourceInference TypeSystem SourceInferenceSoundness
open SourceCompiledGeneralizedSoundness ProtectedVariables

theorem quantified_at_or_after_entry
    {raw : Workspace.RawWorkspace} {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel : Nat}
    {selected : BodySelection compiled row fuel} {source : Syntax.Statement}
    (occurrence : BodyInitializerOccurrence selected source)
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    (scope : CheckingScope selected occurrence.inferenceContext)
    (ready : occurrence.entry.InferenceReady)
    (operational : GeneralizedActualStateInvariant occurrence.entry (evidenceSource selected)) :
    ∀ q ∈ occurrence.receipt.binding.1.scheme.quantified,
      occurrence.entry.inference.next ≤ q.index := by
  have inferred := occurrence.receipt.initializer_inference ready
    (scope.formation checked) (scope.functionsCanonical checked)
  have templates := ProtectedVariables.LocalLetRequirementTiming.Receipt.templates_before
    occurrence.receipt operational.backed ready operational.requirements
    (scope.formation checked) (scope.functionsCanonical checked)
  have live : LiveBindersSafe occurrence.receipt.binding.1.scheme.quantified occurrence.receipt.ready :=
    generalized_live_from_finalizer selected.body.resources
      (operational.origins.congr_localBinders occurrence.receipt.ready_binders)
      occurrence.extension occurrence.retained rfl templates
  intro q quantified
  by_cases later : occurrence.entry.inference.next ≤ q.index
  · exact later
  exfalso
  have earlier : q.index < occurrence.entry.inference.next := Nat.lt_of_not_ge later
  have occurs : q ∈ (occurrence.receipt.ready.resolve occurrence.receipt.value.type).freeVariables :=
    (List.mem_filter.mp quantified).1
  have outside := occurrence.ready.solved.apply_variables_outside_domain
    occurrence.receipt.value.type q occurs
  have fixed : occurrence.receipt.ready.inference.substitution.apply (.variable q) = .variable q := by
    simp only [Substitution.apply,
      (Substitution.lookup?_eq_none_iff_not_mem_domain _ _).mpr outside, Option.getD_none]
  have backwards : ∀ type, Safe occurrence.receipt.binding.1.scheme.quantified occurrence.receipt.ready type →
      Safe [q] occurrence.entry.allocateStatementId.2 type := by
    intro type privateType v present member
    have same : v = q := List.mem_singleton.mp member
    subst v
    exact privateType q (fixed_variable_occurs_at_final inferred.1.substitution_extends fixed present) quantified
  have entryLive : LiveBindersSafe [q] occurrence.entry.allocateStatementId.2 := by
    intro binder member
    have readyMember : binder ∈ occurrence.receipt.ready.localBinders := by
      rw [occurrence.receipt.ready_binders]
      exact member
    have prior := live binder readyMember
    constructor
    · intro v free
      exact backwards _ (prior.1 v free)
    · intro requirement present type typeMember v free unbound
      exact backwards _ (prior.2 requirement present type typeMember v free unbound)
  have actual := inferExprFuel_private [q] occurrence.childFuel occurrence.inferenceContext
    occurrence.receipt.initializer occurrence.receipt.expected occurrence.entry.allocateStatementId.2
    ready.allocateStatementId operational.requirements
    (by intro v member; obtain rfl := List.mem_singleton.mp member; exact earlier)
    entryLive (scope.catalog checked) (scope.formation checked) (scope.functionsCanonical checked)
    (occurrence.receipt.annotationAccepted.variablesBelow _)
    (fun type present => safe_closed _ _ (occurrence.receipt.annotationAccepted.variablesBelow 0 type present))
    _ occurrence.receipt.child
  exact actual.2.1 q occurs (List.mem_singleton_self _)

end Solcore.SourceSemantics.SourceCompiledLocalFinalization.BodyInitializerOccurrence

namespace Solcore.SourceSemantics.SourceCompiledLocalFinalization.InitializerOccurrence
export BodyInitializerOccurrence (quantified_at_or_after_entry)
end Solcore.SourceSemantics.SourceCompiledLocalFinalization.InitializerOccurrence
