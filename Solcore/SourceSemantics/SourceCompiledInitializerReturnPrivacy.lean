import Solcore.SourceSemantics.SourceCompiledInitializerQuantifierFreshness
import Solcore.SourceSemantics.SourceInferenceNewQuantifierFrame

/-! Newly generalized variables cannot enter a type already present at the
initializer entry. The actual child computation supplies fixedness of any
older variable which its live context avoids. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledLocalFinalization.InitializerOccurrence
open Frontend SourceInference TypeSystem SourceInferenceSoundness
open SourceCompiledGeneralizedSoundness ProtectedVariables

theorem generalized_type_safe
    {raw : Workspace.RawWorkspace} {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel : Nat}
    {selected : Selected compiled row fuel} {source : Syntax.Statement}
    (occurrence : InitializerOccurrence selected source)
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    (scope : CheckingScope selected occurrence.inferenceContext)
    (ready : occurrence.entry.InferenceReady)
    (operational : GeneralizedActualStateInvariant occurrence.entry (evidenceSource selected))
    {type : Ty} (typeBelow : type.VariablesBelow occurrence.entry.inference.next) :
    Safe occurrence.receipt.binding.1.scheme.quantified occurrence.receipt.ready type := by
  have templates := ProtectedVariables.LocalLetRequirementTiming.Receipt.templates_before
    occurrence.receipt operational.backed ready operational.requirements
    (scope.formation checked) (scope.functionsCanonical checked)
  have live : LiveBindersSafe occurrence.receipt.binding.1.scheme.quantified occurrence.receipt.ready :=
    generalized_live_from_finalizer selected.body.resources
      (operational.origins.congr_localBinders occurrence.receipt.ready_binders)
      occurrence.extension occurrence.retained rfl templates
  exact inferExprFuel_fresh_quantifiers_safe ready.allocateStatementId operational.requirements
    (scope.catalog checked) (scope.formation checked) (scope.functionsCanonical checked)
    (occurrence.receipt.annotationAccepted.variablesBelow 0) occurrence.receipt.child
    (occurrence.quantified_at_or_after_entry checked scope ready operational) live typeBelow

theorem return_safe
    {raw : Workspace.RawWorkspace} {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel : Nat}
    {selected : Selected compiled row fuel} {source : Syntax.Statement}
    (occurrence : InitializerOccurrence selected source)
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    (scope : CheckingScope selected occurrence.inferenceContext)
    (ready : occurrence.entry.InferenceReady)
    (operational : GeneralizedActualStateInvariant occurrence.entry (evidenceSource selected))
    {expectedReturn : Ty}
    (returnBelow : expectedReturn.VariablesBelow occurrence.entry.inference.next)
    (returnSafe : ∀ binder ∈ occurrence.entry.localBinders,
      Safe binder.scheme.quantified occurrence.entry expectedReturn) :
    ∀ binder ∈ occurrence.result.state.localBinders,
      Safe binder.scheme.quantified occurrence.result.state expectedReturn := by
  intro binder member
  rw [occurrence.receipt.result_binders] at member
  rcases List.mem_cons.mp member with rfl | old
  · have safe := occurrence.generalized_type_safe checked scope ready operational returnBelow
    simpa only [Safe, State.resolve, InferState.resolve, occurrence.receipt.inference_eq] using safe
  · have privacy := inferExprFuel_private binder.scheme.quantified occurrence.childFuel
      occurrence.inferenceContext occurrence.receipt.initializer occurrence.receipt.expected
      occurrence.entry.allocateStatementId.2 ready.allocateStatementId operational.requirements
      (operational.quantifiersBelow binder old) (operational.allocateStatementId.privacy binder old)
      (scope.catalog checked) (scope.formation checked) (scope.functionsCanonical checked)
      (occurrence.receipt.annotationAccepted.variablesBelow _)
      (fun type present => safe_closed _ _ (occurrence.receipt.annotationAccepted.variablesBelow 0 type present))
      _ occurrence.receipt.child
    have safe := privacy.1 expectedReturn (returnSafe binder old)
    simpa only [Safe, State.resolve, InferState.resolve, occurrence.receipt.inference_eq] using safe

end Solcore.SourceSemantics.SourceCompiledLocalFinalization.InitializerOccurrence
