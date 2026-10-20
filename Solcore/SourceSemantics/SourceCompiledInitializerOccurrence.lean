import Solcore.SourceSemantics.SourceCompiledBodySelectionFormation
import Solcore.SourceSemantics.SourceCompiledGeneralizedExpressionContracts

/-! The semantic initializer carrier retains only the actual computation,
its final source occurrence and the facts used by typing. Prior quantifier
avoidance is derived from the actual entering operational invariant; no
whole-suffix privacy law is carried into recursive typing. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledLocalFinalization
open Frontend SourceInference TypeSystem SourceInferenceSoundness
open SourceCompiledGeneralizedSoundness

structure BodyInitializerOccurrence {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel : Nat}
    (selected : BodySelection compiled row fuel) (source : Syntax.Statement) where
  childFuel : Nat
  inferenceContext : SourceInference.Context
  entry : State
  result : Detail.StatementResult
  receipt : LocalLetRequirementTiming.Receipt childFuel inferenceContext source entry result
  ready : receipt.ready.InferenceReady
  extension : selected.body.finalized.substitution.SemanticallyExtends receipt.ready.inference.substitution
  recorded : .statement {
    id := entry.allocateStatementId.1, span := source.span, type := .unit
    form := .letDecl receipt.binding.1 (some receipt.value.id) } ∈ selected.body.returned.nodes
  priorAvoided : ProtectedVariables.Avoids (activeSchemeQuantifiers entry)
    (receipt.ready.resolve receipt.value.type)

namespace BodyInitializerOccurrence
variable {raw : Workspace.RawWorkspace} {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel childFuel : Nat}
    {selected : BodySelection compiled row fuel} {source : Syntax.Statement}
    {inferenceContext : SourceInference.Context} {entry : State} {result : Detail.StatementResult}

/-- An actual accepted initializer and its exact retained statement suffice.
The ready state and prior-variable avoidance are produced by that inference. -/
def ofReceipt (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    (scope : CheckingScope selected inferenceContext)
    (receipt : LocalLetRequirementTiming.Receipt childFuel inferenceContext source entry result)
    (ready : entry.InferenceReady)
    (operational : GeneralizedActualStateInvariant entry (evidenceSource selected))
    (recorded : .statement {
      id := entry.allocateStatementId.1, span := source.span, type := .unit
      form := .letDecl receipt.binding.1 (some receipt.value.id) } ∈ selected.body.returned.nodes)
    (extension : selected.body.finalized.substitution.SemanticallyExtends result.state.inference.substitution) :
    BodyInitializerOccurrence selected source where
  childFuel
  inferenceContext
  entry
  result
  receipt
  ready := (receipt.initializer_inference ready (scope.formation checked)
    (scope.functionsCanonical checked)).2.1
  extension := by rwa [receipt.inference_eq] at extension
  recorded
  priorAvoided := ProtectedVariables.LocalLetRequirementTiming.Receipt.value_avoids_active receipt
    ready operational.requirements operational.quantifiersBelow operational.privacy
    (scope.catalog checked) (scope.formation checked) (scope.functionsCanonical checked)

theorem retained (occurrence : BodyInitializerOccurrence selected source) :
    occurrence.receipt.binding.1 ∈ (evidenceSource selected).initializedLetBinders :=
  List.mem_flatMap.mpr ⟨_, occurrence.recorded, List.mem_singleton_self _⟩

end BodyInitializerOccurrence

def RetainedInitializer.toOccurrence {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel : Nat}
    {selected : BodySelection compiled row fuel} {source : Syntax.Statement}
    (continuation : RetainedInitializer selected source) : BodyInitializerOccurrence selected source where
  childFuel := continuation.childFuel
  inferenceContext := continuation.inferenceContext
  entry := continuation.entry
  result := continuation.result
  receipt := continuation.receipt
  ready := continuation.privacy.ready
  extension := continuation.privacy.extension
  recorded := continuation.privacy.recorded
  priorAvoided := continuation.privacy.priorAvoided

/-- Ordinary callers keep their exact original selection witness. -/
abbrev InitializerOccurrence {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel : Nat}
    (selected : Selected compiled row fuel) (source : Syntax.Statement) :=
  BodyInitializerOccurrence selected.toBodySelection source

namespace InitializerOccurrence
export BodyInitializerOccurrence (ofReceipt retained)
end InitializerOccurrence

end Solcore.SourceSemantics.SourceCompiledLocalFinalization
