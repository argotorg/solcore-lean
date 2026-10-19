import Solcore.Test.SourceCoreMixedBuiltinHandlePlan
import Solcore.SourceSemantics.CoreLowering.CellAwarePublicDirectObservedOutput

/-! The observed completion belongs to the builtin call planned independently
from Source. Its unchanged mixed heap and every exported handle are retained. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
namespace Tests.SourceCoreMixedBuiltinValue
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering
open RecursiveNamedPublicFunctionHistory (Entry)

variable {fixture : ProfiledFixture} {row : Row fixture.original}
  {selected : SelectedInventory fixture row} {shape : Shape row.original.function.typedBody}
  {flag : Bool} {started : Started fixture.original row.original.key [.bool flag]}
  {callableProfile : fixture.original.recipe.compiled.compatible.checked.catalog.callableContracts = true}
  {first : InitialForward selected shape flag started callableProfile}
  {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
  {entries : List Entry} {retained : first.Retained session entries}
  {entry : Entry} {word : Core.Word}
  {call : CellAwarePublicHandleStart.StartedCall session entry.handle (.word word) runOptions.inputValidationFuel}

/-- Native determinism joins the actual completion to the independently
proved primitive call; no numerical sufficient-fuel bound is assumed. -/
theorem BuiltinHandlePlan.observed_retained
    (plan : BuiltinHandlePlan first retained entry word call)
    {executionFuel outputFuel : Nat} {returned : SourceCoreExecution.Completion artifact}
    (resumed : call.checkpoint.ResumeAt executionFuel outputFuel (.succeeded returned)) :
    ∃ continued : first.Retained returned.session entries,
      continued.state.heap = retained.state.heap := by
  obtain ⟨sidecar,_issued,_selected⟩ := selected.invocation
  obtain ⟨sourceSize,measured⟩ := RecursiveNamedCallBounds.CallOutcome.has_size (.value plan.trace)
  have metadata : SourceCoreRawMetadata.Extends plan.start.encodedValues.registry
      plan.ready.receiving.result.context.registry := by
    rw [plan.ready.contextAt]
    exact .refl _
  obtain ⟨native,store,mapping,world,required,run,resultAt⟩ :=
    CellAwarePublicBuiltinHandleMeaning.source_has_sufficient_fuel
      (invocation := RecursiveStageRegistry.scope sidecar [] selected.packet.header.function)
      callableProfile _ plan.ready.history.semantic entry plan.member plan.entryType plan.sourceEq plan.input
      plan.start.started plan.start.parameterView metadata (.singleton (.word word)) measured
  obtain ⟨actual,generation,reached,_exported,atReturned,_related,history,registry,exportsReady⟩ :=
    CellAwarePublicDirectObservedOutput.after_success _ _ plan.start.started
      (congrArg SourceCoreCompatibleValues.Context.registry plan.ready.contextAt) retained.exportsReady
      plan.start.atCheckpoint resultAt (run required (Nat.le_refl _)) resumed plan.ready.history
  exact ⟨⟨{
    artifact := retained.state.artifact, session := actual.session,
    mapping := mapping, world := world, heap := retained.state.heap, store := store, caller := reached,
    atSession := atReturned.2.2.2, atRecipe := retained.state.atRecipe,
    receiving := plan.ready.receiving, issued := plan.ready.issued, extension := plan.ready.extension,
    registry := registry, history := history
    },exportsReady⟩,rfl⟩

end Tests.SourceCoreMixedBuiltinValue
