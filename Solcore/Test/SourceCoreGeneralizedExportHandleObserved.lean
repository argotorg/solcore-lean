import Solcore.Test.SourceCoreGeneralizedExportHandlePlan
import Solcore.SourceSemantics.CoreLowering.CellAwarePublicDirectObservedOutput

/-! The observed result of the already planned independent Source call retains
all exported functions at its exact returned Source/native heap. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
namespace Tests.SourceCoreGeneralizedExport
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedBootstrapRootState (keys owner)
open RecursiveNamedPublicFunctionHistory (Entry)

variable {fixture : ProfiledFixture} {whole : WholeInventory fixture} {row : Row fixture.original}
  {selected : SelectedInventory whole row} {shape : MakeShape row.original.function.typedBody}
  {flag : Bool} {started : Started fixture.original row.original.key [.bool flag]}
  {callableProfile : fixture.original.recipe.compiled.compatible.checked.catalog.callableContracts = true}
  {first : InitialForward selected shape flag started callableProfile}
  {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
  {entries : List Entry} {retained : first.Retained session entries}
  {entry : Entry} {parameter result : TypeSystem.Ty}
  {argument : SourceCorePublicValues.Value} {sourceArgument : Dynamic.Value}
  {call : CellAwarePublicHandleStart.StartedCall session entry.handle argument runOptions.inputValidationFuel}

/-- No result of the current target is used to construct the independent call.
Its actual completion identifies the same final store by native determinism. -/
theorem HandleSourcePlan.observed_retained {value : Dynamic.Value} {after : Dynamic.Heap}
    (plan : HandleSourcePlan first retained entry call parameter result sourceArgument value after)
    (typing : OriginalTyping fixture.original)
    (origins : CellAwareMaterializedRetainedEntries.Retained (keys fixture.original.recipe.compiled)
      retained.state.mapping retained.state.world entries)
    {executionFuel outputFuel : Nat} {returned : SourceCoreExecution.Completion artifact}
    (resumed : call.checkpoint.ResumeAt executionFuel outputFuel (.succeeded returned)) :
    ∃ continued : first.Retained returned.session entries,
      continued.state.heap = after ∧
      CellAwareMaterializedRetainedEntries.Retained (keys fixture.original.recipe.compiled)
        continued.state.mapping continued.state.world entries := by
  obtain ⟨sidecar,_issued,_selected⟩ := selected.invocation
  obtain ⟨sourceSize,measured⟩ := RecursiveNamedCallBounds.CallOutcome.has_size (.value plan.trace)
  have metadata : SourceCoreRawMetadata.Extends plan.start.encodedValues.registry
      plan.ready.receiving.result.context.registry := by
    rw [plan.ready.contextAt]
    exact .refl _
  obtain ⟨native,store,mapping,world,required,run,resultAt⟩ :=
    CellAwarePublicRetainedMaterializedHandle.source_has_sufficient_fuel
      (invocation := RecursiveStageRegistry.scope sidecar [] selected.packet.header.function)
      first.functions callableProfile plan.ready.issued plan.ready.receiving.result.extension
      (SelectedCompilationBodyTyping.Bodies.of_program typing.wellFormed) typing.wellFormed
      plan.ready.history.semantic entry plan.member plan.entryType plan.sourceEq plan.materialized plan.input
      plan.start.started plan.start.parameterView metadata (.singleton sourceArgument) plan.arity measured
  obtain ⟨actual,generation,reached,_exported,atReturned,_related,history,registry,exportsReady⟩ :=
    CellAwarePublicDirectObservedOutput.after_success _ _ plan.start.started
      (congrArg SourceCoreCompatibleValues.Context.registry plan.ready.contextAt) retained.exportsReady
      plan.start.atCheckpoint resultAt (run required (Nat.le_refl _)) resumed plan.ready.history
  exact ⟨⟨{
    artifact := retained.state.artifact, session := actual.session,
    mapping := mapping, world := world, heap := after, store := store, caller := reached,
    atSession := atReturned.2.2.2, atRecipe := retained.state.atRecipe,
    receiving := plan.ready.receiving, issued := plan.ready.issued, extension := plan.ready.extension,
    registry := registry, history := history
    },exportsReady⟩,rfl,origins.extend resultAt.2.2.1 resultAt.2.2.2.1⟩

end Tests.SourceCoreGeneralizedExport
