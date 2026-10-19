import Solcore.SourceSemantics.CoreLowering.CellAwarePublicPhysicalHistory
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicDirectPackedInputMeaning
import Solcore.SourceSemantics.CoreLowering.CompatiblePublicOutputShapes
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicReturnedInputRegistry

/-! A direct handle call retains its actual mixed heap and prior public history.
The original requested signature and output codec determine public completion. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwarePublicDirectOutput
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open SourceCoreIndexedSession CallableIndexedOwnedFunctionState
open CallableIndexedOwnedFunctionValues (Header)
open CellAwarePublicFunctionHistory (Caller)
open CellAwarePublicApplicationResult (ResultAt)
open RecursiveNamedPublicFunctionHistory (Entry)
open RecursiveNamedPublicDirectPackedInputMeaning (StartAt)

variable {recipe : Recipe}
  {headers : List (Header recipe.compiled (Program.ofChecked recipe.compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key recipe.compiled (Program.ofChecked recipe.compiled.sourceProgram))}
  (functions : FunctionModel recipe.compiled.compatible.checked.catalog
    (CallableIndexedAmbient.ambientDefinitions recipe.compiled.indexed))
  (cells : GenericHeap.CellModel (CallableIndexedAmbient.ambientDefinitions recipe.compiled.indexed).definitions)
  {registry : SourceCoreRawMetadata.Registry}
  {anchor : Header recipe.compiled (Program.ofChecked recipe.compiled.sourceProgram)}
  {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store : Store}
  {caller : Caller headers keys mapping world before store}
  {artifact : Artifact} {session : Session artifact} {checkpoint : Checkpoint artifact}
  {handle : SourceCorePublicValues.Handle} {argument : SourceCorePublicValues.Value}
  {inputFuel : Nat} {encodedValues : SourceCoreCompatibleValues.Context}
  {parameter requested sourceResult : TypeSystem.Ty} {nativeParameter nativeResult : Core.Ty}
  {callable packed : Core.Value}
  (started : StartAt session handle argument inputFuel checkpoint recipe world store
    parameter requested nativeParameter nativeResult callable packed encodedValues)
  (exactRegistry : registry = encodedValues.registry)
  (resultView : SourceCoreRawMetadata.runtimeType requested = SourceCoreRawMetadata.runtimeType sourceResult)
  (ready : session.ExportsReady)
  {publicArtifact : SourceCoreExecution.Artifact} {publicCheckpoint : SourceCoreExecution.Checkpoint publicArtifact}
  (atCheckpoint : publicCheckpoint.IndexedAt checkpoint)
  {source : Dynamic.Value} {after : Dynamic.Heap} {native : Core.Value} {finalStore : Store}
  {finalMap : LocationMap} {finalWorld : StoreTyping} {faults : RecursiveStageMeaning.FaultRep}
  (result : ResultAt (registry := registry) functions cells caller anchor.function.context sourceResult nativeResult
    (.value source) after native finalStore finalMap finalWorld faults)
  {requiredExecution : Nat}
  (completes : ∀ executionFuel, requiredExecution ≤ executionFuel → checkpoint.NativeDone executionFuel native finalStore)

include started exactRegistry resultView ready atCheckpoint result completes in
theorem exports :
    ∃ payload requiredOutput,
      native = .inRight .word payload ∧
      ValueRep recipe.compiled.compatible.checked registry functions finalMap finalWorld
        sourceResult source payload nativeResult ∧
      ∀ executionFuel outputFuel (outcome : SourceCoreExecution.Outcome publicArtifact),
        requiredExecution ≤ executionFuel → requiredOutput ≤ outputFuel →
        publicCheckpoint.ResumeAt executionFuel outputFuel outcome →
        ∃ (completion : SourceCoreExecution.Completion publicArtifact) (actual : Completion artifact)
          (generation : SourceCorePublicValues.ExportGeneration),
          outcome = .succeeded completion ∧
          checkpoint.SucceededResultAt executionFuel outputFuel generation native finalStore actual ∧
          completion.IndexedAt actual ∧ actual.session.ExportsReady := by
  obtain ⟨payload, same⟩ : ∃ payload, native = .inRight .word payload := by
    cases result.1 with
    | value _ => exact ⟨_, rfl⟩
  subst native
  have represented : ValueRep recipe.compiled.compatible.checked registry functions finalMap finalWorld
      sourceResult source payload nativeResult := by
    cases result.1 with
    | value represented => exact represented
  have shape : SourceCorePublicOutputShapes.Output recipe.compiled.compatible.checked encodedValues.registry
      (finalStore.map Core.Value.type) recipe.program.layouts.definitions requested payload := by
    have shaped := CompatiblePublicOutputShapes.ValueRep.output represented
    rw [exactRegistry, result.2.1.runtime_hasTypes.world_eq] at shaped
    exact .compatible resultView shaped
  have checkpointRegistry : checkpoint.RegistryAt encodedValues.registry := by
    have values := started.values
    cases checkpoint
    change _ = encodedValues at values
    exact congrArg SourceCoreCompatibleValues.Context.registry values
  have checkpointReady := started.original.initial_registry.exportsReady ready
  obtain ⟨requiredOutput, exported⟩ := publicCheckpoint.output_succeeded_uniform
    atCheckpoint started.recipe_eq checkpointRegistry checkpointReady started.requested shape
  exact ⟨payload, requiredOutput, rfl, represented, fun executionFuel outputFuel outcome enough outputEnough resumed =>
    exported executionFuel (completes executionFuel enough) outputFuel outputEnough outcome resumed⟩

include started exactRegistry resultView ready atCheckpoint result completes in
/-- The actual successful direct call keeps all earlier handles and the full
physical cache at its restored caller and final mixed heap. -/
theorem after_success {entries : List Entry}
    (history : CellAwarePublicPhysicalHistory.History (functions := functions) (cells := cells)
      (receiving := registry) (anchor := anchor) session mapping world before store caller entries) :
    ∃ requiredOutput,
      ∀ executionFuel outputFuel (outcome : SourceCoreExecution.Outcome publicArtifact),
        requiredExecution ≤ executionFuel → requiredOutput ≤ outputFuel →
        publicCheckpoint.ResumeAt executionFuel outputFuel outcome →
        ∃ (completion : SourceCoreExecution.Completion publicArtifact) (actual : Completion artifact)
          (generation : SourceCorePublicValues.ExportGeneration)
          (reached : Caller headers keys finalMap finalWorld after finalStore),
          outcome = .succeeded completion ∧
          checkpoint.SucceededResultAt executionFuel outputFuel generation native finalStore actual ∧
          completion.IndexedAt actual ∧ Relates caller reached ∧
          CellAwarePublicPhysicalHistory.History (functions := functions) (cells := cells)
            (receiving := registry) (anchor := anchor)
            actual.session finalMap finalWorld after finalStore reached entries ∧
          actual.session.RegistryAt registry ∧ actual.session.ExportsReady := by
  obtain ⟨_payload, requiredOutput, _nativeEq, _represented, exported⟩ :=
    exports functions cells started exactRegistry resultView ready atCheckpoint result completes
  refine ⟨requiredOutput, ?_⟩
  intro executionFuel outputFuel outcome enough outputEnough resumed
  obtain ⟨completion, actual, generation, succeeded, actualResult, actualAt, returnedReady⟩ :=
    exported executionFuel outputFuel outcome enough outputEnough resumed
  obtain ⟨reached, related, retained⟩ := history.semantic.after_packed_success started.original actualResult result
  exact ⟨completion, actual, generation, reached, succeeded, actualResult, actualAt, related,
    ⟨retained, history.physical.extend result.2.2.2.2.1⟩,
    exactRegistry.symm ▸ started.returned_registry actualResult, returnedReady⟩

end Solcore.SourceSemantics.CoreLowering.CellAwarePublicDirectOutput
