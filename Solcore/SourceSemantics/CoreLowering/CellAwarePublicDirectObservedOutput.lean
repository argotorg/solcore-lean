import Solcore.SourceSemantics.CoreLowering.CellAwarePublicPhysicalHistory
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicDirectPackedInputMeaning
import Solcore.Core.ExactFuelProperties
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicReturnedInputRegistry

/-! A direct handle call retains its actual mixed heap and prior public history.
The original requested signature and output codec determine public completion. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwarePublicDirectObservedOutput
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
  (ready : session.ExportsReady)
  {publicArtifact : SourceCoreExecution.Artifact} {publicCheckpoint : SourceCoreExecution.Checkpoint publicArtifact}
  (atCheckpoint : publicCheckpoint.IndexedAt checkpoint)
  {outcome : Staging.Recursive.Outcome} {after : Dynamic.Heap} {native : Core.Value} {finalStore : Store}
  {finalMap : LocationMap} {finalWorld : StoreTyping} {faults : RecursiveStageMeaning.FaultRep}
  (result : ResultAt (registry := registry) functions cells caller anchor.function.context sourceResult nativeResult
    outcome after native finalStore finalMap finalWorld faults)

variable {proofFuel executionFuel outputFuel : Nat}
  (completed : checkpoint.NativeDone proofFuel native finalStore)
  {completion : SourceCoreExecution.Completion publicArtifact}
  (resumed : publicCheckpoint.ResumeAt executionFuel outputFuel (.succeeded completion))

include atCheckpoint completed resumed in
/-- Native determinism identifies the Source-derived value and heap with the
actual observed public completion, regardless of the proof's fuel budget. -/
theorem actual_result :
    ∃ (actual : Completion artifact) (generation : SourceCorePublicValues.ExportGeneration),
      checkpoint.SucceededResultAt executionFuel outputFuel generation native finalStore actual ∧
      completion.IndexedAt actual := by
  obtain ⟨actual, generation, observed, observedStore, done, exported, atReturned⟩ :=
    resumed.indexed_succeeded atCheckpoint
  obtain ⟨_leftSteps, _leftEnough, left⟩ := runStateful_sound completed
  obtain ⟨_rightSteps, _rightEnough, right⟩ := runStateful_sound done
  obtain ⟨_steps, sameValue, sameStore⟩ := left.final_unique right
  cases sameValue
  cases sameStore
  exact ⟨actual, generation, exported, atReturned⟩

include started exactRegistry ready atCheckpoint result completed resumed in
theorem after_success {entries : List Entry}
    (history : CellAwarePublicPhysicalHistory.History (functions := functions) (cells := cells)
      (receiving := registry) (anchor := anchor) session mapping world before store caller entries) :
    ∃ (actual : Completion artifact) (generation : SourceCorePublicValues.ExportGeneration)
      (reached : Caller headers keys finalMap finalWorld after finalStore),
      checkpoint.SucceededResultAt executionFuel outputFuel generation native finalStore actual ∧
      completion.IndexedAt actual ∧ Relates caller reached ∧
      CellAwarePublicPhysicalHistory.History (functions := functions) (cells := cells)
        (receiving := registry) (anchor := anchor)
        actual.session finalMap finalWorld after finalStore reached entries ∧
      actual.session.RegistryAt registry ∧ actual.session.ExportsReady := by
  obtain ⟨actual, generation, exported, atReturned⟩ := actual_result atCheckpoint completed resumed
  obtain ⟨reached, related, retained⟩ := history.semantic.after_packed_success started.original exported result
  exact ⟨actual, generation, reached, exported, atReturned, related,
    ⟨retained, history.physical.extend result.2.2.2.2.1⟩,
    exactRegistry.symm ▸ started.returned_registry exported,
    exported.exportsReady (started.original.initial_registry.exportsReady ready)⟩

end Solcore.SourceSemantics.CoreLowering.CellAwarePublicDirectObservedOutput
