import Solcore.SourceSemantics.CoreLowering.CellAwarePublicPhysicalHistory
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicDirectPackedInputMeaning
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicActualRegistryFailures
import Solcore.Core.ExactFuelProperties
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicReturnedInputRegistry

/-! A direct handle call retains its actual mixed heap and prior public history.
The original requested signature and output codec determine public completion. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwarePublicDirectFailure
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
  {failure : Staging.Recursive.Failure} {after : Dynamic.Heap} {native : Core.Value} {finalStore : Store}
  {finalMap : LocationMap} {finalWorld : StoreTyping} {faults : RecursiveStageMeaning.FaultRep}
  (result : ResultAt (registry := registry) functions cells caller anchor.function.context sourceResult nativeResult
    (.fault failure) after native finalStore finalMap finalWorld faults)
  {requiredExecution : Nat}
  (completes : ∀ executionFuel, requiredExecution ≤ executionFuel → checkpoint.NativeDone executionFuel native finalStore)

include started exactRegistry ready atCheckpoint result completes in
theorem failed :
    ∃ token, faults failure token ∧
      ∀ executionFuel outputFuel (outcome : SourceCoreExecution.Outcome publicArtifact),
        requiredExecution ≤ executionFuel →
        publicCheckpoint.ResumeAt executionFuel outputFuel outcome →
        ∃ (returned : SourceCoreExecution.Session publicArtifact) (actual : Session artifact),
          outcome = .failed token returned ∧
          checkpoint.FailedResultAt executionFuel native finalStore token actual ∧
          returned.IndexedAt actual ∧ actual.RegistryAt registry ∧ actual.ExportsReady := by
  obtain ⟨token, nativeEq, represented⟩ : ∃ token,
      native = .inLeft nativeResult (.word token) ∧ faults failure token := by
    have related := result.1
    cases related with
    | fault represented => exact ⟨_, rfl, represented⟩
  have checkpointReady := started.original.initial_registry.exportsReady ready
  refine ⟨token, represented, ?_⟩
  intro executionFuel outputFuel outcome enough resumed
  have completed := completes executionFuel enough
  obtain ⟨returned, outcomeEq⟩ := resumed.native_failed atCheckpoint completed (by rw [nativeEq]; rfl)
  have failedResume : publicCheckpoint.ResumeAt executionFuel outputFuel (.failed token returned) := outcomeEq ▸ resumed
  obtain ⟨actual, _generation, actualValue, actualStore, actualCompleted, failedAt, returnedAt⟩ :=
    failedResume.indexed_failed atCheckpoint
  have same := completed.symm.trans actualCompleted
  cases same
  have returnedRegistry : actual.RegistryAt registry := by
    rw [exactRegistry]
    exact congrArg SourceCoreCompatibleValues.Context.registry (failedAt.2.2.2.2.1.trans started.values)
  exact ⟨returned, actual, outcomeEq, failedAt, returnedAt, returnedRegistry, failedAt.exportsReady checkpointReady⟩

include started exactRegistry ready atCheckpoint result completes in
theorem after_failure {entries : List Entry}
    (heapTyped : Dynamic.HeapWellTyped anchor.function.context after)
    (history : CellAwarePublicPhysicalHistory.History (functions := functions) (cells := cells)
      (receiving := registry) (anchor := anchor) session mapping world before store caller entries) :
    ∃ token, faults failure token ∧
      ∀ executionFuel outputFuel (outcome : SourceCoreExecution.Outcome publicArtifact),
        requiredExecution ≤ executionFuel →
        publicCheckpoint.ResumeAt executionFuel outputFuel outcome →
        ∃ (returned : SourceCoreExecution.Session publicArtifact) (actual : Session artifact)
          (reached : Caller headers keys finalMap finalWorld after finalStore),
          outcome = .failed token returned ∧
          checkpoint.FailedResultAt executionFuel native finalStore token actual ∧
          returned.IndexedAt actual ∧ Relates caller reached ∧
          CellAwarePublicPhysicalHistory.History (functions := functions) (cells := cells)
            (receiving := registry) (anchor := anchor)
            actual finalMap finalWorld after finalStore reached entries ∧
          actual.RegistryAt registry ∧ returned.ExportsReady := by
  obtain ⟨token, represented, output⟩ :=
    failed functions cells started exactRegistry ready atCheckpoint result completes
  refine ⟨token, represented, ?_⟩
  intro executionFuel outputFuel outcome enough resumed
  obtain ⟨returned, actual, failedOutcome, actualResult, actualAt, registryAt, actualReady⟩ :=
    output executionFuel outputFuel outcome enough resumed
  obtain ⟨reached, related, retained⟩ := history.semantic.after_packed_failure
    started.original actualResult result heapTyped
  exact ⟨returned, actual, reached, failedOutcome, actualResult, actualAt, related,
    ⟨retained, history.physical.extend result.2.2.2.2.1⟩, registryAt, actualAt.exportsReady_iff.mpr actualReady⟩


include started exactRegistry ready atCheckpoint result in
/-- An observed failed direct call retains the exact Source-derived final heap
and every earlier handle even if the observer used a different execution budget. -/
theorem observed_failure {entries : List Entry}
    (history : CellAwarePublicPhysicalHistory.History (functions := functions) (cells := cells)
      (receiving := registry) (anchor := anchor) session mapping world before store caller entries)
    (heapTyped : Dynamic.HeapWellTyped anchor.function.context after)
    {proofFuel executionFuel outputFuel : Nat}
    (completed : checkpoint.NativeDone proofFuel native finalStore)
    {token : Word} {returned : SourceCoreExecution.Session publicArtifact}
    (resumed : publicCheckpoint.ResumeAt executionFuel outputFuel (.failed token returned)) :
    faults failure token ∧
    ∃ (actual : Session artifact) (reached : Caller headers keys finalMap finalWorld after finalStore),
      checkpoint.FailedResultAt executionFuel native finalStore token actual ∧
      returned.IndexedAt actual ∧ Relates caller reached ∧
      CellAwarePublicPhysicalHistory.History (functions := functions) (cells := cells)
        (receiving := registry) (anchor := anchor)
        actual finalMap finalWorld after finalStore reached entries ∧
      actual.RegistryAt registry ∧ returned.ExportsReady := by
  obtain ⟨actual, _generation, observed, observedStore, done, failedAt, returnedAt⟩ :=
    resumed.indexed_failed atCheckpoint
  obtain ⟨_leftSteps, _leftEnough, left⟩ := runStateful_sound completed
  obtain ⟨_rightSteps, _rightEnough, right⟩ := runStateful_sound done
  obtain ⟨_steps, sameValue, sameStore⟩ := left.final_unique right
  cases sameValue
  cases sameStore
  have tokenAt : faults failure token := by
    have represented := result.1
    have decoded := failedAt.2.1
    cases represented with
    | fault represented =>
        simp only [LanguageResult.decode?, Option.some.injEq, LanguageResult.Outcome.failed.injEq] at decoded
        subst token
        exact represented
  obtain ⟨reached, related, retained⟩ := history.semantic.after_packed_failure
    started.original failedAt result heapTyped
  have checkpointReady := started.original.initial_registry.exportsReady ready
  have returnedRegistry : actual.RegistryAt registry := by
    rw [exactRegistry]
    exact congrArg SourceCoreCompatibleValues.Context.registry (failedAt.2.2.2.2.1.trans started.values)
  exact ⟨tokenAt, actual, reached, failedAt, returnedAt, related,
    ⟨retained, history.physical.extend result.2.2.2.2.1⟩, returnedRegistry,
    returnedAt.exportsReady_iff.mpr (failedAt.exportsReady checkpointReady)⟩

end Solcore.SourceSemantics.CoreLowering.CellAwarePublicDirectFailure
