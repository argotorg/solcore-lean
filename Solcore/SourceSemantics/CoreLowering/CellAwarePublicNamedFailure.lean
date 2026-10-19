import Solcore.SourceSemantics.CoreLowering.CellAwarePublicPhysicalHistory
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicActualRegistryFailures

/-! Actual fault results determine the public failed session and preserve its
reached mixed heap, physical cache and retained function history. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwarePublicNamedFailure
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open SourceCoreIndexedSession CallableIndexedOwnedFunctionState
open CallableIndexedOwnedFunctionValues (Header NamedCapture OwnedKey)
open CellAwarePublicFunctionHistory (Caller Result)
open RecursiveNamedPublicFunctionHistory (Entry)

variable {recipe : Recipe}
  {headers : List (Header recipe.compiled (Program.ofChecked recipe.compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key recipe.compiled (Program.ofChecked recipe.compiled.sourceProgram))}
  (functions : FunctionModel recipe.compiled.compatible.checked.catalog
    (CallableIndexedAmbient.ambientDefinitions recipe.compiled.indexed))
  (cells : GenericHeap.CellModel (CallableIndexedAmbient.ambientDefinitions recipe.compiled.indexed).definitions)
  {registry : SourceCoreRawMetadata.Registry}
  {anchor header : Header recipe.compiled (Program.ofChecked recipe.compiled.sourceProgram)}
  {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store : Store}
  {owner : OwnedKey keys} {caller : Caller headers keys mapping world before store}
  {capture : NamedCapture headers owner.key header mapping world} {arguments : List Core.Value}
  {root : Root recipe.compiled}
  (selected : RecursiveNamedPublicRootMeaning.RootSelection
    (values := .initial recipe.compiled.compatible.checked)
    (ambient := CallableIndexedAmbient.ambientDefinitions recipe.compiled.indexed)
    (program := Program.ofChecked recipe.compiled.sourceProgram) headers root header)
  {artifact : Artifact} {session : Session artifact} {checkpoint : Checkpoint artifact}
  {key : SourceCoreIndexedSession.Key} {publicArguments : List SourceCorePublicValues.Value}
  {inputFuel : Nat} {encodedValues : SourceCoreCompatibleValues.Context}
  (started : RecursiveNamedPublicStartMeaning.StartAt session key publicArguments inputFuel checkpoint
    recipe root world store arguments encodedValues)
  (exactRegistry : registry = encodedValues.registry)
  (ready : session.ExportsReady)
  {publicArtifact : SourceCoreExecution.Artifact} {publicCheckpoint : SourceCoreExecution.Checkpoint publicArtifact}
  (atCheckpoint : publicCheckpoint.IndexedAt checkpoint)
  {failure : Staging.Recursive.Failure} {after : Dynamic.Heap} {native : Core.Value} {finalStore : Store}
  {finalMap : LocationMap} {finalWorld : StoreTyping} {faults : RecursiveStageMeaning.FaultRep}
  (heapTyped : Dynamic.HeapWellTyped anchor.function.context after)
  (result : Result (cells := cells) (functions := functions) (receiving := registry) (anchor := anchor)
    owner caller header capture arguments (.fault failure) after native finalStore finalMap finalWorld faults)
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
      native = .inLeft header.output (.word token) ∧ faults failure token := by
    have related := result.2.1
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

include selected started exactRegistry ready atCheckpoint heapTyped result completes in
theorem first_failure
    (physical : CallableIndexedOwnedPhysicalGlobals.Authority recipe.compiled mapping store) :
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
            actual finalMap finalWorld after finalStore reached [] ∧
          actual.RegistryAt registry ∧ returned.ExportsReady := by
  obtain ⟨token, represented, output⟩ :=
    failed functions cells started exactRegistry ready atCheckpoint result completes
  refine ⟨token, represented, ?_⟩
  intro executionFuel outputFuel outcome enough resumed
  obtain ⟨returned, actual, failedOutcome, actualResult, actualAt, registryAt, actualReady⟩ :=
    output executionFuel outputFuel outcome enough resumed
  obtain ⟨reached, related, history⟩ := CellAwarePublicFunctionHistory.first_failure
    rfl started selected actualResult result heapTyped
  exact ⟨returned, actual, reached, failedOutcome, actualResult, actualAt, related,
    ⟨history, CellAwarePublicPhysicalHistory.physical_of_result physical result⟩,
    registryAt, actualAt.exportsReady_iff.mpr actualReady⟩

include selected started exactRegistry ready atCheckpoint heapTyped result completes in
theorem after_failure {entries : List Entry}
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
  obtain ⟨reached, related, retained⟩ := history.semantic.after_failure
    rfl started selected actualResult result heapTyped
  exact ⟨returned, actual, reached, failedOutcome, actualResult, actualAt, related,
    history.after_result result retained, registryAt, actualAt.exportsReady_iff.mpr actualReady⟩

end Solcore.SourceSemantics.CoreLowering.CellAwarePublicNamedFailure
