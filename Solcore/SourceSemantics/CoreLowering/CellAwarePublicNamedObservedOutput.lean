import Solcore.Core.ExactFuelProperties
import Solcore.SourceSemantics.CoreLowering.CellAwarePublicPhysicalHistory
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicActualRegistryNamedOutputPreservation

/-! Actual public success consumes the independent Source-derived native result
without assuming a numerical fuel bound for that observed completion. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwarePublicNamedObservedOutput
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
  {source : Dynamic.Value} {after : Dynamic.Heap} {native : Core.Value} {finalStore : Store}
  {finalMap : LocationMap} {finalWorld : StoreTyping} {faults : RecursiveStageMeaning.FaultRep}
  (result : Result (cells := cells) (functions := functions) (receiving := registry) (anchor := anchor)
    owner caller header capture arguments (.value source) after native finalStore finalMap finalWorld faults)

variable {proofFuel executionFuel outputFuel : Nat}
  (completed : checkpoint.NativeDone proofFuel native finalStore)
  {completion : SourceCoreExecution.Completion publicArtifact}
  (resumed : publicCheckpoint.ResumeAt executionFuel outputFuel (.succeeded completion))

include atCheckpoint completed resumed in
/-- Different fuel budgets for the same checkpoint cannot change a completed
value or store. The export receipt belongs to the actual observed resume. -/
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

include selected started exactRegistry ready atCheckpoint result completed resumed in
/-- An observed first success retains the exact Source-derived heap and
physical history, even when the observer did not know its sufficient fuel. -/
theorem first_success
    (physical : CallableIndexedOwnedPhysicalGlobals.Authority recipe.compiled mapping store) :
    ∃ (actual : Completion artifact) (generation : SourceCorePublicValues.ExportGeneration)
      (reached : Caller headers keys finalMap finalWorld after finalStore),
      checkpoint.SucceededResultAt executionFuel outputFuel generation native finalStore actual ∧
      completion.IndexedAt actual ∧ Relates caller reached ∧
      CellAwarePublicPhysicalHistory.History (functions := functions) (cells := cells)
        (receiving := registry) (anchor := anchor)
        actual.session finalMap finalWorld after finalStore reached [] ∧
      actual.session.RegistryAt registry ∧ actual.session.ExportsReady := by
  obtain ⟨actual, generation, exported, atReturned⟩ := actual_result atCheckpoint completed resumed
  obtain ⟨reached, related, history⟩ :=
    CellAwarePublicFunctionHistory.first_success rfl started selected exported result
  exact ⟨actual, generation, reached, exported, atReturned, related,
    ⟨history, CellAwarePublicPhysicalHistory.physical_of_result physical result⟩,
    exactRegistry.symm ▸ started.returned_registry exported,
    exported.exportsReady (started.original.initial_registry.exportsReady ready)⟩

include selected started exactRegistry ready atCheckpoint result completed resumed in
/-- An observed later success preserves every earlier function handle and its
captures at the Source-derived heap reached by this invocation. -/
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
  obtain ⟨reached, related, retained⟩ := history.semantic.after_success rfl started selected exported result
  exact ⟨actual, generation, reached, exported, atReturned, related,
    history.after_result result retained, exactRegistry.symm ▸ started.returned_registry exported,
    exported.exportsReady (started.original.initial_registry.exportsReady ready)⟩

end Solcore.SourceSemantics.CoreLowering.CellAwarePublicNamedObservedOutput
