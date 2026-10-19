import Solcore.SourceSemantics.CoreLowering.CellAwarePublicPhysicalHistory
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicActualRegistryNamedOutputPreservation

/-! Successful named execution derives public output fuel from its represented
value. The exact returned session retains mixed cells, physical cache authority,
and all earlier exported function values. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwarePublicNamedOutput
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
  {requiredExecution : Nat}
  (completes : ∀ executionFuel, requiredExecution ≤ executionFuel → checkpoint.NativeDone executionFuel native finalStore)

include selected started exactRegistry ready atCheckpoint result completes in
theorem exports :
    ∃ payload requiredOutput,
      native = .inRight .word payload ∧
      ValueRep recipe.compiled.compatible.checked registry functions finalMap finalWorld
        header.function.resultType source payload header.output ∧
      ∀ executionFuel outputFuel (outcome : SourceCoreExecution.Outcome publicArtifact),
        requiredExecution ≤ executionFuel → requiredOutput ≤ outputFuel →
        publicCheckpoint.ResumeAt executionFuel outputFuel outcome →
        ∃ (completion : SourceCoreExecution.Completion publicArtifact) (actual : Completion artifact)
          (generation : SourceCorePublicValues.ExportGeneration),
          outcome = .succeeded completion ∧
          checkpoint.SucceededResultAt executionFuel outputFuel generation native finalStore actual ∧
          completion.IndexedAt actual ∧ actual.session.ExportsReady := by
  obtain ⟨payload, same⟩ : ∃ payload, native = .inRight .word payload := by
    have represented := result.2.1
    cases represented with
    | value _ => exact ⟨_, rfl⟩
  subst native
  have represented : ValueRep recipe.compiled.compatible.checked registry functions finalMap finalWorld
      header.function.resultType source payload header.output := by
    have related := result.2.1
    cases related with
    | value represented => exact represented
  have shape : SourceCorePublicOutputShapes.Output recipe.compiled.compatible.checked encodedValues.registry
      (finalStore.map Core.Value.type) recipe.program.layouts.definitions header.function.resultType payload := by
    have shaped := CompatiblePublicOutputShapes.ValueRep.output represented
    rw [exactRegistry, result.2.2.1.runtime_hasTypes.world_eq] at shaped
    exact shaped
  have checkpointRegistry : checkpoint.RegistryAt encodedValues.registry := by
    have values := started.values
    cases checkpoint
    change _ = encodedValues at values
    exact congrArg SourceCoreCompatibleValues.Context.registry values
  have atRecipe : artifact.RecipeAt recipe := by cases artifact; exact started.recipe_eq
  have requested := started.original.result_type_at atRecipe started.selected
  have resultType := (RecursiveNamedPublicRootSourceSignature.inputs_and_result selected).2
  rw [resultType] at requested
  have checkpointReady := started.original.initial_registry.exportsReady ready
  obtain ⟨requiredOutput, exported⟩ := publicCheckpoint.output_succeeded_uniform
    atCheckpoint atRecipe checkpointRegistry checkpointReady requested shape
  exact ⟨payload, requiredOutput, rfl, represented, fun executionFuel outputFuel outcome enough outputEnough resumed =>
    exported executionFuel (completes executionFuel enough) outputFuel outputEnough outcome resumed⟩

include selected started exactRegistry ready atCheckpoint result completes in
/-- A first successful public call produces a reusable physical history at
the actual returned mixed heap; no output success is assumed. -/
theorem first_success
    (physical : CallableIndexedOwnedPhysicalGlobals.Authority recipe.compiled mapping store) :
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
            actual.session finalMap finalWorld after finalStore reached [] ∧
          actual.session.RegistryAt registry ∧ actual.session.ExportsReady := by
  obtain ⟨_payload, requiredOutput, _nativeEq, _represented, exported⟩ :=
    exports functions cells selected started exactRegistry ready atCheckpoint result completes
  refine ⟨requiredOutput, ?_⟩
  intro executionFuel outputFuel outcome enough outputEnough resumed
  obtain ⟨completion, actual, generation, succeeded, actualResult, actualAt, returnedReady⟩ :=
    exported executionFuel outputFuel outcome enough outputEnough resumed
  obtain ⟨reached, related, history⟩ := CellAwarePublicFunctionHistory.first_success
    rfl started selected actualResult result
  have retained : CellAwarePublicPhysicalHistory.History (functions := functions) (cells := cells)
      (receiving := registry) (anchor := anchor) actual.session finalMap finalWorld after finalStore reached [] :=
    ⟨history, CellAwarePublicPhysicalHistory.physical_of_result physical result⟩
  exact ⟨completion, actual, generation, reached, succeeded, actualResult, actualAt, related,
    retained, exactRegistry.symm ▸ started.returned_registry actualResult, returnedReady⟩

include selected started exactRegistry ready atCheckpoint result completes in
/-- Following calls preserve earlier handle entries at the exact public
return and retain the full physical cache after all body effects. -/
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
    exports functions cells selected started exactRegistry ready atCheckpoint result completes
  refine ⟨requiredOutput, ?_⟩
  intro executionFuel outputFuel outcome enough outputEnough resumed
  obtain ⟨completion, actual, generation, succeeded, actualResult, actualAt, returnedReady⟩ :=
    exported executionFuel outputFuel outcome enough outputEnough resumed
  obtain ⟨reached, related, retained⟩ := history.semantic.after_success rfl started selected actualResult result
  exact ⟨completion, actual, generation, reached, succeeded, actualResult, actualAt, related,
    history.after_result result retained, exactRegistry.symm ▸ started.returned_registry actualResult, returnedReady⟩

end Solcore.SourceSemantics.CoreLowering.CellAwarePublicNamedOutput
