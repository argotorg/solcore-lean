import Solcore.SourceSemantics.CoreLowering.CellAwarePublicNamedOutput

/-! Public output fuel and actual export receipts retain returned function
leaves for later calls, including functions nested in products. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwarePublicNamedCollection
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
/-- The first real output export collects selected function leaves, including
leaves inside products, at the exact returned heap and public session. -/
theorem first_collected
    (physical : CallableIndexedOwnedPhysicalGlobals.Authority recipe.compiled mapping store) :
    ∃ requiredOutput,
      ∀ executionFuel outputFuel (outcome : SourceCoreExecution.Outcome publicArtifact),
        requiredExecution ≤ executionFuel → requiredOutput ≤ outputFuel →
        publicCheckpoint.ResumeAt executionFuel outputFuel outcome →
        ∃ (completion : SourceCoreExecution.Completion publicArtifact) (actual : Completion artifact)
          (generation : SourceCorePublicValues.ExportGeneration),
          outcome = .succeeded completion ∧
          checkpoint.SucceededResultAt executionFuel outputFuel generation native finalStore actual ∧
          completion.IndexedAt actual ∧ actual.session.RegistryAt registry ∧ actual.session.ExportsReady ∧
          ∀ selection : RecursiveNamedPublicOutputSelections.Selection header.function.resultType actual.value,
            ∃ (reached : Caller headers keys finalMap finalWorld after finalStore) (added : List Entry),
              added.map Entry.handle = selection.handles ∧ Relates caller reached ∧
              CellAwarePublicPhysicalHistory.History (functions := functions) (cells := cells)
                (receiving := registry) (anchor := anchor)
                actual.session finalMap finalWorld after finalStore reached added := by
  obtain ⟨_payload, requiredOutput, _nativeEq, _represented, exported⟩ :=
    CellAwarePublicNamedOutput.exports functions cells selected started exactRegistry ready atCheckpoint result completes
  refine ⟨requiredOutput, ?_⟩
  intro executionFuel outputFuel outcome enough outputEnough resumed
  obtain ⟨completion, actual, generation, succeeded, actualResult, actualAt, returnedReady⟩ :=
    exported executionFuel outputFuel outcome enough outputEnough resumed
  refine ⟨completion, actual, generation, succeeded, actualResult, actualAt,
    exactRegistry.symm ▸ started.returned_registry actualResult, returnedReady, ?_⟩
  intro selection
  have atRecipe : artifact.RecipeAt recipe := by cases artifact; exact started.recipe_eq
  have requested := started.original.result_type_at atRecipe started.selected
  rw [(RecursiveNamedPublicRootSourceSignature.inputs_and_result selected).2] at requested
  obtain ⟨reached, added, handles, related, history⟩ :=
    CellAwarePublicFunctionHistory.first_collected rfl started selected requested actualResult result selection
  exact ⟨reached, added, handles, related,
    ⟨history, CellAwarePublicPhysicalHistory.physical_of_result physical result⟩⟩

include selected started exactRegistry ready atCheckpoint result completes in
/-- Later public outputs append selected leaves to the complete prior history;
intervening named calls retain the same captured locations in the reached heap. -/
theorem after_collected {entries : List Entry}
    (history : CellAwarePublicPhysicalHistory.History (functions := functions) (cells := cells)
      (receiving := registry) (anchor := anchor) session mapping world before store caller entries) :
    ∃ requiredOutput,
      ∀ executionFuel outputFuel (outcome : SourceCoreExecution.Outcome publicArtifact),
        requiredExecution ≤ executionFuel → requiredOutput ≤ outputFuel →
        publicCheckpoint.ResumeAt executionFuel outputFuel outcome →
        ∃ (completion : SourceCoreExecution.Completion publicArtifact) (actual : Completion artifact)
          (generation : SourceCorePublicValues.ExportGeneration),
          outcome = .succeeded completion ∧
          checkpoint.SucceededResultAt executionFuel outputFuel generation native finalStore actual ∧
          completion.IndexedAt actual ∧ actual.session.RegistryAt registry ∧ actual.session.ExportsReady ∧
          ∀ selection : RecursiveNamedPublicOutputSelections.Selection header.function.resultType actual.value,
            ∃ (reached : Caller headers keys finalMap finalWorld after finalStore) (added : List Entry),
              added.map Entry.handle = selection.handles ∧ Relates caller reached ∧
              CellAwarePublicPhysicalHistory.History (functions := functions) (cells := cells)
                (receiving := registry) (anchor := anchor)
                actual.session finalMap finalWorld after finalStore reached (entries ++ added) := by
  obtain ⟨_payload, requiredOutput, _nativeEq, _represented, exported⟩ :=
    CellAwarePublicNamedOutput.exports functions cells selected started exactRegistry ready atCheckpoint result completes
  refine ⟨requiredOutput, ?_⟩
  intro executionFuel outputFuel outcome enough outputEnough resumed
  obtain ⟨completion, actual, generation, succeeded, actualResult, actualAt, returnedReady⟩ :=
    exported executionFuel outputFuel outcome enough outputEnough resumed
  refine ⟨completion, actual, generation, succeeded, actualResult, actualAt,
    exactRegistry.symm ▸ started.returned_registry actualResult, returnedReady, ?_⟩
  intro selection
  have atRecipe : artifact.RecipeAt recipe := by cases artifact; exact started.recipe_eq
  have requested := started.original.result_type_at atRecipe started.selected
  rw [(RecursiveNamedPublicRootSourceSignature.inputs_and_result selected).2] at requested
  obtain ⟨reached, added, handles, related, retained⟩ :=
    history.semantic.collect_success rfl started selected requested actualResult result selection
  exact ⟨reached, added, handles, related, history.after_result result retained⟩

end Solcore.SourceSemantics.CoreLowering.CellAwarePublicNamedCollection
