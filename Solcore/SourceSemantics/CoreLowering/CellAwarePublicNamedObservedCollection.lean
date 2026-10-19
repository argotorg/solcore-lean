import Solcore.SourceSemantics.CoreLowering.CellAwarePublicNamedObservedOutput

/-! Actual public success consumes the independent Source-derived native result
without assuming a numerical fuel bound for that observed completion. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwarePublicNamedObservedCollection
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

include result in
private theorem selected_addition
    {actual : Completion artifact} {generation : SourceCorePublicValues.ExportGeneration}
    (requested : checkpoint.ResultTypeAt header.function.resultType)
    (exported : checkpoint.SucceededResultAt executionFuel outputFuel generation native finalStore actual)
    (selection : RecursiveNamedPublicOutputSelections.Selection header.function.resultType actual.value) :
    ∃ (payload : Core.Value) (added : List Entry),
      native = .inRight .word payload ∧
      RecursiveNamedPublicOutputSelections.Selected selection source payload header.output outputFuel added ∧
      added.map Entry.handle = selection.handles ∧
      RecursiveNamedPublicFunctionHistory.Addition (checked := recipe.compiled.compatible.checked)
        checkpoint actual outputFuel header.function.resultType header.output (.value source) native added := by
  obtain ⟨payload, decoded, _imported⟩ := exported.reimports
  obtain ⟨_sourceType, imported⟩ := exported.reimports_payload requested decoded
  obtain ⟨actualSource, actualOutcome, represented, _heaps, _world, _returned, _related, _stable, _typed, valueTyped⟩ :=
    CellAwarePublicApplicationResult.named_returned_value result decoded
  have same : source = actualSource := Staging.Recursive.Outcome.value.inj actualOutcome
  subst actualSource
  obtain ⟨encoded, encodedAt, payloadAt⟩ := imported
  obtain ⟨added, selected, handles, _meanings⟩ := selection.collect represented valueTyped encodedAt rfl payloadAt
  have nativeValue : native = .inRight .word payload := by
    cases result.2.1 with
    | value represented =>
        simp only [LanguageResult.decode?, Option.some.injEq, LanguageResult.Outcome.succeeded.injEq] at decoded
        exact congrArg (Core.Value.inRight .word) decoded
  exact ⟨payload, added, nativeValue, selected, handles, .select requested rfl nativeValue selection selected⟩

include selected started exactRegistry ready atCheckpoint result completed resumed in
/-- The actual export receipt collects all requested function leaves at the
Source-derived returned heap, without guessing a numeric sufficient budget. -/
theorem first_collected
    (physical : CallableIndexedOwnedPhysicalGlobals.Authority recipe.compiled mapping store) :
    ∃ (actual : Completion artifact) (generation : SourceCorePublicValues.ExportGeneration),
      checkpoint.SucceededResultAt executionFuel outputFuel generation native finalStore actual ∧
      completion.IndexedAt actual ∧ actual.session.RegistryAt registry ∧ actual.session.ExportsReady ∧
      ∀ selection : RecursiveNamedPublicOutputSelections.Selection header.function.resultType actual.value,
        ∃ (reached : Caller headers keys finalMap finalWorld after finalStore) (payload : Core.Value) (added : List Entry),
          native = .inRight .word payload ∧
          RecursiveNamedPublicOutputSelections.Selected selection source payload header.output outputFuel added ∧
          added.map Entry.handle = selection.handles ∧ Relates caller reached ∧
          CellAwarePublicPhysicalHistory.History (functions := functions) (cells := cells)
            (receiving := registry) (anchor := anchor)
            actual.session finalMap finalWorld after finalStore reached added := by
  obtain ⟨actual, generation, exported, atReturned⟩ :=
    CellAwarePublicNamedObservedOutput.actual_result atCheckpoint completed resumed
  refine ⟨actual,generation,exported,atReturned,
    exactRegistry.symm ▸ started.returned_registry exported,
    exported.exportsReady (started.original.initial_registry.exportsReady ready),?_⟩
  intro selection
  have atRecipe : artifact.RecipeAt recipe := by cases artifact; exact started.recipe_eq
  have requested := started.original.result_type_at atRecipe started.selected
  rw [(RecursiveNamedPublicRootSourceSignature.inputs_and_result selected).2] at requested
  obtain ⟨payload,added,nativeValue,selectedLeaves,handles,addition⟩ :=
    selected_addition functions cells result requested exported selection
  obtain ⟨reached,related,post⟩ := result.2.2.2.2.2.2.2
  exact ⟨reached,payload,added,nativeValue,selectedLeaves,handles,related,
    ⟨.first rfl started selected exported result reached ⟨related,post⟩ addition,
      CellAwarePublicPhysicalHistory.physical_of_result physical result⟩⟩

include selected started exactRegistry ready atCheckpoint result completed resumed in
/-- Later observed output appends its selected function leaves while retaining
all previous entries and the exact current Source/native heap. -/
theorem after_collected {entries : List Entry}
    (history : CellAwarePublicPhysicalHistory.History (functions := functions) (cells := cells)
      (receiving := registry) (anchor := anchor) session mapping world before store caller entries) :
    ∃ (actual : Completion artifact) (generation : SourceCorePublicValues.ExportGeneration),
      checkpoint.SucceededResultAt executionFuel outputFuel generation native finalStore actual ∧
      completion.IndexedAt actual ∧ actual.session.RegistryAt registry ∧ actual.session.ExportsReady ∧
      ∀ selection : RecursiveNamedPublicOutputSelections.Selection header.function.resultType actual.value,
        ∃ (reached : Caller headers keys finalMap finalWorld after finalStore) (payload : Core.Value) (added : List Entry),
          native = .inRight .word payload ∧
          RecursiveNamedPublicOutputSelections.Selected selection source payload header.output outputFuel added ∧
          added.map Entry.handle = selection.handles ∧ Relates caller reached ∧
          CellAwarePublicPhysicalHistory.History (functions := functions) (cells := cells)
            (receiving := registry) (anchor := anchor)
            actual.session finalMap finalWorld after finalStore reached (entries ++ added) := by
  obtain ⟨actual,generation,exported,atReturned⟩ :=
    CellAwarePublicNamedObservedOutput.actual_result atCheckpoint completed resumed
  refine ⟨actual,generation,exported,atReturned,
    exactRegistry.symm ▸ started.returned_registry exported,
    exported.exportsReady (started.original.initial_registry.exportsReady ready),?_⟩
  intro selection
  have atRecipe : artifact.RecipeAt recipe := by cases artifact; exact started.recipe_eq
  have requested := started.original.result_type_at atRecipe started.selected
  rw [(RecursiveNamedPublicRootSourceSignature.inputs_and_result selected).2] at requested
  obtain ⟨payload,added,nativeValue,selectedLeaves,handles,addition⟩ :=
    selected_addition functions cells result requested exported selection
  obtain ⟨reached,related,post⟩ := result.2.2.2.2.2.2.2
  have retained := CellAwarePublicFunctionHistory.History.next history.semantic rfl started selected exported
    result reached ⟨related,post⟩ addition
  exact ⟨reached,payload,added,nativeValue,selectedLeaves,handles,related,history.after_result result retained⟩

end Solcore.SourceSemantics.CoreLowering.CellAwarePublicNamedObservedCollection
