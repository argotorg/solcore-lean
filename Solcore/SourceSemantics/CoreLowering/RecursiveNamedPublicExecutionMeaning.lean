import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicRuntimeMeaning
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPreparedStageContracts
import Solcore.SourceSemantics.CoreLowering.CompatiblePlaceModifier
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicRootSourceSignature

/-! Actual public facade startup and returned outcomes retain the same indexed
checkpoint and export receipt. The existing static catalog profiles, Source
admission, argument interpretation and heap representation remain explicit.
No separate body execution law is assumed by this connection. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicExecutionMeaning
open Core Frontend SourceInference
open SourceCoreIndexedSession

/-- Public compile, open and start success recover one real recipe preparation
and the original indexed startup. All returned observations are propositions. -/
theorem actual_start {program : CheckedProgram} {seeds : List SourceCompiler.Seed}
    {options : SourceCompiler.Options} {compiled : SourceCoreExecution.Compiled}
    (compiledAccepted : SourceCoreExecution.compileChecked program seeds options = .ok compiled)
    {publicArtifact : SourceCoreExecution.Artifact}
    {publicSession : SourceCoreExecution.Session publicArtifact}
    {key : Key} {arguments : List SourceCorePublicValues.Value} {boundaryFuel : Nat}
    {publicCheckpoint : SourceCoreExecution.Checkpoint publicArtifact}
    (opened : publicArtifact.CompiledAt compiled)
    (accepted : publicSession.start key arguments boundaryFuel = .ok publicCheckpoint) :
    ∃ (recipe : Recipe) (artifact : Artifact) (session : Session artifact)
      (checkpoint : Checkpoint artifact) (root : Root recipe.compiled)
      (world : StoreTyping) (store : Store) (native : Environment)
      (encodedValues : SourceCoreCompatibleValues.Context),
      publicArtifact.IndexedAt compiled recipe artifact ∧
      Recipe.prepare recipe.compiled = .ok recipe ∧ recipe.compiled.sourceProgram = program ∧
      publicSession.IndexedAt session ∧ publicCheckpoint.IndexedAt checkpoint ∧
      RecursiveNamedPublicStartMeaning.StartAt session key arguments boundaryFuel
        checkpoint recipe root world store native encodedValues := by
  obtain ⟨recipe, artifact, session, checkpoint, atArtifact, atSession, atCheckpoint, issued⟩ :=
    publicSession.start_indexed opened accepted
  have selected : RecursiveNamedPreparedStageContracts.PublicRecipe compiled recipe :=
    atArtifact.compiled_recipe
  obtain ⟨source, sourceAccepted, cached, prepared⟩ :=
    RecursiveNamedPreparedStageContracts.public_compilation compiledAccepted selected
  have sourceProgram := (SourceCoreCompiler.Compiled.artifact_fields source cached).1.trans
    (SourceCoreCompiler.compileChecked_program sourceAccepted)
  obtain ⟨actualRecipe, root, world, store, native, encodedValues, started⟩ :=
    RecursiveNamedPublicStartMeaning.actual_start session issued
  have actualAt : artifact.RecipeAt actualRecipe := by
    cases artifact
    exact started.recipe_eq
  have atRecipe := atArtifact.recipe_at
  have same : actualRecipe = recipe := by
    unfold Artifact.RecipeAt at actualAt atRecipe
    exact actualAt.symm.trans atRecipe
  cases same
  exact ⟨recipe, artifact, session, checkpoint, root, world, store, native, encodedValues,
    atArtifact, prepared, sourceProgram, atSession, atCheckpoint, started⟩

/-- Word export follows the same public resume and native execution receipt.
This is a proof transport through the facade, with no native replay. -/
theorem resume_word_succeeded {publicArtifact : SourceCoreExecution.Artifact}
    {publicCheckpoint : SourceCoreExecution.Checkpoint publicArtifact}
    {publicOutcome : SourceCoreExecution.Outcome publicArtifact}
    {artifact : Artifact} {checkpoint : Checkpoint artifact} {fuel outputBudget : Nat}
    {word : Word} {store : Store}
    (atCheckpoint : publicCheckpoint.IndexedAt checkpoint)
    (resumed : publicCheckpoint.ResumeAt fuel outputBudget publicOutcome)
    (completed : checkpoint.NativeDone fuel (.inRight .word (.word word)) store)
    (requested : checkpoint.ResultTypeAt .word) (positive : 0 < outputBudget) :
    ∃ completion : SourceCoreExecution.Completion publicArtifact,
      publicOutcome = .succeeded completion ∧ completion.value = .word word := by
  rcases publicArtifact with ⟨compiled, opened⟩
  cases opened with
  | empty selected => rcases publicCheckpoint with ⟨impossible⟩; exact nomatch impossible
  | indexed recipe selected actualArtifact atRecipe =>
      rcases publicCheckpoint with ⟨actualCheckpoint⟩
      rcases atCheckpoint with ⟨rfl, same⟩
      cases eq_of_heq same
      obtain ⟨actualOutcome, receipt, returned⟩ := resumed
      obtain ⟨actual, succeeded, valueEq⟩ := receipt.word_succeeded completed requested positive
      rw [succeeded] at returned
      exact ⟨_, returned.symm, valueEq⟩

section Evidence
open GeneralHeap ReadOnly CompatiblePayload CoreProof
open RecursiveNamedCatalog RecursiveNamedPublicStartMeaning RecursiveNamedPublicDataInputs
open RecursiveNamedCatalogInvocationBounds
variable (authenticated : Bool) {artifact : Artifact} {session : Session artifact} {key : Key}
  {publicArguments : List SourceCorePublicValues.Value} {boundaryFuel : Nat}
  {checkpoint : Checkpoint artifact} {recipe : Recipe}
  {encodedValues : SourceCoreCompatibleValues.Context}
  {values : SourceCoreCompatibleValues.Context}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  {headers : Inventory recipe.compiled.indexed.ancestry values ambient.definitions (SourceSemantics.Program.ofChecked recipe.compiled.sourceProgram)} {locations : Locations} {capturePrefix : Nat}
  {compilation : Header recipe.compiled.indexed.ancestry values ambient.definitions (SourceSemantics.Program.ofChecked recipe.compiled.sourceProgram) → SourceCoreFunctions.Context}
  {expressionSyntax : Header recipe.compiled.indexed.ancestry values ambient.definitions (SourceSemantics.Program.ofChecked recipe.compiled.sourceProgram) → ExpressionId → Prop}
  {diagnosticPolicy : AssignmentDiagnosticPolicy}
  (functions : FunctionModel values.checked.catalog ambient)
  (extension : SourceCoreRawMetadata.Extends values.registry encodedValues.registry)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)
  (runtimeViews : FunctionRuntimeViews functions)
  {faults : FunctionCalls.FaultRep}
  (uninitialized : ∀ header ∈ headers, ∀ id location, faults (.uninitializedLocation location) (header.reasonAt id))
  (missing : ∀ header ∈ headers, ∀ id key value tag, MetadataRep encodedValues.registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((header.reasonAt id).add tag))
  (escaped : ∀ header ∈ headers, faults .controlEscapedFunction header.escaped)
  (prefixMatches : ∀ header ∈ headers, (compilation header).administrativePrefix = capturePrefix + 1)
  (profiles : ∀ header, header ∈ headers →
    ∀ {arguments : List Dynamic.Value} {before : Dynamic.Heap} {initialStore : Store}
      {initialMap : LocationMap} {initialWorld : StoreTyping} {administrative actualContext : Core.Context}
      {actual : Environment} {ξ : Renaming} {frameLocation : Location}
      {current : CallableIndexedHistory.NativeFrame} {ghost : CallableIndexedHistory.GhostFrame},
      BodyState headers locations capturePrefix functions encodedValues.registry header arguments before initialStore initialMap initialWorld
        administrative actualContext actual ξ frameLocation current ghost →
      RuntimeMatchProfileForWith authenticated diagnosticPolicy headers header (compilation header) header.readFuel (expressionSyntax header)
        (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative) encodedValues.registry faults)

variable {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store : Store}
  (caller : Entry headers locations capturePrefix 0 [] mapping world before store
    (SourceCoreCallableIndexedTemplates.globalEnvironment recipe.compiled.indexed))
  {header : Header recipe.compiled.indexed.ancestry values ambient.definitions (SourceSemantics.Program.ofChecked recipe.compiled.sourceProgram)}
  {root : SourceCoreIndexedSession.Root recipe.compiled} (selected : RecursiveNamedPublicRootMeaning.RootSelection headers root header)
  {arguments : List Dynamic.Value} {payloads : List Core.Value}
  (started : StartAt session key publicArguments boundaryFuel checkpoint recipe root world store payloads encodedValues)
  (data : ∀ argument ∈ publicArguments, DataPublic argument)
  (sameChecked : values.checked = recipe.compiled.compatible.checked)
  (programTyped : ProgramWellFormed (SourceSemantics.Program.ofChecked recipe.compiled.sourceProgram))
  (record : SourceCompilationPlan.exactSpecialization recipe.compiled.indexed.base.plan header.named.signature.key =
    .ok header.named.specialized)
  (meanings : RecursiveNamedPublicDataInputs.Meanings publicArguments arguments)
  (heaps : CompatibleAmbientHeap.HeapRepresents values.checked encodedValues.registry functions mapping world before store)


include extension faithful observations runtimeViews uninitialized missing escaped prefixMatches profiles caller selected started data sameChecked programTyped record meanings heaps in
/-- A success from one actual facade run reflects to a Source (SourceSemantics.Program.ofChecked recipe.compiled.sourceProgram) outcome
at its same native result/store. The returned public session remains aligned
with the exact indexed export session and its full semantic heap relation. -/
theorem run_succeeded_reflects_program_evidence
    {publicArtifact : SourceCoreExecution.Artifact}
    {publicSession : SourceCoreExecution.Session publicArtifact}
    {publicCheckpoint : SourceCoreExecution.Checkpoint publicArtifact}
    {publicCompletion : SourceCoreExecution.Completion publicArtifact}
    {options : SourceCoreExecution.RunOptions}
    (publicStart : publicSession.start key publicArguments options.inputValidationFuel = .ok publicCheckpoint)
    (atCheckpoint : publicCheckpoint.IndexedAt checkpoint)
    (publicRun : publicSession.RunAt key publicArguments options (.ok (.succeeded publicCompletion)))
    (admitted : Staging.ProgramHasStages (SourceSemantics.Program.ofChecked recipe.compiled.sourceProgram))
    (heapTyped : Dynamic.HeapWellTyped header.function.context before)
    (argumentsTyped : Dynamic.ValuesHaveTypes header.function.context before arguments header.types) :
    ∃ (actual : Completion artifact) (generation : SourceCorePublicValues.ExportGeneration)
      (value : Core.Value) (finalStore : Store) (outcome : Dynamic.ExpressionOutcome)
      (after : Dynamic.Heap) (finalMap : LocationMap) (finalWorld : StoreTyping),
      checkpoint.SucceededResultAt options.executionFuel options.outputValidationFuel
        generation value finalStore actual ∧
      publicCompletion.value = actual.value ∧ publicCompletion.sourceType = actual.sourceType ∧
      publicCompletion.boundaryFuel = actual.boundaryFuel ∧ publicCompletion.session.IndexedAt actual.session ∧
      Dynamic.ProgramOutcome (SourceSemantics.Program.ofChecked recipe.compiled.sourceProgram) (RecursiveNamedProgramEntrySource.entry header arguments) before outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked encodedValues.registry functions)
        finalMap finalWorld header.function.resultType header.output faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked encodedValues.registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      Nonempty (Entry headers locations capturePrefix 0 [] finalMap finalWorld after finalStore
        (SourceCoreCallableIndexedTemplates.globalEnvironment recipe.compiled.indexed)) := by
  obtain ⟨actualCheckpoint, accepted, resumed⟩ := publicRun
  have same : actualCheckpoint = publicCheckpoint := Except.ok.inj (accepted.symm.trans publicStart)
  subst actualCheckpoint
  obtain ⟨actual, generation, value, finalStore, completed, exported, valueEq, typeEq, budgetEq, sessionAt⟩ :=
    resumed.indexed_succeeded atCheckpoint
  obtain ⟨outcome, after, finalMap, finalWorld, executed, result, finalHeap, mapExtension,
    worldExtension, administrative, heapExtension, finalEntry⟩ :=
    RecursiveNamedPublicRuntimeMeaning.completed_reflects_program_evidence authenticated functions
      extension faithful observations runtimeViews uninitialized missing escaped prefixMatches profiles
      caller selected started data sameChecked programTyped record meanings heaps
      admitted heapTyped argumentsTyped completed
  exact ⟨actual, generation, value, finalStore, outcome, after, finalMap, finalWorld,
    exported, valueEq, typeEq, budgetEq, sessionAt, executed, result, finalHeap,
    mapExtension, worldExtension, administrative, heapExtension, finalEntry⟩

include extension faithful observations runtimeViews uninitialized missing escaped prefixMatches profiles caller selected started data sameChecked programTyped record meanings heaps in
/-- An actual public failure reconstructs a Source fault with the same token
relation, final heap, and the exact returned indexed session. -/
theorem run_failed_reflects_program_evidence
    {publicArtifact : SourceCoreExecution.Artifact}
    {publicSession : SourceCoreExecution.Session publicArtifact}
    {publicCheckpoint : SourceCoreExecution.Checkpoint publicArtifact}
    {returned : SourceCoreExecution.Session publicArtifact}
    {options : SourceCoreExecution.RunOptions} {reason : Word}
    (publicStart : publicSession.start key publicArguments options.inputValidationFuel = .ok publicCheckpoint)
    (atCheckpoint : publicCheckpoint.IndexedAt checkpoint)
    (publicRun : publicSession.RunAt key publicArguments options (.ok (.failed reason returned)))
    (admitted : Staging.ProgramHasStages (SourceSemantics.Program.ofChecked recipe.compiled.sourceProgram))
    (heapTyped : Dynamic.HeapWellTyped header.function.context before)
    (argumentsTyped : Dynamic.ValuesHaveTypes header.function.context before arguments header.types) :
    ∃ (actual : Session artifact) (value : Core.Value) (finalStore : Store)
      (sourceReason : Dynamic.SemanticFault) (after : Dynamic.Heap)
      (finalMap : LocationMap) (finalWorld : StoreTyping),
      checkpoint.FailedResultAt options.executionFuel value finalStore reason actual ∧
      returned.IndexedAt actual ∧ faults sourceReason reason ∧
      Dynamic.ProgramOutcome (SourceSemantics.Program.ofChecked recipe.compiled.sourceProgram)
        (RecursiveNamedProgramEntrySource.entry header arguments) before (.fault sourceReason) after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked encodedValues.registry functions)
        finalMap finalWorld header.function.resultType header.output faults (.fault sourceReason) value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked encodedValues.registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      Nonempty (Entry headers locations capturePrefix 0 [] finalMap finalWorld after finalStore
        (SourceCoreCallableIndexedTemplates.globalEnvironment recipe.compiled.indexed)) := by
  obtain ⟨actualCheckpoint, accepted, resumed⟩ := publicRun
  have same : actualCheckpoint = publicCheckpoint := Except.ok.inj (accepted.symm.trans publicStart)
  subst actualCheckpoint
  obtain ⟨actual, _generation, value, finalStore, completed, failed, sessionAt⟩ :=
    resumed.indexed_failed atCheckpoint
  obtain ⟨outcome, after, finalMap, finalWorld, executed, result, finalHeap, mapExtension,
    worldExtension, administrative, heapExtension, finalEntry⟩ :=
    RecursiveNamedPublicRuntimeMeaning.completed_reflects_program_evidence authenticated functions
      extension faithful observations runtimeViews uninitialized missing escaped prefixMatches profiles
      caller selected started data sameChecked programTyped record meanings heaps
      admitted heapTyped argumentsTyped completed
  have decoded := failed.2.1
  have faulted : ∃ sourceReason, outcome = .fault sourceReason ∧ faults sourceReason reason := by
    cases result with
    | value represented => simp [LanguageResult.decode?] at decoded
    | fault related =>
        simp only [LanguageResult.decode?, Option.some.injEq, LanguageResult.Outcome.failed.injEq] at decoded
        exact ⟨_, rfl, decoded ▸ related⟩
  obtain ⟨sourceReason, rfl, related⟩ := faulted
  exact ⟨actual, value, finalStore, sourceReason, after, finalMap, finalWorld,
    failed, sessionAt, related, executed, result, finalHeap,
    mapExtension, worldExtension, administrative, heapExtension, finalEntry⟩

include extension faithful observations runtimeViews uninitialized missing escaped prefixMatches profiles caller selected started data sameChecked programTyped record meanings heaps in
/-- A Source Word result reaches the same public checkpoint at sufficient
native fuel and exports that Word at a positive output budget. -/
theorem word_preserved_at_resume_evidence
    {publicArtifact : SourceCoreExecution.Artifact}
    {publicCheckpoint : SourceCoreExecution.Checkpoint publicArtifact}
    (atCheckpoint : publicCheckpoint.IndexedAt checkpoint)
    (outputWord : header.output = .word) (resultWord : header.function.resultType = .word)
    (outputBudget : Nat) (positive : 0 < outputBudget)
    {word : Word} {after : Dynamic.Heap}
    (executed : Dynamic.ProgramOutcome (SourceSemantics.Program.ofChecked recipe.compiled.sourceProgram)
      (RecursiveNamedProgramEntrySource.entry header arguments) before (.value (.word word)) after) :
    ∃ finalStore finalMap finalWorld required,
      (∀ fuel, required ≤ fuel → ∀ outcome,
        publicCheckpoint.ResumeAt fuel outputBudget outcome →
        ∃ completion, outcome = .succeeded completion ∧ completion.value = .word word) ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked encodedValues.registry functions)
        finalMap finalWorld header.function.resultType header.output faults
        (.value (.word word)) (.inRight .word (.word word)) ∧
      CompatibleAmbientHeap.HeapRepresents values.checked encodedValues.registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      Nonempty (Entry headers locations capturePrefix 0 [] finalMap finalWorld after finalStore
        (SourceCoreCallableIndexedTemplates.globalEnvironment recipe.compiled.indexed)) := by
  obtain ⟨value, finalStore, finalMap, finalWorld, required, completes, result, finalHeap,
    mapExtension, worldExtension, administrative, heapExtension, finalEntry⟩ :=
    RecursiveNamedPublicRuntimeMeaning.has_sufficient_fuel_evidence authenticated functions
      extension faithful observations runtimeViews uninitialized missing escaped prefixMatches profiles
      caller selected started data sameChecked programTyped record meanings heaps executed
  have wordResult := result
  rw [outputWord] at wordResult
  have nativeWord : value = .inRight .word (.word word) := by
    cases wordResult with
    | value represented =>
        obtain ⟨actualWord, sourceEq, nativeEq⟩ := CompatiblePlaceModifier.word_fields observations represented
        have same : word = actualWord := Dynamic.Value.word.inj sourceEq
        cases same
        exact congrArg (fun payload => Core.Value.inRight .word payload) nativeEq
  rw [nativeWord] at completes result
  have atRecipe : artifact.RecipeAt recipe := by
    cases artifact
    exact started.recipe_eq
  have requested := started.original.result_type_at atRecipe started.selected
  have rootWord := (RecursiveNamedPublicRootSourceSignature.inputs_and_result selected).2.trans resultWord
  rw [rootWord] at requested
  exact ⟨finalStore, finalMap, finalWorld, required,
    fun fuel enough outcome resumed => resume_word_succeeded atCheckpoint resumed
      (completes fuel enough) requested positive,
    result, finalHeap, mapExtension, worldExtension, administrative, heapExtension, finalEntry⟩

end Evidence
end Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicExecutionMeaning
