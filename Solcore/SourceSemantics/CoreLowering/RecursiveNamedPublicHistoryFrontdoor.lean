import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedBodiesSupport
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedHistoryPublicContinuations
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedHistoryPublicFailures

/-! An accepted public start selects its original native checkpoint, complete
Source header and original input encoding. Current history fixes the starting
world and store. The public execution consumer derives these receipts before
calling the existing semantic theorem and returns its reusable next history. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicHistoryFrontdoor
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open SourceCoreIndexedSession RecursiveNamedPublicStartMeaning
open CallableIndexedOwnedFunctionState
open CallableIndexedOwnedFunctionValues (Header)
open CallableIndexedOwnedPreparedBootstrapRootState (keys owner)
open CallableIndexedOwnedPreparedFiniteNamedInventories (Input Inventory headers)
open CallableIndexedOwnedContextualTypedClosureReceipts (Association)
open CallableIndexedOwnedPreparedStagedOrdinarySequenceCallerBounds (OrdinarySequenceFor)
open CallableIndexedOwnedPreparedStagedNamedBodies (Body)
open CallableIndexedOwnedPreparedStagedNamedBodiesSupport (Support)

/-- Data selected by one original public start. Each field of provenance is
proved from that start and the finite inventory, without a body execution. -/
structure Started {compiled : SourceCoreUnifiedCompilation.Compiled}
    (headers : List (Header compiled (Program.ofChecked compiled.sourceProgram)))
    {recipe : Recipe} (prepared : Recipe.prepare compiled = .ok recipe)
    {publicArtifact : SourceCoreExecution.Artifact}
    (publicCheckpoint : SourceCoreExecution.Checkpoint publicArtifact)
    {nativeArtifact : Artifact} (session : Session nativeArtifact)
    (key : Key) (publicArguments : List SourceCorePublicValues.Value) (fuel : Nat)
    (world : StoreTyping) (store : Store) where
  checkpoint : Checkpoint nativeArtifact
  root : Root compiled
  header : Header compiled (Program.ofChecked compiled.sourceProgram)
  payloads : Environment
  encodedValues : SourceCoreCompatibleValues.Context
  rawD : SourceTypedRuntime.RuntimeEvidenceEnvironment
  function : Dynamic.GlobalFunction
  atCheckpoint : publicCheckpoint.IndexedAt checkpoint
  started : StartAt session key publicArguments fuel checkpoint recipe
    ((Recipe.prepare_compiled prepared).symm ▸ root) world store payloads encodedValues
  selected : RecursiveNamedPublicRootMeaning.RootSelection
    (values := .initial compiled.compatible.checked)
    (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
    (program := Program.ofChecked compiled.sourceProgram) headers root header
  sourceAt : CallableIndexedOwnedFunctionValues.NamedSourceAt header rawD function

private theorem start_at_state {artifact : Artifact} {session : Session artifact}
    {world actualWorld : StoreTyping} {store actualStore : Store}
    (native : session.NativeAt world store) (state : SessionState session actualWorld actualStore) :
    actualWorld = world ∧ actualStore = store := by
  cases session
  rename_i authority currentWorld currentStore stored environmentTyped registry values owner sourcePrefix
  change currentWorld = world ∧ currentStore = store at native
  change currentWorld = actualWorld ∧ currentStore = actualStore at state
  exact ⟨state.1.symm.trans native.1, state.2.symm.trans native.2⟩

/-- Recover the actual selected root and current native input state for a
following public call. The caller can then retain its exact Source arguments
when invoking the public continuation theorem. -/
theorem recover_start
    {compiled : SourceCoreUnifiedCompilation.Compiled} {recipe : Recipe}
    (prepared : Recipe.prepare compiled = .ok recipe)
    (inputs : List (Input compiled)) (rows : Inventory inputs)
    (complete : RecursiveNamedCatalogNativeContexts.Complete
      (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      (program := Program.ofChecked compiled.sourceProgram) (headers rows))
    {nativeArtifact : Artifact} {session : Session nativeArtifact}
    (atRecipe : ArtifactRecipe nativeArtifact recipe)
    {world : StoreTyping} {store : Store} (native : session.NativeAt world store)
    {publicArtifact : SourceCoreExecution.Artifact}
    {publicSession : SourceCoreExecution.Session publicArtifact}
    {publicCheckpoint : SourceCoreExecution.Checkpoint publicArtifact}
    (atSession : publicSession.IndexedAt session)
    {key : Key} {publicArguments : List SourceCorePublicValues.Value} {fuel : Nat}
    (accepted : publicSession.start key publicArguments fuel = .ok publicCheckpoint) :
    Nonempty (Started (headers rows) prepared publicCheckpoint session key publicArguments fuel world store) := by
  have sameCompiled := Recipe.prepare_compiled prepared
  cases sameCompiled
  rcases publicArtifact with ⟨publicCompiled, opened⟩
  cases opened with
  | empty selected => exact False.elim atSession
  | indexed actualRecipe selected actualArtifact recipeAt =>
      rcases publicSession with ⟨actualSession⟩
      rcases atSession with ⟨rfl, sameSession⟩
      have same : actualSession = session := eq_of_heq sameSession
      subst actualSession
      obtain ⟨foundRecipe, foundArtifact, foundSession, checkpoint,
          _openedAt, atFound, atCheckpoint, startEq⟩ :=
        SourceCoreExecution.Session.start_indexed (compiled := publicCompiled)
          (checkpoint := publicCheckpoint) rfl accepted
      have artifactEq : actualArtifact = foundArtifact := atFound.1
      cases artifactEq
      have sessionEq : session = foundSession := eq_of_heq atFound.2
      cases sessionEq
      obtain ⟨currentRecipe, root, actualWorld, actualStore, payloads, encodedValues, started⟩ :=
        RecursiveNamedPublicStartMeaning.actual_start session startEq
      have recipeEq : currentRecipe = recipe := by
        cases actualArtifact
        exact started.recipe_eq.symm.trans atRecipe
      subst currentRecipe
      obtain ⟨worldEq, storeEq⟩ := start_at_state native started.state
      subst actualWorld
      subst actualStore
      obtain ⟨header, selectedRoot⟩ := started.selection prepared complete
      obtain ⟨rawD, function, sourceAt⟩ := (CallableIndexedOwnedPreparedFiniteNamedInventories.source_receipts rows).receipts
        header selectedRoot.member
      exact ⟨⟨checkpoint, root, header, payloads, encodedValues, rawD, function,
        atCheckpoint, started, selectedRoot, sourceAt⟩⟩

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {completion : SourceCoreCallableIndexedPrograms.Completion compiled.indexed}
  (inputs : List (Input compiled)) (rows : Inventory inputs)
  (stagePrepared : RecursiveNamedPreparedStageContracts.Prepared compiled
    compiled.indexed.ancestry.graph.inputs.callable)
  (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt compiled.indexed completion.entry
    completion.result.context.registry completion.result.extension completion.result.diagnostics)
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  {bodyRegistry : SourceCoreRawMetadata.Registry} {semanticFaults : FunctionCalls.FaultRep}
  {identities : Dynamic.Value → Word → Prop}
  (observations : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog
    (CallableIndexedOwnedContextualCellOrigins.functions (headers rows) (keys compiled)
      bodyRegistry semanticFaults profile) identities)
  (extension : SourceCoreRawMetadata.Extends
    (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry completion.result.context.registry)
  (semantic : ∀ reason token, semanticFaults reason token →
    CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics (.semantic reason) token)
  (family : ∀ {mapping world function native bindings parameterCore resultCore}
    (association : Association (headers rows) (keys compiled) bodyRegistry semanticFaults
      mapping world function native bindings parameterCore resultCore), OrdinarySequenceFor stagePrepared association)
  (namedTerminals : ∀ header, header ∈ headers rows → Body header)
  (namedSupport : ∀ header (member : header ∈ headers rows),
    Support (headers rows) (keys compiled) bodyRegistry header (RecursiveNamedPreparedStageScopes.registry stagePrepared)
      (namedTerminals header member) semanticFaults)
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  {recipe : SourceCoreIndexedSession.Recipe}
  (prepared : SourceCoreIndexedSession.Recipe.prepare compiled = .ok recipe)
  (complete : RecursiveNamedCatalogNativeContexts.Complete
    (values := .initial compiled.compatible.checked)
    (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
    (program := Program.ofChecked compiled.sourceProgram) (headers rows))
  {nativeArtifact : SourceCoreIndexedSession.Artifact}
  {nativeSession : SourceCoreIndexedSession.Session nativeArtifact}
  {anchor : Header compiled (Program.ofChecked compiled.sourceProgram)}
  {entries : List RecursiveNamedPublicFunctionHistory.Entry}
  {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store : Store}
  {caller : RecursiveNamedPublicFunctionHistory.Caller (headers rows) (keys compiled) mapping world before store}
  (history : RecursiveNamedPublicFunctionHistory.History (headers rows) (keys compiled)
    (CallableIndexedOwnedContextualCellOrigins.functions (headers rows) (keys compiled)
      bodyRegistry semanticFaults profile) completion.result.context.registry anchor
    nativeSession mapping world before store caller entries)
  (atRecipe : ArtifactRecipe nativeArtifact recipe)
  {publicArtifact : SourceCoreExecution.Artifact}
  {publicSession : SourceCoreExecution.Session publicArtifact}
  {publicCheckpoint : SourceCoreExecution.Checkpoint publicArtifact}
  (atSession : publicSession.IndexedAt nativeSession)
  {key : SourceCoreIndexedSession.Key} {options : SourceCoreExecution.RunOptions}
  {publicArguments : List SourceCorePublicValues.Value}
  {invocation : Staging.Recursive.Scope}

local notation "rootHeaders" => headers rows
local notation "rootKeys" => keys compiled
local notation "rootOwner" => owner compiled
local notation "rootFunctions" => CallableIndexedOwnedContextualCellOrigins.functions rootHeaders rootKeys bodyRegistry semanticFaults profile
local notation "rootFaults" => CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics

variable
  (inputsFor : ∀ request : Started (headers rows) prepared publicCheckpoint nativeSession key publicArguments
      options.inputValidationFuel world store, ∃ arguments,
    RecursiveNamedPublicFunctionHistoryInputs.Inputs entries request.header.function.context
      (request.header.bindings.map (fun binding => binding.1.scheme.body)) publicArguments arguments)
  (metadataFor : ∀ request : Started (headers rows) prepared publicCheckpoint nativeSession key publicArguments
      options.inputValidationFuel world store,
    SourceCoreRawMetadata.Extends request.encodedValues.registry completion.result.context.registry)
  (descriptors : ∀ request : Started (headers rows) prepared publicCheckpoint nativeSession key publicArguments
      options.inputValidationFuel world store,
    Nonempty (SourceCoreCallableContracts.Descriptor compiled.indexed.ancestry.graph.inputs.callable.table
      (.named request.header.named.signature.key)))

include receiver observations extension semantic family namedTerminals namedSupport wellFormed
  prepared complete history atRecipe atSession inputsFor metadataFor descriptors in
/-- Original public startup supplies every selected receipt, current state and
encoded argument position. Structural input descriptions and metadata coverage
are the only boundary conditions; the full execution meaning and next history
are constructed by the existing caller theorem. -/
theorem public_run_succeeded_retains
    {publicCompletion : SourceCoreExecution.Completion publicArtifact}
    (publicStart : publicSession.start key publicArguments options.inputValidationFuel = .ok publicCheckpoint)
    (publicRun : publicSession.RunAt key publicArguments options (.ok (.succeeded publicCompletion))) :
    ∃ (request : Started (headers rows) prepared publicCheckpoint nativeSession key publicArguments
      options.inputValidationFuel world store) (arguments : List Dynamic.Value),
      RecursiveNamedPublicFunctionHistoryInputs.Inputs entries request.header.function.context
        (request.header.bindings.map (fun binding => binding.1.scheme.body)) publicArguments arguments ∧
      ∃ (actual : SourceCoreIndexedSession.Completion nativeArtifact)
        (generation : SourceCorePublicValues.ExportGeneration) (value : Core.Value) (finalStore : Store)
        (capture : CallableIndexedOwnedFunctionValues.NamedCapture rootHeaders (rootOwner).key request.header mapping world)
        (sourceSize : Nat) (outcome : Staging.Recursive.Outcome) (after : Dynamic.Heap)
        (finalMap : LocationMap) (finalWorld : StoreTyping),
        request.checkpoint.SucceededResultAt options.executionFuel options.outputValidationFuel
          generation value finalStore actual ∧
        publicCompletion.IndexedAt actual ∧
        Staging.Recursive.Size.Applies (Program.ofChecked compiled.sourceProgram)
          (RecursiveNamedPreparedStageScopes.registry stagePrepared) sourceSize invocation anchor.function.context before
          (.global request.function) arguments outcome after ∧
        ∃ _result : CallableIndexedOwnedPreparedStagedTerminalNamedInvocationBounds.ResultAt
          (registry := completion.result.context.registry) (payloads := request.payloads)
          (scope := []) (canonical := SourceCoreCallableIndexedTemplates.globalEnvironment compiled.indexed)
          rootFunctions rootOwner caller request.header capture anchor.function.context
          outcome after value finalStore finalMap finalWorld rootFaults,
        ∃ reached : RecursiveNamedPublicFunctionHistory.Caller rootHeaders rootKeys finalMap finalWorld after finalStore,
          Relates caller reached ∧
          RecursiveNamedPublicFunctionHistory.History rootHeaders rootKeys rootFunctions
            completion.result.context.registry anchor actual.session finalMap finalWorld after finalStore reached entries := by
  obtain ⟨request⟩ := recover_start prepared inputs rows complete atRecipe history.current.1 atSession publicStart
  obtain ⟨arguments, inputReceipts⟩ := inputsFor request
  obtain ⟨descriptor⟩ := descriptors request
  obtain ⟨actual, generation, value, finalStore, capture, sourceSize, outcome, after, finalMap, finalWorld,
      succeeded, valueEq, typeEq, budgetEq, sessionAt, trace, result, reached, related, continued⟩ :=
    CallableIndexedOwnedPreparedStagedHistoryPublicContinuations.public_run_succeeded_retains
      (inputs := inputs) (rows := rows) (stagePrepared := stagePrepared) (receiver := receiver) (profile := profile)
      (observations := observations) (extension := extension) (semantic := semantic)
      (family := family) (namedTerminals := namedTerminals) (namedSupport := namedSupport)
      (wellFormed := wellFormed) (prepared := prepared) (selected := request.selected)
      (caller := caller) (history := history) (atCheckpoint := request.atCheckpoint) (started := request.started)
      (inputReceipts := inputReceipts) (metadata := metadataFor request) (sourceAt := request.sourceAt)
      publicStart publicRun descriptor
  exact ⟨request, arguments, inputReceipts, actual, generation, value, finalStore, capture, sourceSize,
    outcome, after, finalMap, finalWorld, succeeded, ⟨valueEq, typeEq, budgetEq, sessionAt⟩,
    trace, result, reached, related, continued⟩

include receiver observations extension semantic family namedTerminals namedSupport wellFormed
  prepared complete history atRecipe atSession inputsFor metadataFor descriptors in
/-- A function returned by the original public execution joins the history.
The remembered entry uses the exact selected Source result type and the actual
returned Source value and native payload. -/
theorem public_run_succeeded_remembers
    {publicCompletion : SourceCoreExecution.Completion publicArtifact}
    (publicStart : publicSession.start key publicArguments options.inputValidationFuel = .ok publicCheckpoint)
    (publicRun : publicSession.RunAt key publicArguments options (.ok (.succeeded publicCompletion)))
    {handle : SourceCorePublicValues.Handle}
    (returnedHandle : publicCompletion.value = .function handle) :
    ∃ (request : Started (headers rows) prepared publicCheckpoint nativeSession key publicArguments
      options.inputValidationFuel world store) (arguments : List Dynamic.Value),
      RecursiveNamedPublicFunctionHistoryInputs.Inputs entries request.header.function.context
        (request.header.bindings.map (fun binding => binding.1.scheme.body)) publicArguments arguments ∧
      ∃ (actual : SourceCoreIndexedSession.Completion nativeArtifact)
        (generation : SourceCorePublicValues.ExportGeneration) (value : Core.Value) (finalStore : Store)
        (capture : CallableIndexedOwnedFunctionValues.NamedCapture rootHeaders (rootOwner).key request.header mapping world)
        (sourceSize : Nat) (outcome : Staging.Recursive.Outcome) (after : Dynamic.Heap)
        (finalMap : LocationMap) (finalWorld : StoreTyping),
        request.checkpoint.SucceededResultAt options.executionFuel options.outputValidationFuel
          generation value finalStore actual ∧
        publicCompletion.IndexedAt actual ∧
        Staging.Recursive.Size.Applies (Program.ofChecked compiled.sourceProgram)
          (RecursiveNamedPreparedStageScopes.registry stagePrepared) sourceSize invocation anchor.function.context before
          (.global request.function) arguments outcome after ∧
        ∃ _result : CallableIndexedOwnedPreparedStagedTerminalNamedInvocationBounds.ResultAt
          (registry := completion.result.context.registry) (payloads := request.payloads)
          (scope := []) (canonical := SourceCoreCallableIndexedTemplates.globalEnvironment compiled.indexed)
          rootFunctions rootOwner caller request.header capture anchor.function.context
          outcome after value finalStore finalMap finalWorld rootFaults,
        ∃ reached : RecursiveNamedPublicFunctionHistory.Caller rootHeaders rootKeys finalMap finalWorld after finalStore,
        ∃ source payload, outcome = .value source ∧ value = .inRight .word payload ∧
          Relates caller reached ∧
          RecursiveNamedPublicFunctionHistory.History rootHeaders rootKeys rootFunctions
            completion.result.context.registry anchor actual.session finalMap finalWorld after finalStore reached
            (entries ++ [⟨request.header.function.resultType, source, handle, payload, request.header.output,
              options.outputValidationFuel⟩]) := by
  obtain ⟨request⟩ := recover_start prepared inputs rows complete atRecipe history.current.1 atSession publicStart
  obtain ⟨arguments, inputReceipts⟩ := inputsFor request
  obtain ⟨descriptor⟩ := descriptors request
  obtain ⟨actual, generation, value, finalStore, capture, sourceSize, outcome, after, finalMap, finalWorld,
      succeeded, valueEq, typeEq, budgetEq, sessionAt, trace, result, reached, source, payload, sourceValue, nativeValue, related, continued⟩ :=
    CallableIndexedOwnedPreparedStagedHistoryPublicContinuations.public_run_succeeded_remembers
      (inputs := inputs) (rows := rows) (stagePrepared := stagePrepared) (receiver := receiver) (profile := profile)
      (observations := observations) (extension := extension) (semantic := semantic)
      (family := family) (namedTerminals := namedTerminals) (namedSupport := namedSupport)
      (wellFormed := wellFormed) (prepared := prepared) (selected := request.selected)
      (caller := caller) (history := history) (atCheckpoint := request.atCheckpoint) (started := request.started)
      (inputReceipts := inputReceipts) (metadata := metadataFor request) (sourceAt := request.sourceAt)
      publicStart publicRun returnedHandle descriptor
  exact ⟨request, arguments, inputReceipts, actual, generation, value, finalStore, capture, sourceSize,
    outcome, after, finalMap, finalWorld, succeeded, ⟨valueEq, typeEq, budgetEq, sessionAt⟩,
    trace, result, reached, source, payload, sourceValue, nativeValue, related, continued⟩

include receiver observations extension semantic family namedTerminals namedSupport wellFormed
  prepared complete history atRecipe atSession inputsFor metadataFor descriptors in
/-- The original public start and successful product output supply every
selected function entry. The selection describes output positions only; entry
meaning and recursive validation fuel come from the execution and its codec. -/
theorem public_run_succeeded_collects
    {publicCompletion : SourceCoreExecution.Completion publicArtifact}
    (publicStart : publicSession.start key publicArguments options.inputValidationFuel = .ok publicCheckpoint)
    (publicRun : publicSession.RunAt key publicArguments options (.ok (.succeeded publicCompletion)))
    (outputSelections : ∀ request : Started (headers rows) prepared publicCheckpoint nativeSession key publicArguments
      options.inputValidationFuel world store,
      RecursiveNamedPublicOutputSelections.Selection request.header.function.resultType publicCompletion.value) :
    ∃ (request : Started (headers rows) prepared publicCheckpoint nativeSession key publicArguments
      options.inputValidationFuel world store) (arguments : List Dynamic.Value),
      RecursiveNamedPublicFunctionHistoryInputs.Inputs entries request.header.function.context
        (request.header.bindings.map (fun binding => binding.1.scheme.body)) publicArguments arguments ∧
      ∃ (actual : SourceCoreIndexedSession.Completion nativeArtifact)
        (generation : SourceCorePublicValues.ExportGeneration) (value : Core.Value) (finalStore : Store)
        (capture : CallableIndexedOwnedFunctionValues.NamedCapture rootHeaders (rootOwner).key request.header mapping world)
        (sourceSize : Nat) (outcome : Staging.Recursive.Outcome) (after : Dynamic.Heap)
        (finalMap : LocationMap) (finalWorld : StoreTyping),
        request.checkpoint.SucceededResultAt options.executionFuel options.outputValidationFuel
          generation value finalStore actual ∧
        publicCompletion.IndexedAt actual ∧
        Staging.Recursive.Size.Applies (Program.ofChecked compiled.sourceProgram)
          (RecursiveNamedPreparedStageScopes.registry stagePrepared) sourceSize invocation anchor.function.context before
          (.global request.function) arguments outcome after ∧
        ∃ _result : CallableIndexedOwnedPreparedStagedTerminalNamedInvocationBounds.ResultAt
          (registry := completion.result.context.registry) (payloads := request.payloads)
          (scope := []) (canonical := SourceCoreCallableIndexedTemplates.globalEnvironment compiled.indexed)
          rootFunctions rootOwner caller request.header capture anchor.function.context
          outcome after value finalStore finalMap finalWorld rootFaults,
        ∃ reached : RecursiveNamedPublicFunctionHistory.Caller rootHeaders rootKeys finalMap finalWorld after finalStore,
        ∃ added : List RecursiveNamedPublicFunctionHistory.Entry,
          added.map RecursiveNamedPublicFunctionHistory.Entry.handle = (outputSelections request).handles ∧
          Relates caller reached ∧
          RecursiveNamedPublicFunctionHistory.History rootHeaders rootKeys rootFunctions
            completion.result.context.registry anchor actual.session finalMap finalWorld after finalStore reached (entries ++ added) := by
  obtain ⟨request⟩ := recover_start prepared inputs rows complete atRecipe history.current.1 atSession publicStart
  obtain ⟨arguments, inputReceipts⟩ := inputsFor request
  obtain ⟨descriptor⟩ := descriptors request
  obtain ⟨actual, generation, value, finalStore, capture, sourceSize, outcome, after, finalMap, finalWorld,
      succeeded, valueEq, typeEq, budgetEq, sessionAt, trace, result, reached, added, handles, related, continued⟩ :=
    CallableIndexedOwnedPreparedStagedHistoryPublicContinuations.public_run_succeeded_collects
      (inputs := inputs) (rows := rows) (stagePrepared := stagePrepared) (receiver := receiver) (profile := profile)
      (observations := observations) (extension := extension) (semantic := semantic)
      (family := family) (namedTerminals := namedTerminals) (namedSupport := namedSupport)
      (wellFormed := wellFormed) (prepared := prepared) (selected := request.selected)
      (caller := caller) (history := history) (atCheckpoint := request.atCheckpoint) (started := request.started)
      (inputReceipts := inputReceipts) (metadata := metadataFor request) (sourceAt := request.sourceAt)
      publicStart publicRun (outputSelections request) descriptor
  exact ⟨request, arguments, inputReceipts, actual, generation, value, finalStore, capture, sourceSize,
    outcome, after, finalMap, finalWorld, succeeded, ⟨valueEq, typeEq, budgetEq, sessionAt⟩,
    trace, result, reached, added, handles, related, continued⟩


include receiver observations extension semantic family namedTerminals namedSupport wellFormed
  prepared complete history atRecipe atSession inputsFor metadataFor descriptors in
/-- Actual public startup and a failed execution return a reusable history at
the failure heap, preserving every earlier handle and its captured environment. -/
theorem public_run_failed_retains
    {returned : SourceCoreExecution.Session publicArtifact} {reason : Word}
    (publicStart : publicSession.start key publicArguments options.inputValidationFuel = .ok publicCheckpoint)
    (publicRun : publicSession.RunAt key publicArguments options (.ok (.failed reason returned))) :
    ∃ (request : Started (headers rows) prepared publicCheckpoint nativeSession key publicArguments
      options.inputValidationFuel world store) (arguments : List Dynamic.Value),
      RecursiveNamedPublicFunctionHistoryInputs.Inputs entries request.header.function.context
        (request.header.bindings.map (fun binding => binding.1.scheme.body)) publicArguments arguments ∧
      ∃ (actual : SourceCoreIndexedSession.Session nativeArtifact) (value : Core.Value) (finalStore : Store)
        (capture : CallableIndexedOwnedFunctionValues.NamedCapture rootHeaders (rootOwner).key request.header mapping world)
        (sourceSize : Nat) (outcome : Staging.Recursive.Outcome) (after : Dynamic.Heap)
        (finalMap : LocationMap) (finalWorld : StoreTyping),
        request.checkpoint.FailedResultAt options.executionFuel value finalStore reason actual ∧
        returned.IndexedAt actual ∧
        Staging.Recursive.Size.Applies (Program.ofChecked compiled.sourceProgram)
          (RecursiveNamedPreparedStageScopes.registry stagePrepared) sourceSize invocation anchor.function.context before
          (.global request.function) arguments outcome after ∧
        ∃ _result : CallableIndexedOwnedPreparedStagedTerminalNamedInvocationBounds.ResultAt
          (registry := completion.result.context.registry) (payloads := request.payloads)
          (scope := []) (canonical := SourceCoreCallableIndexedTemplates.globalEnvironment compiled.indexed)
          rootFunctions rootOwner caller request.header capture anchor.function.context
          outcome after value finalStore finalMap finalWorld rootFaults,
        ∃ reached : RecursiveNamedPublicFunctionHistory.Caller rootHeaders rootKeys finalMap finalWorld after finalStore,
          Relates caller reached ∧
          RecursiveNamedPublicFunctionHistory.History rootHeaders rootKeys rootFunctions
            completion.result.context.registry anchor actual finalMap finalWorld after finalStore reached entries := by
  obtain ⟨request⟩ := recover_start prepared inputs rows complete atRecipe history.current.1 atSession publicStart
  obtain ⟨arguments, inputReceipts⟩ := inputsFor request
  obtain ⟨descriptor⟩ := descriptors request
  obtain ⟨actual, value, finalStore, capture, sourceSize, outcome, after, finalMap, finalWorld,
      failed, sessionAt, trace, result, reached, related, continued⟩ :=
    CallableIndexedOwnedPreparedStagedHistoryPublicFailures.public_run_failed_retains
      (inputs := inputs) (rows := rows) (stagePrepared := stagePrepared) (receiver := receiver) (profile := profile)
      (observations := observations) (extension := extension) (semantic := semantic)
      (family := family) (namedTerminals := namedTerminals) (namedSupport := namedSupport)
      (wellFormed := wellFormed) (prepared := prepared) (selected := request.selected)
      (caller := caller) (history := history) (atCheckpoint := request.atCheckpoint) (started := request.started)
      (inputReceipts := inputReceipts) (metadata := metadataFor request) (sourceAt := request.sourceAt)
      publicStart publicRun descriptor
  exact ⟨request, arguments, inputReceipts, actual, value, finalStore, capture, sourceSize,
    outcome, after, finalMap, finalWorld, failed, sessionAt, trace, result, reached, related, continued⟩

end Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicHistoryFrontdoor
