import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicFaultReceivers
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.NamedEvidenceRoots
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.PhysicalPublic
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.InitializedPublicBounds
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.PublicRoots
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.PublicDirectHistories
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.PublicInputRegistries
import Solcore.Frontend.SourceCoreFailurePreservationReceipts
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.PublicFunctionHistory
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPhysicalCanonicalState
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.PublicNestedInputs
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPhysicalCellOrigins
import Solcore.SourceSemantics.Staging.RecursiveFaultPreservation
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedPrepared.Bootstrap
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.PublicArgumentReceipts
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.OrdinarySequenceCallers
import Solcore.SourceSemantics.CoreLowering.CompatiblePublicOutputShapes
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.PublicPhysicalApplications
import Solcore.Frontend.SourceCoreExecution

/-!
# Recursive named public results: the actual registry

Public runs against the actual registry: the history and physical front doors, starts, reflection, failures, export errors, output collection and their preservation.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicHistoryFrontdoor
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
  {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
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
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicPhysicalFrontdoor
/-! Actual public startup needs Source attribution only for its selected root.
Complete physical method slots are retained separately from ordinary semantic
headers; the whole-root coverage API remains a specialization. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicPhysicalFrontdoor
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open SourceCoreIndexedSession RecursiveNamedPublicStartMeaning RecursiveNamedPublicHistoryFrontdoor
open CallableIndexedOwnedPreparedFiniteNamedInventories (Input Inventory headers)

private theorem start_at_state {artifact : Artifact} {session : Session artifact}
    {world actualWorld : StoreTyping} {store actualStore : Store}
    (native : session.NativeAt world store) (state : SessionState session actualWorld actualStore) :
    actualWorld = world ∧ actualStore = store := by
  cases session
  rename_i authority currentWorld currentStore stored environmentTyped registry values owner sourcePrefix
  change currentWorld = world ∧ currentStore = store at native
  change currentWorld = actualWorld ∧ currentStore = actualStore at state
  exact ⟨state.1.symm.trans native.1, state.2.symm.trans native.2⟩

/-- Recover the actual public start using only its selected root. A static
selector may retain additional Source admission at the exact returned Header;
no coverage of unrelated roots or body execution is required. -/
theorem recover_start_at_with
    {compiled : SourceCoreUnifiedCompilation.Compiled} {recipe : Recipe}
    (prepared : Recipe.prepare compiled = .ok recipe)
    (inputs : List (Input compiled)) (rows : Inventory inputs)
    {nativeArtifact : Artifact} {session : Session nativeArtifact}
    (atRecipe : ArtifactRecipe nativeArtifact recipe)
    {world : StoreTyping} {store : Store} (native : session.NativeAt world store)
    {publicArtifact : SourceCoreExecution.Artifact}
    {publicSession : SourceCoreExecution.Session publicArtifact}
    {publicCheckpoint : SourceCoreExecution.Checkpoint publicArtifact}
    (atSession : publicSession.IndexedAt session)
    {key : Key} {publicArguments : List SourceCorePublicValues.Value} {fuel : Nat}
    (admitted : Root compiled →
      CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram) → Prop)
    (select : ∀ root : Root compiled,
      recipe.roots.find? (fun candidate => decide (candidate.key = key)) =
        some ((Recipe.prepare_compiled prepared).symm ▸ root) →
      ∃ header, RecursiveNamedPublicRootMeaning.RootSelection
        (values := .initial compiled.compatible.checked)
        (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
        (program := Program.ofChecked compiled.sourceProgram) (headers rows) root header ∧
        admitted root header)
    (accepted : publicSession.start key publicArguments fuel = .ok publicCheckpoint) :
    ∃ request : Started (headers rows) prepared publicCheckpoint session key publicArguments fuel world store,
      admitted request.root request.header := by
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
      obtain ⟨header, selectedRoot, admission⟩ := select root started.selected
      obtain ⟨rawD, function, sourceAt⟩ := (CallableIndexedOwnedPreparedFiniteNamedInventories.source_receipts rows).receipts
        header selectedRoot.member
      exact ⟨⟨checkpoint, root, header, payloads, encodedValues, rawD, function,
        atCheckpoint, started, selectedRoot, sourceAt⟩, admission⟩


/-- A Header selector for the actual first matching public root suffices to
recover the same start receipt used by existing public continuations. -/
theorem recover_start_at
    {compiled : SourceCoreUnifiedCompilation.Compiled} {recipe : Recipe}
    (prepared : Recipe.prepare compiled = .ok recipe)
    (inputs : List (Input compiled)) (rows : Inventory inputs)
    {nativeArtifact : Artifact} {session : Session nativeArtifact}
    (atRecipe : ArtifactRecipe nativeArtifact recipe)
    {world : StoreTyping} {store : Store} (native : session.NativeAt world store)
    {publicArtifact : SourceCoreExecution.Artifact}
    {publicSession : SourceCoreExecution.Session publicArtifact}
    {publicCheckpoint : SourceCoreExecution.Checkpoint publicArtifact}
    (atSession : publicSession.IndexedAt session)
    {key : Key} {publicArguments : List SourceCorePublicValues.Value} {fuel : Nat}
    (select : ∀ root : Root compiled,
      recipe.roots.find? (fun candidate => decide (candidate.key = key)) =
        some ((Recipe.prepare_compiled prepared).symm ▸ root) →
      ∃ header, RecursiveNamedPublicRootMeaning.RootSelection
        (values := .initial compiled.compatible.checked)
        (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
        (program := Program.ofChecked compiled.sourceProgram) (headers rows) root header)
    (accepted : publicSession.start key publicArguments fuel = .ok publicCheckpoint) :
    Nonempty (Started (headers rows) prepared publicCheckpoint session key publicArguments fuel world store) := by
  obtain ⟨request, _⟩ := recover_start_at_with prepared inputs rows atRecipe native atSession
    (fun _ _ => True) (fun root selected => by
      obtain ⟨header, selectedRoot⟩ := select root selected
      exact ⟨header, selectedRoot, True.intro⟩) accepted
  exact ⟨request⟩


/-- Recover the actual selected root and current native input state for a
following public call. The caller can then retain its exact Source arguments
when invoking the public continuation theorem. -/
theorem recover_start_covered
    {compiled : SourceCoreUnifiedCompilation.Compiled} {recipe : Recipe}
    (prepared : Recipe.prepare compiled = .ok recipe)
    (inputs : List (Input compiled)) (rows : Inventory inputs)
    (coverage : RecursiveNamedPublicRootCoverage.Coverage
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
  apply recover_start_at prepared inputs rows atRecipe native atSession _ accepted
  intro root selected
  have sameCompiled := Recipe.prepare_compiled prepared
  cases sameCompiled
  exact RecursiveNamedPublicRootCoverage.selection_of_recipe prepared
    (List.mem_of_find?_eq_some selected) coverage

end Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicPhysicalFrontdoor
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicActualRegistryStart
/-! The actual packed startup determines the receiving context. Current
history supplies both the retained callable and every nested input handle;
the encoder supplies the forward registry extension. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicActualRegistryStart
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open SourceCoreIndexedSession CallableIndexedOwnedFunctionState
open RecursiveNamedPublicFunctionHistory (History Entry Caller)
open CallableIndexedOwnedPublicFaultReceivers

variable {recipe : Recipe}
  {headers : List (CallableIndexedOwnedFunctionValues.Header recipe.compiled (Program.ofChecked recipe.compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key recipe.compiled (Program.ofChecked recipe.compiled.sourceProgram))}
  {functions : FunctionModel recipe.compiled.compatible.checked.catalog
    (CallableIndexedAmbient.ambientDefinitions recipe.compiled.indexed)}
  {registry : SourceCoreRawMetadata.Registry}
  {anchor : CallableIndexedOwnedFunctionValues.Header recipe.compiled (Program.ofChecked recipe.compiled.sourceProgram)}
  {mapping : LocationMap} {world : StoreTyping} {heap : Dynamic.Heap} {store : Store}
  {caller : Caller headers keys mapping world heap store}
  {artifact : Artifact} {session : Session artifact} {entries : List Entry}

/-- Construct the actual receiver and input meaning together. No completed
native execution, future registry or reverse extension is supplied. -/
theorem packed_input
    (history : History headers keys functions registry anchor session mapping world heap store caller entries)
    (atRegistry : session.RegistryAt registry)
    {entry : Entry} (member : entry ∈ entries)
    {sourceParameter sourceResult : TypeSystem.Ty}
    (entryType : entry.sourceType = .function sourceParameter sourceResult)
    {argument : SourceCorePublicValues.Value} {source : Dynamic.Value}
    (input : RecursiveNamedPublicFunctionHistoryInputs.Input entries anchor.function.context sourceParameter argument source)
    {inputFuel : Nat} {checkpoint : Checkpoint artifact}
    {parameter result : TypeSystem.Ty} {nativeParameter nativeResult : Core.Ty}
    {callable packed : Core.Value} {encodedValues : SourceCoreCompatibleValues.Context}
    (started : RecursiveNamedPublicDirectPackedInputMeaning.StartAt session entry.handle argument inputFuel
      checkpoint recipe world store parameter result nativeParameter nativeResult callable packed encodedValues) :
    ∃ receiver : Receiver recipe.compiled.indexed,
      receiver.entry ∈ recipe.compiled.indexed.entries ∧
      receiver.result.context = encodedValues ∧
      CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt recipe.compiled.indexed receiver.entry
        receiver.result.context.registry receiver.result.extension receiver.result.diagnostics ∧
      SourceCoreRawMetadata.Extends registry receiver.result.context.registry ∧
      History headers keys functions receiver.result.context.registry anchor
        session mapping world heap store caller entries ∧
      ValueRep recipe.compiled.compatible.checked receiver.result.context.registry functions mapping world
        sourceParameter source packed nativeParameter ∧
      Dynamic.ValueHasType anchor.function.context heap source sourceParameter ∧
      ∀ token, checkpoint.diagnostic token = .ok (receiver.result.diagnostics.diagnostic? token) := by
  obtain ⟨extended, retained, represented, typed⟩ :=
    RecursiveNamedPublicHistoryRegistryExtension.at_packed_input rfl member entryType input history atRegistry started
  obtain ⟨indexed, indexedMember⟩ := RecursiveNamedPublicHistoryRegistryExtension.indexed_entry history
  obtain ⟨receiver, indexedAt, contextAt, issued⟩ :=
    Receiver.at_context recipe.compiled indexed encodedValues started.owner
  obtain ⟨program, present⟩ := RecursiveNamedPublicHistoryRegistryExtension.diagnostics_present history
  refine ⟨receiver, indexedAt ▸ indexedMember, contextAt, issued, ?_, ?_, ?_, typed,
    fun token => RecursiveNamedPublicCheckpointReceiver.diagnostic_eq
      started.recipe_eq started.values contextAt issued present token⟩
  · rw [contextAt]; exact extended
  · rw [contextAt]; exact retained
  · rw [contextAt]; exact represented

end Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicActualRegistryStart
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicActualRegistryReflection
/-! The pending public call uses its actual input metadata registry. Earlier
handles and Source captures are retained by forward extension, and diagnostics
are transported from the previous authentic receiver. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicActualRegistryReflection
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open SourceCoreIndexedSession RecursiveNamedPublicStartMeaning
open RecursiveNamedPublicFunctionHistory (History Entry Caller)
open RecursiveNamedPublicDirectPackedInputMeaning (StartAt)
open RecursivePublicApplicationResult (ResultAt)
open CallableIndexedOwnedFunctionState
open CallableIndexedOwnedContextualTypedClosureReceipts (Association)

variable {recipe : Recipe}
variable
  {headers : List (CallableIndexedOwnedFunctionValues.Header recipe.compiled (Program.ofChecked recipe.compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key recipe.compiled (Program.ofChecked recipe.compiled.sourceProgram))}

section Meaning
variable {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver recipe.compiled.indexed}
  {bodyRegistry : SourceCoreRawMetadata.Registry} {semanticFaults : FunctionCalls.FaultRep}
  (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt recipe.compiled.indexed completion.entry
    completion.result.context.registry completion.result.extension completion.result.diagnostics)
  (stagePrepared : RecursiveNamedPreparedStageContracts.Prepared recipe.compiled
    recipe.compiled.indexed.ancestry.graph.inputs.callable)
  (profile : recipe.compiled.compatible.checked.catalog.callableContracts = true)
  {identities : Dynamic.Value → Word → Prop}
  (observations : CompatibleEquality.FunctionObservations recipe.compiled.compatible.checked.catalog
    (CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry semanticFaults profile) identities)
  (semantic : ∀ reason token, semanticFaults reason token →
    CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics (.semantic reason) token)
  (family : ∀ {mapping world function native bindings parameterCore resultCore}
    (association : Association headers keys bodyRegistry semanticFaults mapping world function native
      bindings parameterCore resultCore),
    CallableIndexedOwnedPreparedStagedOrdinarySequenceCallerBounds.OrdinarySequenceFor stagePrepared association)
  (namedTerminals : ∀ header, header ∈ headers →
    CallableIndexedOwnedPreparedStagedNamedBodies.Body header)
  (namedSupport : ∀ header (member : header ∈ headers),
    CallableIndexedOwnedPreparedStagedNamedBodiesSupport.Support headers keys bodyRegistry header
      (RecursiveNamedPreparedStageScopes.registry stagePrepared) (namedTerminals header member) semanticFaults)
  (wellFormed : ProgramWellFormed (Program.ofChecked recipe.compiled.sourceProgram))
  {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store : Store}
  {anchor : CallableIndexedOwnedFunctionValues.Header recipe.compiled (Program.ofChecked recipe.compiled.sourceProgram)}
  {caller : Caller headers keys mapping world before store}
  {artifact : Artifact} {session : Session artifact} {entries : List Entry}
  (history : History headers keys
    (CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry semanticFaults profile)
    completion.result.context.registry anchor session mapping world before store caller entries)
  (entry : Entry) (member : entry ∈ entries)
  {parameter result : TypeSystem.Ty}
  (entryType : entry.sourceType = .function parameter result)
  {argument : SourceCorePublicValues.Value} {packedSource : Dynamic.Value}
  (input : RecursiveNamedPublicFunctionHistoryInputs.Input entries anchor.function.context parameter argument packedSource)

  (atRecipe : ArtifactRecipe artifact recipe)

local notation "functions" => CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry semanticFaults profile
local notation "callStages" => RecursiveNamedPreparedStageScopes.registry stagePrepared

include receiver stagePrepared profile observations semantic family namedTerminals namedSupport wellFormed
  history entry member entryType input in
/-- A successful public resume reflects to Source at the actual extended
registry, with the returned history ready for the next actual session. -/
theorem public_resume_succeeded
    (atRegistry : session.RegistryAt completion.result.context.registry)
    {inputFuel : Nat} {checkpoint : Checkpoint artifact}
    {actualParameter actualResult : TypeSystem.Ty} {nativeParameter nativeResult : Core.Ty}
    {callable packed : Core.Value} {encodedValues : SourceCoreCompatibleValues.Context}
    (started : StartAt session entry.handle argument inputFuel checkpoint recipe world store
      actualParameter actualResult nativeParameter nativeResult callable packed encodedValues)
    {publicArtifact : SourceCoreExecution.Artifact}
    {publicCheckpoint : SourceCoreExecution.Checkpoint publicArtifact}
    {publicCompletion : SourceCoreExecution.Completion publicArtifact}
    {executionFuel outputFuel : Nat}
    (atCheckpoint : publicCheckpoint.IndexedAt checkpoint)
    (resumed : publicCheckpoint.ResumeAt executionFuel outputFuel (.succeeded publicCompletion))
    (invocation : Staging.Recursive.Scope) :
    ∃ receiving : CallableIndexedOwnedPublicFaultReceivers.Receiver recipe.compiled.indexed,
      receiving.result.context = encodedValues ∧
      CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt recipe.compiled.indexed receiving.entry
        receiving.result.context.registry receiving.result.extension receiving.result.diagnostics ∧
      SourceCoreRawMetadata.Extends completion.result.context.registry receiving.result.context.registry ∧
      (∀ token, checkpoint.diagnostic token = .ok (receiving.result.diagnostics.diagnostic? token)) ∧
    SourceCoreRawMetadata.runtimeType actualParameter = SourceCoreRawMetadata.runtimeType parameter ∧
    SourceCoreRawMetadata.runtimeType actualResult = SourceCoreRawMetadata.runtimeType result ∧
    ∃ (actual : Completion artifact) (generation : SourceCorePublicValues.ExportGeneration)
      (value : Core.Value) (finalStore : Store) (sources : List Dynamic.Value)
      (sourceSize : Nat) (outcome : Staging.Recursive.Outcome) (after : Dynamic.Heap)
      (finalMap : LocationMap) (finalWorld : StoreTyping)
      (reached : Caller headers keys finalMap finalWorld after finalStore),
      checkpoint.NativeDone executionFuel value finalStore ∧
      checkpoint.SucceededResultAt executionFuel outputFuel generation value finalStore actual ∧
      publicCompletion.IndexedAt actual ∧
      Dynamic.ValuesPack sources packedSource ∧
      Staging.Recursive.Size.Applies (Program.ofChecked recipe.compiled.sourceProgram) callStages sourceSize
        invocation anchor.function.context before entry.source sources outcome after ∧
      ResultAt (registry := receiving.result.context.registry) functions caller anchor.function.context result nativeResult
        outcome after value finalStore finalMap finalWorld
        (CallableIndexedOwnedPublicDecodedStagedCallFaults.faults receiving.result.diagnostics) ∧
      Relates caller reached ∧
      History headers keys functions receiving.result.context.registry anchor actual.session
        finalMap finalWorld after finalStore reached entries ∧
      actual.session.RegistryAt encodedValues.registry := by
  obtain ⟨receiving, _indexed, contextAt, issued, extended, retained, _represented, _typed, diagnostics⟩ :=
    RecursiveNamedPublicActualRegistryStart.packed_input history atRegistry member entryType input started
  obtain ⟨program, present⟩ := RecursiveNamedPublicHistoryRegistryExtension.diagnostics_present history
  have semanticAt : ∀ reason token, semanticFaults reason token →
      CallableIndexedOwnedPublicDecodedStagedCallFaults.faults receiving.result.diagnostics (.semantic reason) token := by
    intro reason token related
    exact CompatibleRegistryDiagnosticExtension.staged_preserved recipe.compiled
      receiver issued present extended (semantic reason token related)
  have metadata : SourceCoreRawMetadata.Extends encodedValues.registry receiving.result.context.registry := by
    rw [contextAt]
    exact .refl _
  refine ⟨receiving, contextAt, issued, extended, diagnostics, ?_⟩
  exact RecursiveNamedPublicDirectCallablePublicHistory.public_resume_succeeded
    (completion := receiving) issued stagePrepared profile observations receiving.result.extension
    semanticAt family namedTerminals namedSupport wellFormed retained entry member entryType input
    started metadata atCheckpoint resumed invocation

include receiver stagePrepared profile observations semantic family namedTerminals namedSupport wellFormed
  history entry member entryType input atRecipe in
/-- The original public invocation derives startup and the actual future
registry. Arbitrarily nested metadata-bearing inputs use their real encoder;
all previous function entries retain their captures at the reached heap. -/
theorem public_invoke_succeeded
    (atRegistry : session.RegistryAt completion.result.context.registry)
    {publicArtifact : SourceCoreExecution.Artifact}
    {publicSession : SourceCoreExecution.Session publicArtifact}
    {publicCompletion : SourceCoreExecution.Completion publicArtifact}
    {options : SourceCoreExecution.RunOptions}
    (atSession : publicSession.IndexedAt session)
    (invoked : publicSession.InvokeAt entry.handle argument options (.ok (.succeeded publicCompletion)))
    (invocation : Staging.Recursive.Scope) :
    ∃ (receiving : CallableIndexedOwnedPublicFaultReceivers.Receiver recipe.compiled.indexed)
      (checkpoint : Checkpoint artifact) (actual : Completion artifact)
      (generation : SourceCorePublicValues.ExportGeneration) (value : Core.Value) (finalStore : Store)
      (actualParameter actualResult : TypeSystem.Ty) (nativeParameter nativeResult : Core.Ty)
      (callable packed : Core.Value) (encodedValues : SourceCoreCompatibleValues.Context)
      (sources : List Dynamic.Value) (sourceSize : Nat) (outcome : Staging.Recursive.Outcome)
      (after : Dynamic.Heap) (finalMap : LocationMap) (finalWorld : StoreTyping)
      (reached : Caller headers keys finalMap finalWorld after finalStore),
      receiving.result.context = encodedValues ∧
      CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt recipe.compiled.indexed receiving.entry
        receiving.result.context.registry receiving.result.extension receiving.result.diagnostics ∧
      SourceCoreRawMetadata.Extends completion.result.context.registry receiving.result.context.registry ∧
      (∀ token, checkpoint.diagnostic token = .ok (receiving.result.diagnostics.diagnostic? token)) ∧
      StartAt session entry.handle argument options.inputValidationFuel checkpoint recipe world store
        actualParameter actualResult nativeParameter nativeResult callable packed encodedValues ∧
      SourceCoreRawMetadata.runtimeType actualParameter = SourceCoreRawMetadata.runtimeType parameter ∧
      SourceCoreRawMetadata.runtimeType actualResult = SourceCoreRawMetadata.runtimeType result ∧
      checkpoint.SucceededResultAt options.executionFuel options.outputValidationFuel generation value finalStore actual ∧
      publicCompletion.IndexedAt actual ∧
      Dynamic.ValuesPack sources packedSource ∧
      Staging.Recursive.Size.Applies (Program.ofChecked recipe.compiled.sourceProgram) callStages sourceSize
        invocation anchor.function.context before entry.source sources outcome after ∧
      ResultAt (registry := receiving.result.context.registry) functions caller anchor.function.context result nativeResult
        outcome after value finalStore finalMap finalWorld
        (CallableIndexedOwnedPublicDecodedStagedCallFaults.faults receiving.result.diagnostics) ∧
      Relates caller reached ∧
      History headers keys functions receiving.result.context.registry anchor actual.session
        finalMap finalWorld after finalStore reached entries ∧
      actual.session.RegistryAt encodedValues.registry := by
  obtain ⟨publicCheckpoint, accepted, resumed⟩ := invoked
  obtain ⟨checkpoint, atCheckpoint, original⟩ :=
    RecursiveNamedPublicDirectHandleMeaning.recover_handle_start atSession accepted
  have imported := (history.current.2.2.2.2 entry member).1
  rw [entryType] at imported
  obtain ⟨actualParameter, actualResult, nativeParameter, nativeResult, callable, packed, encodedValues,
    started, _parameterView, _resultView⟩ :=
    RecursiveNamedPublicDirectPackedInputMeaning.actual_start_compatible atRecipe history.current.1 imported original
  obtain ⟨receiving, contextAt, issued, extended, diagnostics, parameterView, resultView,
    actual, generation, value, finalStore, sources, sourceSize, outcome, after,
    finalMap, finalWorld, reached, _completed, succeeded, actualAt, packing, trace,
    resultAt, related, retained, returnedRegistry⟩ :=
    public_resume_succeeded receiver stagePrepared profile observations semantic family namedTerminals
      namedSupport wellFormed history entry member entryType input atRegistry started atCheckpoint resumed invocation
  exact ⟨receiving, checkpoint, actual, generation, value, finalStore, actualParameter, actualResult,
    nativeParameter, nativeResult, callable, packed, encodedValues, sources, sourceSize, outcome,
    after, finalMap, finalWorld, reached, contextAt, issued, extended, diagnostics, started, parameterView, resultView,
    succeeded, actualAt, packing, trace, resultAt, related, retained, returnedRegistry⟩

end Meaning
end Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicActualRegistryReflection
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicActualRegistryFailures
/-! Failed direct calls use the actual input metadata and retain the same
current Source captures and effects before failure for the next session. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicActualRegistryFailures
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open SourceCoreIndexedSession RecursiveNamedPublicStartMeaning
open RecursiveNamedPublicFunctionHistory (History Entry Caller)
open RecursiveNamedPublicDirectPackedInputMeaning (StartAt)
open RecursivePublicApplicationResult (ResultAt)
open CallableIndexedOwnedFunctionState
open CallableIndexedOwnedContextualTypedClosureReceipts (Association)

variable {recipe : Recipe}
variable
  {headers : List (CallableIndexedOwnedFunctionValues.Header recipe.compiled (Program.ofChecked recipe.compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key recipe.compiled (Program.ofChecked recipe.compiled.sourceProgram))}

section Meaning
variable {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver recipe.compiled.indexed}
  {bodyRegistry : SourceCoreRawMetadata.Registry} {semanticFaults : FunctionCalls.FaultRep}
  (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt recipe.compiled.indexed completion.entry
    completion.result.context.registry completion.result.extension completion.result.diagnostics)
  (stagePrepared : RecursiveNamedPreparedStageContracts.Prepared recipe.compiled
    recipe.compiled.indexed.ancestry.graph.inputs.callable)
  (profile : recipe.compiled.compatible.checked.catalog.callableContracts = true)
  {identities : Dynamic.Value → Word → Prop}
  (observations : CompatibleEquality.FunctionObservations recipe.compiled.compatible.checked.catalog
    (CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry semanticFaults profile) identities)
  (semantic : ∀ reason token, semanticFaults reason token →
    CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics (.semantic reason) token)
  (family : ∀ {mapping world function native bindings parameterCore resultCore}
    (association : Association headers keys bodyRegistry semanticFaults mapping world function native
      bindings parameterCore resultCore),
    CallableIndexedOwnedPreparedStagedOrdinarySequenceCallerBounds.OrdinarySequenceFor stagePrepared association)
  (namedTerminals : ∀ header, header ∈ headers →
    CallableIndexedOwnedPreparedStagedNamedBodies.Body header)
  (namedSupport : ∀ header (member : header ∈ headers),
    CallableIndexedOwnedPreparedStagedNamedBodiesSupport.Support headers keys bodyRegistry header
      (RecursiveNamedPreparedStageScopes.registry stagePrepared) (namedTerminals header member) semanticFaults)
  (wellFormed : ProgramWellFormed (Program.ofChecked recipe.compiled.sourceProgram))
  {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store : Store}
  {anchor : CallableIndexedOwnedFunctionValues.Header recipe.compiled (Program.ofChecked recipe.compiled.sourceProgram)}
  {caller : Caller headers keys mapping world before store}
  {artifact : Artifact} {session : Session artifact} {entries : List Entry}
  (history : History headers keys
    (CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry semanticFaults profile)
    completion.result.context.registry anchor session mapping world before store caller entries)
  (entry : Entry) (member : entry ∈ entries)
  {parameter result : TypeSystem.Ty}
  (entryType : entry.sourceType = .function parameter result)
  {argument : SourceCorePublicValues.Value} {packedSource : Dynamic.Value}
  (input : RecursiveNamedPublicFunctionHistoryInputs.Input entries anchor.function.context parameter argument packedSource)

  (atRecipe : ArtifactRecipe artifact recipe)

local notation "functions" => CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry semanticFaults profile
local notation "callStages" => RecursiveNamedPreparedStageScopes.registry stagePrepared

include receiver stagePrepared profile observations semantic family namedTerminals namedSupport wellFormed
  history entry member entryType input in
/-- A failed public resume reflects to Source at its actual input registry.
The exact after-heap, old captures and new receiver continue together. -/
theorem public_resume_failed_at_arity
    (atRegistry : session.RegistryAt completion.result.context.registry)
    {inputFuel : Nat} {checkpoint : Checkpoint artifact}
    {actualParameter actualResult : TypeSystem.Ty} {nativeParameter nativeResult : Core.Ty}
    {callable packed : Core.Value} {encodedValues : SourceCoreCompatibleValues.Context}
    (started : StartAt session entry.handle argument inputFuel checkpoint recipe world store
      actualParameter actualResult nativeParameter nativeResult callable packed encodedValues)
    {publicArtifact : SourceCoreExecution.Artifact}
    {publicCheckpoint : SourceCoreExecution.Checkpoint publicArtifact}
    {publicSession : SourceCoreExecution.Session publicArtifact}
    {executionFuel outputFuel : Nat} {reason : Word}
    (atCheckpoint : publicCheckpoint.IndexedAt checkpoint)
    (resumed : publicCheckpoint.ResumeAt executionFuel outputFuel (.failed reason publicSession))
    (invocation : Staging.Recursive.Scope) :
    ∃ receiving : CallableIndexedOwnedPublicFaultReceivers.Receiver recipe.compiled.indexed,
      receiving.result.context = encodedValues ∧
      CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt recipe.compiled.indexed receiving.entry
        receiving.result.context.registry receiving.result.extension receiving.result.diagnostics ∧
      SourceCoreRawMetadata.Extends completion.result.context.registry receiving.result.context.registry ∧
      (∀ token, checkpoint.diagnostic token = .ok (receiving.result.diagnostics.diagnostic? token)) ∧
    ∃ (actual : Session artifact) (value : Core.Value) (finalStore : Store)
      (sources : List Dynamic.Value) (sourceSize : Nat) (failure : Staging.Recursive.Failure)
      (after : Dynamic.Heap) (finalMap : LocationMap) (finalWorld : StoreTyping)
      (reached : Caller headers keys finalMap finalWorld after finalStore),
      checkpoint.FailedResultAt executionFuel value finalStore reason actual ∧
      publicSession.IndexedAt actual ∧
      Dynamic.ValuesPack sources packedSource ∧
      RecursivePublicCallableArity.Arity (Program.ofChecked recipe.compiled.sourceProgram) entry.source sources.length ∧
      Staging.Recursive.Size.Applies (Program.ofChecked recipe.compiled.sourceProgram) callStages sourceSize
        invocation anchor.function.context before entry.source sources (.fault failure) after ∧
      ResultAt (registry := receiving.result.context.registry) functions caller anchor.function.context result nativeResult
        (.fault failure) after value finalStore finalMap finalWorld
        (CallableIndexedOwnedPublicDecodedStagedCallFaults.faults receiving.result.diagnostics) ∧
      Relates caller reached ∧
      History headers keys functions receiving.result.context.registry anchor actual
        finalMap finalWorld after finalStore reached entries ∧
      actual.RegistryAt encodedValues.registry := by
  obtain ⟨receiving, _indexed, contextAt, issued, extended, retained, _represented, _typed, diagnostics⟩ :=
    RecursiveNamedPublicActualRegistryStart.packed_input history atRegistry member entryType input started
  obtain ⟨program, present⟩ := RecursiveNamedPublicHistoryRegistryExtension.diagnostics_present history
  have semanticAt : ∀ reason token, semanticFaults reason token →
      CallableIndexedOwnedPublicDecodedStagedCallFaults.faults receiving.result.diagnostics (.semantic reason) token := by
    intro reason token related
    exact CompatibleRegistryDiagnosticExtension.staged_preserved recipe.compiled
      receiver issued present extended (semantic reason token related)
  have metadata : SourceCoreRawMetadata.Extends encodedValues.registry receiving.result.context.registry := by
    rw [contextAt]
    exact .refl _
  refine ⟨receiving, contextAt, issued, extended, diagnostics, ?_⟩
  exact RecursiveNamedPublicDirectCallableFailures.public_resume_failed_at_arity
    (completion := receiving) issued stagePrepared profile observations receiving.result.extension
    semanticAt family namedTerminals namedSupport wellFormed retained entry member entryType input
    started metadata atCheckpoint resumed invocation

include receiver stagePrepared profile observations semantic family namedTerminals namedSupport wellFormed
  history entry member entryType input in
theorem public_resume_failed
    (atRegistry : session.RegistryAt completion.result.context.registry)
    {inputFuel : Nat} {checkpoint : Checkpoint artifact}
    {actualParameter actualResult : TypeSystem.Ty} {nativeParameter nativeResult : Core.Ty}
    {callable packed : Core.Value} {encodedValues : SourceCoreCompatibleValues.Context}
    (started : StartAt session entry.handle argument inputFuel checkpoint recipe world store
      actualParameter actualResult nativeParameter nativeResult callable packed encodedValues)
    {publicArtifact : SourceCoreExecution.Artifact}
    {publicCheckpoint : SourceCoreExecution.Checkpoint publicArtifact}
    {publicSession : SourceCoreExecution.Session publicArtifact}
    {executionFuel outputFuel : Nat} {reason : Word}
    (atCheckpoint : publicCheckpoint.IndexedAt checkpoint)
    (resumed : publicCheckpoint.ResumeAt executionFuel outputFuel (.failed reason publicSession))
    (invocation : Staging.Recursive.Scope) :
    ∃ receiving : CallableIndexedOwnedPublicFaultReceivers.Receiver recipe.compiled.indexed,
      receiving.result.context = encodedValues ∧
      CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt recipe.compiled.indexed receiving.entry
        receiving.result.context.registry receiving.result.extension receiving.result.diagnostics ∧
      SourceCoreRawMetadata.Extends completion.result.context.registry receiving.result.context.registry ∧
      (∀ token, checkpoint.diagnostic token = .ok (receiving.result.diagnostics.diagnostic? token)) ∧
    ∃ (actual : Session artifact) (value : Core.Value) (finalStore : Store)
      (sources : List Dynamic.Value) (sourceSize : Nat) (failure : Staging.Recursive.Failure)
      (after : Dynamic.Heap) (finalMap : LocationMap) (finalWorld : StoreTyping)
      (reached : Caller headers keys finalMap finalWorld after finalStore),
      checkpoint.FailedResultAt executionFuel value finalStore reason actual ∧
      publicSession.IndexedAt actual ∧
      Dynamic.ValuesPack sources packedSource ∧
      Staging.Recursive.Size.Applies (Program.ofChecked recipe.compiled.sourceProgram) callStages sourceSize
        invocation anchor.function.context before entry.source sources (.fault failure) after ∧
      ResultAt (registry := receiving.result.context.registry) functions caller anchor.function.context result nativeResult
        (.fault failure) after value finalStore finalMap finalWorld
        (CallableIndexedOwnedPublicDecodedStagedCallFaults.faults receiving.result.diagnostics) ∧
      Relates caller reached ∧
      History headers keys functions receiving.result.context.registry anchor actual
        finalMap finalWorld after finalStore reached entries ∧
      actual.RegistryAt encodedValues.registry := by
  obtain ⟨receiving, contextAt, issued, extended, diagnostics, actual, value, finalStore, sources, sourceSize, failure, after, finalMap, finalWorld, reached, failed, sessionAt, packing, _arity, rest⟩ := public_resume_failed_at_arity
    receiver stagePrepared profile observations semantic family namedTerminals namedSupport
      wellFormed history entry member entryType input atRegistry started atCheckpoint resumed invocation
  exact ⟨receiving, contextAt, issued, extended, diagnostics, actual, value, finalStore, sources, sourceSize, failure, after, finalMap, finalWorld, reached, failed, sessionAt, packing, rest⟩

include receiver stagePrepared profile observations semantic family namedTerminals namedSupport wellFormed
  history entry member entryType input atRecipe in
/-- The real public invocation supplies its own failed startup and receipt;
metadata-bearing arguments need no separate receiving extension assumption. -/
theorem public_invoke_failed
    (atRegistry : session.RegistryAt completion.result.context.registry)
    {publicArtifact : SourceCoreExecution.Artifact}
    {publicSession returned : SourceCoreExecution.Session publicArtifact}
    {options : SourceCoreExecution.RunOptions} {reason : Word}
    (atSession : publicSession.IndexedAt session)
    (invoked : publicSession.InvokeAt entry.handle argument options (.ok (.failed reason returned)))
    (invocation : Staging.Recursive.Scope) :
    ∃ (receiving : CallableIndexedOwnedPublicFaultReceivers.Receiver recipe.compiled.indexed)
      (checkpoint : Checkpoint artifact) (actual : Session artifact)
      (value : Core.Value) (finalStore : Store)
      (actualParameter actualResult : TypeSystem.Ty) (nativeParameter nativeResult : Core.Ty)
      (callable packed : Core.Value) (encodedValues : SourceCoreCompatibleValues.Context)
      (sources : List Dynamic.Value) (sourceSize : Nat) (failure : Staging.Recursive.Failure)
      (after : Dynamic.Heap) (finalMap : LocationMap) (finalWorld : StoreTyping)
      (reached : Caller headers keys finalMap finalWorld after finalStore),
      receiving.result.context = encodedValues ∧
      CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt recipe.compiled.indexed receiving.entry
        receiving.result.context.registry receiving.result.extension receiving.result.diagnostics ∧
      SourceCoreRawMetadata.Extends completion.result.context.registry receiving.result.context.registry ∧
      (∀ token, checkpoint.diagnostic token = .ok (receiving.result.diagnostics.diagnostic? token)) ∧
      StartAt session entry.handle argument options.inputValidationFuel checkpoint recipe world store
        actualParameter actualResult nativeParameter nativeResult callable packed encodedValues ∧
      SourceCoreRawMetadata.runtimeType actualParameter = SourceCoreRawMetadata.runtimeType parameter ∧
      SourceCoreRawMetadata.runtimeType actualResult = SourceCoreRawMetadata.runtimeType result ∧
      checkpoint.FailedResultAt options.executionFuel value finalStore reason actual ∧
      returned.IndexedAt actual ∧
      Dynamic.ValuesPack sources packedSource ∧
      Staging.Recursive.Size.Applies (Program.ofChecked recipe.compiled.sourceProgram) callStages sourceSize
        invocation anchor.function.context before entry.source sources (.fault failure) after ∧
      ResultAt (registry := receiving.result.context.registry) functions caller anchor.function.context result nativeResult
        (.fault failure) after value finalStore finalMap finalWorld
        (CallableIndexedOwnedPublicDecodedStagedCallFaults.faults receiving.result.diagnostics) ∧
      Relates caller reached ∧
      History headers keys functions receiving.result.context.registry anchor actual
        finalMap finalWorld after finalStore reached entries ∧
      actual.RegistryAt encodedValues.registry := by
  obtain ⟨publicCheckpoint, accepted, resumed⟩ := invoked
  obtain ⟨checkpoint, atCheckpoint, original⟩ :=
    RecursiveNamedPublicDirectHandleMeaning.recover_handle_start atSession accepted
  have imported := (history.current.2.2.2.2 entry member).1
  rw [entryType] at imported
  obtain ⟨actualParameter, actualResult, nativeParameter, nativeResult, callable, packed, encodedValues,
    started, parameterView, resultView⟩ :=
    RecursiveNamedPublicDirectPackedInputMeaning.actual_start_compatible atRecipe history.current.1 imported original
  obtain ⟨receiving, contextAt, issued, extended, diagnostics, actual, value, finalStore,
    sources, sourceSize, failure, after, finalMap, finalWorld, reached, failed, sessionAt,
    packing, trace, resultAt, related, retained, registry⟩ :=
    public_resume_failed receiver stagePrepared profile observations semantic family namedTerminals
      namedSupport wellFormed history entry member entryType input atRegistry started
      atCheckpoint resumed invocation
  exact ⟨receiving, checkpoint, actual, value, finalStore, actualParameter, actualResult, nativeParameter,
    nativeResult, callable, packed, encodedValues, sources, sourceSize, failure, after, finalMap,
    finalWorld, reached, contextAt, issued, extended, diagnostics, started, parameterView, resultView,
    failed, sessionAt, packing, trace, resultAt, related, retained, registry⟩

end Meaning
end Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicActualRegistryFailures
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicPhysicalHistory
/-! Public histories retain the complete physical cache together with the same
ordinary Source exports and actual caller pool. Whole-call administrative
preservation transports this authority across every exact returned session. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicPhysicalHistory
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open SourceCoreIndexedSession CallableIndexedOwnedFunctionState
open CallableIndexedOwnedFunctionValues (Header NamedCapture OwnedKey)
open RecursiveNamedPublicFunctionHistory (Caller Entry Result)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed)}
  {receiving : SourceCoreRawMetadata.Registry}
  {anchor : Header compiled (Program.ofChecked compiled.sourceProgram)}

structure History {artifact : Artifact} (session : Session artifact)
    (mapping : LocationMap) (world : StoreTyping) (heap : Dynamic.Heap) (store : Store)
    (caller : Caller headers keys mapping world heap store) (entries : List Entry) : Prop where
  semantic : RecursiveNamedPublicFunctionHistory.History headers keys functions receiving anchor
    session mapping world heap store caller entries
  physical : CallableIndexedOwnedPhysicalGlobals.Authority compiled mapping store

theorem physical_of_result
    {mapping : LocationMap} {world : StoreTyping} {heap : Dynamic.Heap} {store : Store}
    {owner : OwnedKey keys} {caller : Caller headers keys mapping world heap store}
    {header : Header compiled (Program.ofChecked compiled.sourceProgram)}
    {capture : NamedCapture headers owner.key header mapping world} {arguments : List Core.Value}
    {outcome : Staging.Recursive.Outcome} {after : Dynamic.Heap} {native : Core.Value} {finalStore : Store}
    {finalMap : LocationMap} {finalWorld : StoreTyping} {faults : RecursiveStageMeaning.FaultRep}
    (physical : CallableIndexedOwnedPhysicalGlobals.Authority compiled mapping store)
    (result : Result (functions := functions) (receiving := receiving) (anchor := anchor)
      owner caller header capture arguments outcome after native finalStore finalMap finalWorld faults) :
    CallableIndexedOwnedPhysicalGlobals.Authority compiled finalMap finalStore :=
  physical.extend result.2.2.2.2.2.1

/-- The supplied history is the original public history at the actual result;
only its physical cache proof is added from whole-call preservation. -/
theorem History.after_result
    {artifact : Artifact} {session : Session artifact}
    {mapping : LocationMap} {world : StoreTyping} {heap : Dynamic.Heap} {store : Store}
    {owner : OwnedKey keys} {caller : Caller headers keys mapping world heap store} {entries : List Entry}
    (prior : History (functions := functions) (receiving := receiving) (anchor := anchor)
      session mapping world heap store caller entries)
    {header : Header compiled (Program.ofChecked compiled.sourceProgram)}
    {capture : NamedCapture headers owner.key header mapping world} {arguments : List Core.Value}
    {outcome : Staging.Recursive.Outcome} {after : Dynamic.Heap} {native : Core.Value} {finalStore : Store}
    {finalMap : LocationMap} {finalWorld : StoreTyping} {faults : RecursiveStageMeaning.FaultRep}
    (result : Result (functions := functions) (receiving := receiving) (anchor := anchor)
      owner caller header capture arguments outcome after native finalStore finalMap finalWorld faults)
    {nextSession : Session artifact} {reached : Caller headers keys finalMap finalWorld after finalStore}
    {nextEntries : List Entry}
    (next : RecursiveNamedPublicFunctionHistory.History headers keys functions receiving anchor
      nextSession finalMap finalWorld after finalStore reached nextEntries) :
    History (functions := functions) (receiving := receiving) (anchor := anchor)
      nextSession finalMap finalWorld after finalStore reached nextEntries :=
  ⟨next, physical_of_result prior.physical result⟩

/-- The stronger public caller wraps the identical reached pool. -/
def History.caller {artifact : Artifact} {session : Session artifact}
    {mapping : LocationMap} {world : StoreTyping} {heap : Dynamic.Heap} {store : Store}
    {caller : Caller headers keys mapping world heap store} {entries : List Entry}
    (history : History (functions := functions) (receiving := receiving) (anchor := anchor)
      session mapping world heap store caller entries) :
    CallableIndexedOwnedPhysicalState.PoolState headers keys
      ⟨[], mapping, world, heap, store, SourceCoreCallableIndexedTemplates.globalEnvironment compiled.indexed⟩ :=
  ⟨caller, history.physical⟩

/-- The public session's actual global environment supplies the full canonical
slot layout for the next call, paired with its reached physical cache. -/
def History.canonical_caller {artifact : Artifact} {session : Session artifact}
    {mapping : LocationMap} {world : StoreTyping} {heap : Dynamic.Heap} {store : Store}
    {caller : Caller headers keys mapping world heap store} {entries : List Entry}
    (history : History (functions := functions) (receiving := receiving) (anchor := anchor)
      session mapping world heap store caller entries) :
    (CallableIndexedOwnedPhysicalCanonicalState.protocol headers keys 0).State
      ⟨[], mapping, world, heap, store, SourceCoreCallableIndexedTemplates.globalEnvironment compiled.indexed⟩ :=
  ⟨⟨caller, CallableIndexedOwnedPhysicalGlobals.environment_slots compiled⟩, history.physical⟩

end Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicPhysicalHistory
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicPhysicalClosureHistory
/-! Public history is instantiated directly with positive physical closure
origins. Original export and reimport receipts preserve those origins through
containers, repeated handles, and actual returned sessions. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicPhysicalClosureHistory
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open SourceCoreIndexedSession CallableIndexedOwnedFunctionState
open CallableIndexedOwnedFunctionValues (Header Key)
open RecursiveNamedPublicFunctionHistory (Caller Entry)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (Key compiled (Program.ofChecked compiled.sourceProgram))}
  {bodyRegistry receiving : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {profile : compiled.compatible.checked.catalog.callableContracts = true}
  {anchor : Header compiled (Program.ofChecked compiled.sourceProgram)}

local notation "rootFunctions" => CallableIndexedOwnedPhysicalCellOrigins.functions headers keys bodyRegistry faults profile

abbrev History {artifact : Artifact} (session : Session artifact)
    (mapping : LocationMap) (world : StoreTyping) (heap : Dynamic.Heap) (store : Store)
    (caller : Caller headers keys mapping world heap store) (entries : List Entry) : Prop :=
  RecursiveNamedPublicPhysicalHistory.History (functions := rootFunctions) (receiving := receiving) (anchor := anchor)
    session mapping world heap store caller entries

/-- The original history supplies positive captured members, the current heap,
and the exact physical cache. The actual input encoder chooses each retained
handle at its original argument position. -/
theorem History.current_arguments
    {artifact : Artifact} {session : Session artifact} {entries : List Entry}
    {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store : Store}
    {caller : Caller headers keys mapping world before store}
    (history : History (bodyRegistry := bodyRegistry) (faults := faults) (profile := profile)
      (receiving := receiving) (anchor := anchor) session mapping world before store caller entries)
    {recipe : Recipe} (prepared : Recipe.prepare compiled = .ok recipe)
    {root : Root compiled} {header : Header compiled (Program.ofChecked compiled.sourceProgram)}
    (selected : RecursiveNamedPublicRootMeaning.RootSelection
      (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      (program := Program.ofChecked compiled.sourceProgram) headers root header)
    {checkpoint : Checkpoint artifact} {key : SourceCoreIndexedSession.Key}
    {publicArguments : List SourceCorePublicValues.Value} {inputFuel : Nat}
    {payloads : Environment} {encodedValues : SourceCoreCompatibleValues.Context}
    (started : RecursiveNamedPublicStartMeaning.StartAt session key publicArguments inputFuel checkpoint recipe
      ((Recipe.prepare_compiled prepared).symm ▸ root) world store payloads encodedValues)
    {arguments : List Dynamic.Value}
    (inputReceipts : RecursiveNamedPublicFunctionHistoryInputs.Inputs entries header.function.context
      (header.bindings.map (fun binding => binding.1.scheme.body)) publicArguments arguments)
    (metadata : SourceCoreRawMetadata.Extends encodedValues.registry receiving)
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram)) :
    CallableIndexedOwnedIndirectExpressionHeads.StableRows caller ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked receiving rootFunctions
        mapping world before store ∧
      Dynamic.HeapWellTyped header.function.context before ∧
      CallableIndexedParameterMeaning.Arguments
        (CompatibleAmbientHeap.payloadModel compiled.compatible.checked receiving rootFunctions)
        mapping world header.bindings arguments payloads ∧
      Dynamic.ValuesHaveTypes header.function.context before arguments header.types := by
  have sameCompiled := Recipe.prepare_compiled prepared
  cases sameCompiled
  obtain ⟨_nativeAt, heaps, stable, heapTyped, retained⟩ := history.semantic.current
  have contexts := RecursiveNamedPublicReturnedValues.header_context_supports anchor header wellFormed
  obtain ⟨represented, argumentsTyped⟩ :=
    RecursiveNamedPublicFunctionHistoryArgumentsReceiving.StartAt.history_arguments_receiving
      started _ selected entries (fun entry member => (retained entry member).1)
      (fun entry member => (retained entry member).2.1)
      (fun entry member => (retained entry member).2.2.transportContext contexts.1)
      inputReceipts metadata wellFormed
  exact ⟨stable, heaps, heapTyped.transportContext contexts.1, represented, argumentsTyped⟩

end Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicPhysicalClosureHistory
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicActualRegistryNamedStart
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicActualRegistryNamedStart
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open SourceCoreIndexedSession CallableIndexedOwnedFunctionState
open RecursiveNamedPublicFunctionHistory (History Entry Caller)
open CallableIndexedOwnedPublicFaultReceivers

variable {recipe : Recipe}
  {headers : List (CallableIndexedOwnedFunctionValues.Header recipe.compiled (Program.ofChecked recipe.compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key recipe.compiled (Program.ofChecked recipe.compiled.sourceProgram))}
  {functions : FunctionModel recipe.compiled.compatible.checked.catalog
    (CallableIndexedAmbient.ambientDefinitions recipe.compiled.indexed)}
  {registry : SourceCoreRawMetadata.Registry}
  {anchor : CallableIndexedOwnedFunctionValues.Header recipe.compiled (Program.ofChecked recipe.compiled.sourceProgram)}
  {mapping : LocationMap} {world : StoreTyping} {heap : Dynamic.Heap} {store : Store}
  {caller : Caller headers keys mapping world heap store}
  {artifact : Artifact} {session : Session artifact} {entries : List Entry}

/-- Named input encoding chooses the receiver and transports the entire
retained history along its actual forward metadata extension. -/
theorem named_start
    (history : History headers keys functions registry anchor session mapping world heap store caller entries)
    (atRegistry : session.RegistryAt registry)
    {root : Root recipe.compiled} {key : SourceCoreIndexedSession.Key}
    {arguments : List SourceCorePublicValues.Value} {inputFuel : Nat}
    {checkpoint : Checkpoint artifact} {native : Environment}
    {encodedValues : SourceCoreCompatibleValues.Context}
    (started : RecursiveNamedPublicStartMeaning.StartAt session key arguments inputFuel
      checkpoint recipe root world store native encodedValues) :
    ∃ receiver : Receiver recipe.compiled.indexed,
      receiver.entry ∈ recipe.compiled.indexed.entries ∧
      receiver.result.context = encodedValues ∧
      CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt recipe.compiled.indexed receiver.entry
        receiver.result.context.registry receiver.result.extension receiver.result.diagnostics ∧
      SourceCoreRawMetadata.Extends registry receiver.result.context.registry ∧
      History headers keys functions receiver.result.context.registry anchor
        session mapping world heap store caller entries ∧
      ∀ token, checkpoint.diagnostic token = .ok (receiver.result.diagnostics.diagnostic? token) := by
  obtain ⟨extended, retained⟩ :=
    RecursiveNamedPublicHistoryRegistryExtension.at_named_start history atRegistry started
  obtain ⟨indexed, indexedMember⟩ := RecursiveNamedPublicHistoryRegistryExtension.indexed_entry history
  obtain ⟨receiver, indexedAt, contextAt, issued⟩ :=
    Receiver.at_context recipe.compiled indexed encodedValues started.owner
  obtain ⟨program, present⟩ := RecursiveNamedPublicHistoryRegistryExtension.diagnostics_present history
  refine ⟨receiver, indexedAt ▸ indexedMember, contextAt, issued, ?_, ?_,
    fun token => RecursiveNamedPublicCheckpointReceiver.diagnostic_eq
      started.recipe_eq started.values contextAt issued present token⟩
  · rw [contextAt]; exact extended
  · rw [contextAt]; exact retained

end Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicActualRegistryNamedStart
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicActualRegistryNamedOutputPreservation
/-! Source success of a following named call produces sufficient public fuel
and a reusable history at the actual input registry. Current history provides
heap, arguments and captured functions; output follows from representation. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicActualRegistryNamedOutputPreservation
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState
open CallableIndexedOwnedPreparedBootstrapRootState (keys owner)
open CallableIndexedOwnedPreparedFiniteNamedInventories (Input Inventory headers)
open CallableIndexedOwnedContextualTypedClosureReceipts (Association)
open CallableIndexedOwnedPreparedStagedOrdinarySequenceCallerBounds (OrdinarySequenceFor)
open CallableIndexedOwnedPreparedStagedNamedBodies (Body)
open CallableIndexedOwnedPreparedStagedNamedBodiesSupport (Support)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
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
  {root : SourceCoreIndexedSession.Root compiled}
  {header : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)}
  (selected : RecursiveNamedPublicRootMeaning.RootSelection
    (values := .initial compiled.compatible.checked)
    (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
    (program := Program.ofChecked compiled.sourceProgram) (headers rows) root header)
  {nativeArtifact : SourceCoreIndexedSession.Artifact}
  {nativeSession : SourceCoreIndexedSession.Session nativeArtifact}
  {anchor : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)}
  {entries : List RecursiveNamedPublicFunctionHistory.Entry}
  {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store : Store}
  (caller : State (headers rows) (keys compiled)
    ⟨[], mapping, world, before, store, SourceCoreCallableIndexedTemplates.globalEnvironment compiled.indexed⟩)
  (history : RecursiveNamedPublicFunctionHistory.History (headers rows) (keys compiled)
    (CallableIndexedOwnedContextualCellOrigins.functions (headers rows) (keys compiled)
      bodyRegistry semanticFaults profile) completion.result.context.registry anchor
    nativeSession mapping world before store caller entries)
  {publicArtifact : SourceCoreExecution.Artifact}
  {publicSession : SourceCoreExecution.Session publicArtifact}
  {publicCheckpoint : SourceCoreExecution.Checkpoint publicArtifact}
  {nativeCheckpoint : SourceCoreIndexedSession.Checkpoint nativeArtifact}
  {key : SourceCoreIndexedSession.Key} {options : SourceCoreExecution.RunOptions}
  {publicArguments : List SourceCorePublicValues.Value} {arguments : List Dynamic.Value}
  {payloads : Environment} {encodedValues : SourceCoreCompatibleValues.Context}
  (atCheckpoint : publicCheckpoint.IndexedAt nativeCheckpoint)
  (started : RecursiveNamedPublicStartMeaning.StartAt nativeSession key publicArguments
    options.inputValidationFuel nativeCheckpoint recipe
    ((SourceCoreIndexedSession.Recipe.prepare_compiled prepared).symm ▸ root)
    world store payloads encodedValues)
  (inputReceipts : RecursiveNamedPublicFunctionHistoryInputs.Inputs entries
    header.function.context (header.bindings.map (fun binding => binding.1.scheme.body))
    publicArguments arguments)
  (atRegistry : nativeSession.RegistryAt completion.result.context.registry)
  (exportsReady : nativeSession.ExportsReady)
  {rawD : SourceTypedRuntime.RuntimeEvidenceEnvironment} {function : Dynamic.GlobalFunction}
  (sourceAt : CallableIndexedOwnedFunctionValues.NamedSourceAt header rawD function)
  {invocation : Staging.Recursive.Scope}

local notation "rootHeaders" => headers rows
local notation "rootKeys" => keys compiled
local notation "rootOwner" => owner compiled
local notation "rootFunctions" => CallableIndexedOwnedContextualCellOrigins.functions rootHeaders rootKeys bodyRegistry semanticFaults profile
local notation "rootModel" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked completion.result.context.registry rootFunctions
local notation "rootFaults" => CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics

include receiver observations semantic family namedTerminals namedSupport wellFormed
  prepared selected history atCheckpoint started inputReceipts sourceAt atRegistry exportsReady in
/-- A following named call keeps all prior captures and ordered entries at its
actual returned session. Both fuel bounds follow from the independent Source
success; native completion and successful export are conclusions. -/
theorem public_resume_has_sufficient_fuel
    {sourceSize : Nat} {sourceResult : Dynamic.Value} {after : Dynamic.Heap}
    (trace : Staging.Recursive.Size.Applies (Program.ofChecked compiled.sourceProgram)
      (RecursiveNamedPreparedStageScopes.registry stagePrepared) sourceSize invocation anchor.function.context before
      (.global function) arguments (.value sourceResult) after) :
    ∃ receiving : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed,
      receiving.result.context = encodedValues ∧
      CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt compiled.indexed receiving.entry
        receiving.result.context.registry receiving.result.extension receiving.result.diagnostics ∧
      SourceCoreRawMetadata.Extends completion.result.context.registry receiving.result.context.registry ∧
      (∀ token, nativeCheckpoint.diagnostic token = .ok (receiving.result.diagnostics.diagnostic? token)) ∧
    ∃ (capture : CallableIndexedOwnedFunctionValues.NamedCapture rootHeaders (rootOwner).key header mapping world)
      (payload : Core.Value) (finalStore : Store) (finalMap : LocationMap) (finalWorld : StoreTyping)
      (requiredExecution requiredOutput : Nat),
      (∀ executionFuel, requiredExecution ≤ executionFuel →
        nativeCheckpoint.NativeDone executionFuel (.inRight .word payload) finalStore) ∧
      CallableIndexedOwnedPreparedStagedTerminalNamedInvocationBounds.ResultAt
        (registry := receiving.result.context.registry) (payloads := payloads)
        (scope := []) (canonical := SourceCoreCallableIndexedTemplates.globalEnvironment compiled.indexed)
        rootFunctions rootOwner caller header capture anchor.function.context (.value sourceResult) after
        (.inRight .word payload) finalStore finalMap finalWorld
        (CallableIndexedOwnedPublicDecodedStagedCallFaults.faults receiving.result.diagnostics) ∧
      ∀ executionFuel outputFuel (outcome : SourceCoreExecution.Outcome publicArtifact),
        requiredExecution ≤ executionFuel → requiredOutput ≤ outputFuel →
        publicCheckpoint.ResumeAt executionFuel outputFuel outcome →
        ∃ (publicCompletion : SourceCoreExecution.Completion publicArtifact)
          (actual : SourceCoreIndexedSession.Completion nativeArtifact)
          (generation : SourceCorePublicValues.ExportGeneration)
          (reached : RecursiveNamedPublicFunctionHistory.Caller rootHeaders rootKeys finalMap finalWorld after finalStore),
          outcome = .succeeded publicCompletion ∧
          nativeCheckpoint.SucceededResultAt executionFuel outputFuel generation (.inRight .word payload) finalStore actual ∧
          publicCompletion.IndexedAt actual ∧ Relates caller reached ∧
          RecursiveNamedPublicFunctionHistory.History rootHeaders rootKeys rootFunctions
            receiving.result.context.registry anchor actual.session finalMap finalWorld after finalStore reached entries ∧
          actual.session.RegistryAt encodedValues.registry ∧ actual.session.ExportsReady := by
  have sameCompiled := SourceCoreIndexedSession.Recipe.prepare_compiled prepared
  cases sameCompiled
  have atRecipe : nativeArtifact.RecipeAt recipe := by
    cases nativeArtifact
    exact started.recipe_eq
  obtain ⟨receiving, _member, contextAt, issued, extended, retained, diagnostics⟩ :=
    RecursiveNamedPublicActualRegistryNamedStart.named_start history atRegistry started
  obtain ⟨program, present⟩ := RecursiveNamedPublicHistoryRegistryExtension.diagnostics_present history
  have semanticAt : ∀ reason token, semanticFaults reason token →
      CallableIndexedOwnedPublicDecodedStagedCallFaults.faults receiving.result.diagnostics (.semantic reason) token := by
    intro reason token related
    exact CompatibleRegistryDiagnosticExtension.staged_preserved recipe.compiled
      receiver issued present extended (semantic reason token related)
  have metadata : SourceCoreRawMetadata.Extends encodedValues.registry receiving.result.context.registry := by
    rw [contextAt]
    exact .refl _
  obtain ⟨stable, heaps, heapTyped, represented, argumentsTyped⟩ :=
    CallableIndexedOwnedPreparedStagedHistoryPublicBounds.current_arguments
      (completion := receiving) (inputs := inputs) (rows := rows) (profile := profile)
      (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults)
      (wellFormed := wellFormed) (prepared := prepared) (selected := selected)
      (history := retained) (started := started) (inputReceipts := inputReceipts) (metadata := metadata)
  have globalReference := CallableIndexedOwnedPreparedBootstrapGlobalReferences.global_reference rows header selected.member
  obtain ⟨capture, value, finalStore, finalMap, finalWorld, requiredExecution, enough, result⟩ :=
    CallableIndexedOwnedPreparedStagedOrdinarySequenceCallerBounds.preserves_root
      (stagePrepared := stagePrepared) (receiver := issued) (profile := profile)
      (observations := observations) (extension := receiving.result.extension) (semantic := semanticAt)
      (family := family) (namedTerminals := namedTerminals) (namedSupport := namedSupport)
      (acceptedPlan := SourceCoreUnifiedPreparationCertificates.compiled_planPrepared recipe.compiled)
      (wellFormed := wellFormed) (selected := selected) (owner := owner recipe.compiled)
      (caller := caller) (globalReference := globalReference) (stable := stable)
      (heapTyped := heapTyped) (argumentsTyped := argumentsTyped) (represented := represented)
      (heaps := heaps) (sourceAt := sourceAt)
      (supports := (RecursiveNamedPublicReturnedValues.header_context_supports header anchor wellFormed).2) trace
  obtain ⟨payload, rfl⟩ : ∃ payload, value = .inRight .word payload := by
    have representedResult := result.2.1
    cases representedResult with
    | value represented => exact ⟨_, rfl⟩
  have completes : ∀ executionFuel, requiredExecution ≤ executionFuel →
      nativeCheckpoint.NativeDone executionFuel (.inRight .word payload) finalStore :=
    fun fuel bound => started.initial.native_done_iff.mpr (enough fuel bound)
  have representedResult : ValueRep recipe.compiled.compatible.checked receiving.result.context.registry
      (CallableIndexedOwnedContextualCellOrigins.functions (headers rows) (keys recipe.compiled)
        bodyRegistry semanticFaults profile)
      finalMap finalWorld header.function.resultType sourceResult payload header.output := by
    have representedResult := result.2.1
    cases representedResult with
    | value related => exact related
  have shape : SourceCorePublicOutputShapes.Output recipe.compiled.compatible.checked encodedValues.registry
      (finalStore.map Core.Value.type) recipe.program.layouts.definitions header.function.resultType payload := by
    have shaped := CompatiblePublicOutputShapes.ValueRep.output representedResult
    rw [contextAt] at shaped
    rw [result.2.2.1.runtime_hasTypes.world_eq] at shaped
    exact shaped
  have checkpointRegistry : nativeCheckpoint.RegistryAt encodedValues.registry := by
    have values := started.values
    cases nativeCheckpoint
    change _ = encodedValues at values
    exact congrArg SourceCoreCompatibleValues.Context.registry values
  have requested := started.original.result_type_at atRecipe started.selected
  have rawResult := (RecursiveNamedPublicRootSourceSignature.inputs_and_result selected).2
  rw [rawResult] at requested
  have checkpointReady := started.original.initial_registry.exportsReady exportsReady
  obtain ⟨requiredOutput, exports⟩ := publicCheckpoint.output_succeeded_uniform
    atCheckpoint atRecipe checkpointRegistry checkpointReady requested shape
  refine ⟨receiving, contextAt, issued, extended, diagnostics, capture, payload,
    finalStore, finalMap, finalWorld, requiredExecution, requiredOutput, completes, result, ?_⟩
  intro executionFuel outputFuel outcome executionBound outputBound resumed
  obtain ⟨publicCompletion, actual, generation, succeeded, exported, actualAt, returnedReady⟩ :=
    exports executionFuel (completes executionFuel executionBound) outputFuel outputBound outcome resumed
  obtain ⟨reached, related, retained⟩ :=
    retained.after_success rfl started selected exported result
  exact ⟨publicCompletion, actual, generation, reached, succeeded, exported, actualAt,
    related, retained, started.returned_registry exported, returnedReady⟩


include receiver observations semantic family namedTerminals namedSupport wellFormed
  prepared selected history atCheckpoint started inputReceipts sourceAt atRegistry exportsReady in
/-- Independent Source failure of the actual ordered named call fixes the
public token and reached heap for every sufficient execution budget. Output
fuel may be zero; the failed session retains earlier captures and export authority. -/
theorem public_resume_fault_has_sufficient_fuel
    {sourceSize : Nat} {failure : Staging.Recursive.Failure} {after : Dynamic.Heap}
    (trace : Staging.Recursive.Size.Applies (Program.ofChecked compiled.sourceProgram)
      (RecursiveNamedPreparedStageScopes.registry stagePrepared) sourceSize invocation anchor.function.context before
      (.global function) arguments (.fault failure) after) :
    ∃ receiving : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed,
      receiving.result.context = encodedValues ∧
      CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt compiled.indexed receiving.entry
        receiving.result.context.registry receiving.result.extension receiving.result.diagnostics ∧
      SourceCoreRawMetadata.Extends completion.result.context.registry receiving.result.context.registry ∧
      (∀ token, nativeCheckpoint.diagnostic token = .ok (receiving.result.diagnostics.diagnostic? token)) ∧
    ∃ (capture : CallableIndexedOwnedFunctionValues.NamedCapture rootHeaders (rootOwner).key header mapping world)
      (token : Word) (finalStore : Store) (finalMap : LocationMap) (finalWorld : StoreTyping) (required : Nat),
      (CallableIndexedOwnedPublicDecodedStagedCallFaults.faults receiving.result.diagnostics) failure token ∧
      (∀ executionFuel, required ≤ executionFuel →
        nativeCheckpoint.NativeDone executionFuel (.inLeft header.output (.word token)) finalStore) ∧
      CallableIndexedOwnedPreparedStagedTerminalNamedInvocationBounds.ResultAt
        (registry := receiving.result.context.registry) (payloads := payloads)
        (scope := []) (canonical := SourceCoreCallableIndexedTemplates.globalEnvironment compiled.indexed)
        rootFunctions rootOwner caller header capture anchor.function.context (.fault failure) after
        (.inLeft header.output (.word token)) finalStore finalMap finalWorld (CallableIndexedOwnedPublicDecodedStagedCallFaults.faults receiving.result.diagnostics) ∧
      ∀ executionFuel outputFuel (outcome : SourceCoreExecution.Outcome publicArtifact),
        required ≤ executionFuel → publicCheckpoint.ResumeAt executionFuel outputFuel outcome →
        ∃ (returned : SourceCoreExecution.Session publicArtifact)
          (actual : SourceCoreIndexedSession.Session nativeArtifact)
          (reached : RecursiveNamedPublicFunctionHistory.Caller rootHeaders rootKeys finalMap finalWorld after finalStore),
          outcome = .failed token returned ∧
          nativeCheckpoint.FailedResultAt executionFuel (.inLeft header.output (.word token)) finalStore token actual ∧
          returned.IndexedAt actual ∧ Relates caller reached ∧
          RecursiveNamedPublicFunctionHistory.History rootHeaders rootKeys rootFunctions
            receiving.result.context.registry anchor actual finalMap finalWorld after finalStore reached entries ∧
          actual.RegistryAt encodedValues.registry ∧ actual.ExportsReady := by
  have sameCompiled := SourceCoreIndexedSession.Recipe.prepare_compiled prepared
  cases sameCompiled
  have atRecipe : nativeArtifact.RecipeAt recipe := by
    cases nativeArtifact
    exact started.recipe_eq
  obtain ⟨receiving, _member, contextAt, issued, extended, retained, diagnostics⟩ :=
    RecursiveNamedPublicActualRegistryNamedStart.named_start history atRegistry started
  obtain ⟨program, present⟩ := RecursiveNamedPublicHistoryRegistryExtension.diagnostics_present history
  have semanticAt : ∀ reason token, semanticFaults reason token →
      CallableIndexedOwnedPublicDecodedStagedCallFaults.faults receiving.result.diagnostics (.semantic reason) token := by
    intro reason token related
    exact CompatibleRegistryDiagnosticExtension.staged_preserved recipe.compiled
      receiver issued present extended (semantic reason token related)
  have metadata : SourceCoreRawMetadata.Extends encodedValues.registry receiving.result.context.registry := by
    rw [contextAt]
    exact .refl _
  obtain ⟨stable, heaps, heapTyped, represented, argumentsTyped⟩ :=
    CallableIndexedOwnedPreparedStagedHistoryPublicBounds.current_arguments
      (completion := receiving) (inputs := inputs) (rows := rows) (profile := profile)
      (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults)
      (wellFormed := wellFormed) (prepared := prepared) (selected := selected)
      (history := retained) (started := started) (inputReceipts := inputReceipts) (metadata := metadata)
  have globalReference := CallableIndexedOwnedPreparedBootstrapGlobalReferences.global_reference rows header selected.member
  obtain ⟨capture, value, finalStore, finalMap, finalWorld, required, enough, result⟩ :=
    CallableIndexedOwnedPreparedStagedOrdinarySequenceCallerBounds.preserves_root
      (stagePrepared := stagePrepared) (receiver := issued) (profile := profile)
      (observations := observations) (extension := receiving.result.extension) (semantic := semanticAt)
      (family := family) (namedTerminals := namedTerminals) (namedSupport := namedSupport)
      (acceptedPlan := SourceCoreUnifiedPreparationCertificates.compiled_planPrepared recipe.compiled)
      (wellFormed := wellFormed) (selected := selected) (owner := owner recipe.compiled)
      (caller := caller) (globalReference := globalReference) (stable := stable)
      (heapTyped := heapTyped) (argumentsTyped := argumentsTyped) (represented := represented)
      (heaps := heaps) (sourceAt := sourceAt)
      (supports := (RecursiveNamedPublicReturnedValues.header_context_supports header anchor wellFormed).2) trace
  obtain ⟨token, valueEq, faultRelated⟩ : ∃ token,
      value = .inLeft header.output (.word token) ∧
      CallableIndexedOwnedPublicDecodedStagedCallFaults.faults receiving.result.diagnostics failure token := by
    have representation := result.2.1
    cases representation with
    | fault related => exact ⟨_, rfl, related⟩
  subst value
  have completes : ∀ executionFuel, required ≤ executionFuel →
      nativeCheckpoint.NativeDone executionFuel (.inLeft header.output (.word token)) finalStore :=
    fun fuel bound => started.initial.native_done_iff.mpr (enough fuel bound)
  have supports := (RecursiveNamedPublicReturnedValues.header_context_supports header anchor wellFormed).1
  have callerHeap := heapTyped.transportContext supports
  have callerArguments := argumentsTyped.transportContext supports
  obtain ⟨packed, packing⟩ := Dynamic.ValuesPack.exists_pack arguments
  have preserved := Staging.Recursive.FaultPreservation.applies wellFormed
    (RecursiveNamedPublicHistorySourceInputs.header_runtime wellFormed anchor) callerHeap
    (RecursiveNamedPublicHistorySourceInputs.source_typed wellFormed sourceAt anchor before)
    packing (packing.hasType callerArguments) trace
  have checkpointReady := started.original.initial_registry.exportsReady exportsReady
  refine ⟨receiving, contextAt, issued, extended, diagnostics,
    capture, token, finalStore, finalMap, finalWorld, required, faultRelated, completes, result, ?_⟩
  intro executionFuel outputFuel outcome bound resumed
  have completed := completes executionFuel bound
  obtain ⟨returned, outcomeEq⟩ := resumed.native_failed atCheckpoint completed rfl
  have failedResume : publicCheckpoint.ResumeAt executionFuel outputFuel (.failed token returned) := outcomeEq ▸ resumed
  obtain ⟨actual, _generation, actualValue, actualStore, actualCompleted, failed, returnedAt⟩ :=
    failedResume.indexed_failed atCheckpoint
  have same := completed.symm.trans actualCompleted
  cases same
  obtain ⟨reached, related, continued⟩ :=
    retained.after_failure rfl started selected failed result preserved.1
  have returnedRegistry : actual.RegistryAt encodedValues.registry := by
    have values := failed.2.2.2.2.1.trans started.values
    cases nativeCheckpoint
    exact congrArg SourceCoreCompatibleValues.Context.registry values
  exact ⟨returned, actual, reached, outcomeEq, failed, returnedAt, related, continued, returnedRegistry, failed.exportsReady checkpointReady⟩


end Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicActualRegistryNamedOutputPreservation
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicPhysicalDirectCallableHistory
/-! Actual history and input encoding supply direct callable arguments.
The retained callable may be named, builtin or a closure. Source and host raw
signatures remain distinct, and the complete returned caller is retained. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicPhysicalDirectCallableHistory
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open SourceCoreIndexedSession RecursiveNamedPublicStartMeaning
open RecursiveNamedPublicFunctionHistory (History Entry Caller)
open RecursiveNamedPublicDirectPackedInputMeaning (StartAt)
open RecursivePublicApplicationResult (ResultAt)
open CallableIndexedOwnedFunctionState
open CallableIndexedOwnedContextualTypedClosureReceipts (Association)

variable {recipe : Recipe}
variable
  {headers : List (CallableIndexedOwnedFunctionValues.Header recipe.compiled (Program.ofChecked recipe.compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key recipe.compiled (Program.ofChecked recipe.compiled.sourceProgram))}

section Meaning
variable {initial completion : CallableIndexedOwnedPublicFaultReceivers.Receiver recipe.compiled.indexed}
  (support : CallableIndexedOwnedPreparedPhysicalProgramSupport.Support recipe.compiled headers keys initial)
  (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt recipe.compiled.indexed completion.entry
    completion.result.context.registry completion.result.extension completion.result.diagnostics)
  (extension : SourceCoreRawMetadata.Extends initial.result.context.registry completion.result.context.registry)
  {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store : Store}
  {anchor : CallableIndexedOwnedFunctionValues.Header recipe.compiled (Program.ofChecked recipe.compiled.sourceProgram)}
  {caller : Caller headers keys mapping world before store}
  {artifact : Artifact} {session : Session artifact} {entries : List Entry}
  (history : History headers keys
    (CallableIndexedOwnedPreparedPhysicalProgramSupport.functions support)
    completion.result.context.registry anchor session mapping world before store caller entries)
  (physical : CallableIndexedOwnedPhysicalGlobals.Authority recipe.compiled mapping store)
  (entry : Entry) (member : entry ∈ entries)
  {parameter result actualParameter actualResult : TypeSystem.Ty}
  (entryType : entry.sourceType = .function parameter result)
  {argument : SourceCorePublicValues.Value} {packedSource : Dynamic.Value}
  (input : RecursiveNamedPublicFunctionHistoryInputs.Input entries anchor.function.context parameter argument packedSource)
  {checkpoint : Checkpoint artifact} {inputFuel : Nat}
  {nativeParameter nativeResult : Core.Ty} {callable packed : Core.Value}
  {encodedValues : SourceCoreCompatibleValues.Context}
  (started : StartAt session entry.handle argument inputFuel checkpoint recipe world store
    actualParameter actualResult nativeParameter nativeResult callable packed encodedValues)
  (parameterView : SourceCoreRawMetadata.runtimeType parameter = SourceCoreRawMetadata.runtimeType actualParameter)
  (metadata : SourceCoreRawMetadata.Extends encodedValues.registry completion.result.context.registry)

local notation "functions" => CallableIndexedOwnedPreparedPhysicalProgramSupport.functions support
local notation "callStages" => CallableIndexedOwnedPreparedPhysicalProgramSupport.stages recipe.compiled
local notation "callFaults" => CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics

include history member entryType input started parameterView metadata in
private theorem current_inputs :
    ValueRep recipe.compiled.compatible.checked completion.result.context.registry functions mapping world
      (.function parameter result) entry.source callable
      (CallableContract.functionType nativeParameter nativeResult) ∧
    Dynamic.ValueHasType anchor.function.context before entry.source (.function parameter result) ∧
    ValueRep recipe.compiled.compatible.checked completion.result.context.registry functions mapping world
      parameter packedSource packed nativeParameter ∧
    Dynamic.ValueHasType anchor.function.context before packedSource parameter := by
  obtain ⟨imported, represented, typed⟩ := history.current.2.2.2.2 entry member
  have callableEq := started.callable_eq imported
  rw [entryType] at represented typed
  rw [← callableEq] at represented
  have nativeTypeEq : entry.nativeType = CallableContract.functionType nativeParameter nativeResult :=
    represented.runtime_hasType.type_eq.symm.trans started.callableTyped.type_eq
  rw [nativeTypeEq] at represented
  obtain ⟨packedRelated, packedTyped⟩ := started.history_input_compatible history input parameterView.symm metadata
  exact ⟨represented, typed, packedRelated, packedTyped⟩

include support in
private theorem anchor_runtime : Dynamic.SourceRuntimeValid (Program.ofChecked recipe.compiled.sourceProgram)
    anchor.function.context anchor.function.source := by
  obtain ⟨_facts, certificate⟩ := RecursiveNamedHeaderSourceTyping.certificate anchor support.wellFormed
  rw [anchor.frame.context, anchor.frame.source]
  exact certificate.toBodyInstanceTypingCertificate.sourceRuntimeValid

include support receiver extension physical
  history entry member entryType input started parameterView metadata in
/-- Actual current history and packed encoding close the direct native result
against independent Source execution, including the ordered Source arguments. -/
theorem completed_reflects_at_arity
    {executionFuel : Nat} {value : Core.Value} {finalStore : Store}
    (completed : checkpoint.NativeDone executionFuel value finalStore)
    (invocation : Staging.Recursive.Scope) :
    ∃ sources,
      Dynamic.ValuesPack sources packedSource ∧
      RecursivePublicCallableArity.Arity (Program.ofChecked recipe.compiled.sourceProgram) entry.source sources.length ∧
      ∃ sourceSize outcome after finalMap finalWorld,
        Staging.Recursive.Size.Applies (Program.ofChecked recipe.compiled.sourceProgram) callStages sourceSize
          invocation anchor.function.context before entry.source sources outcome after ∧
        ResultAt (registry := completion.result.context.registry) functions caller anchor.function.context result nativeResult
          outcome after value finalStore finalMap finalWorld callFaults := by
  obtain ⟨calleeRelated, calleeTyped, packedRelated, packedTyped⟩ :=
    current_inputs support history entry member entryType input started parameterView metadata
  obtain ⟨_native, heaps, stable, heapTyped, _entries⟩ := history.current
  obtain ⟨size, measured⟩ := evaluation_has_size
    (runStateful_evaluation_sound (started.initial.native_done_iff.mp completed))
  exact RecursiveNamedPublicPhysicalDirectCallableApplicationBounds.reflects_packed_at_arity support receiver extension caller physical stable
    (anchor_runtime support) heapTyped calleeTyped calleeRelated heaps packedTyped packedRelated
    (invocation := invocation) measured

include support receiver extension physical
  history entry member entryType input started parameterView metadata in
theorem completed_reflects
    {executionFuel : Nat} {value : Core.Value} {finalStore : Store}
    (completed : checkpoint.NativeDone executionFuel value finalStore)
    (invocation : Staging.Recursive.Scope) :
    ∃ sources,
      Dynamic.ValuesPack sources packedSource ∧
      ∃ sourceSize outcome after finalMap finalWorld,
        Staging.Recursive.Size.Applies (Program.ofChecked recipe.compiled.sourceProgram) callStages sourceSize
          invocation anchor.function.context before entry.source sources outcome after ∧
        ResultAt (registry := completion.result.context.registry) functions caller anchor.function.context result nativeResult
          outcome after value finalStore finalMap finalWorld callFaults := by
  obtain ⟨sources, packing, _arity, meaning⟩ := completed_reflects_at_arity support receiver extension history physical entry member entryType input
    started parameterView metadata completed invocation
  exact ⟨sources, packing, meaning⟩

include support receiver extension physical
  history entry member entryType input started parameterView metadata in
/-- The actual callable, encoded input and genuine Source arity derive native
completion for every sufficient fuel, including effects before a Source fault. -/
theorem has_sufficient_fuel_at_arity {invocation : Staging.Recursive.Scope} {sources : List Dynamic.Value}
    (packing : Dynamic.ValuesPack sources packedSource)
    (arity : RecursivePublicCallableArity.Arity (Program.ofChecked recipe.compiled.sourceProgram) entry.source sources.length)
    {sourceSize : Nat} {outcome : Staging.Recursive.Outcome} {after : Dynamic.Heap}
    (trace : Staging.Recursive.Size.Applies (Program.ofChecked recipe.compiled.sourceProgram) callStages sourceSize
      invocation anchor.function.context before entry.source sources outcome after) :
    ∃ value finalStore finalMap finalWorld required,
      (∀ executionFuel, required ≤ executionFuel → checkpoint.NativeDone executionFuel value finalStore) ∧
      ResultAt (registry := completion.result.context.registry) functions caller anchor.function.context result nativeResult
        outcome after value finalStore finalMap finalWorld callFaults := by
  obtain ⟨calleeRelated, calleeTyped, packedRelated, packedTyped⟩ :=
    current_inputs support history entry member entryType input started parameterView metadata
  obtain ⟨_native, heaps, stable, heapTyped, _entries⟩ := history.current
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, resultAt⟩ :=
    RecursiveNamedPublicPhysicalDirectCallableApplicationBounds.preserves_packed support receiver extension caller physical stable
      (anchor_runtime support) heapTyped calleeTyped calleeRelated heaps packedTyped packedRelated
      (tail := SourceCoreCallableIndexedTemplates.globalEnvironment recipe.compiled.indexed) packing arity trace
  obtain ⟨required, enough⟩ := evaluation_runStateful_complete_with_sufficient_fuel evaluated
  exact ⟨value, finalStore, finalMap, finalWorld, required,
    fun fuel bound => started.initial.native_done_iff.mpr (enough fuel bound), resultAt⟩

include support receiver extension physical
  history entry member entryType input started parameterView metadata in
/-- Source success supplies the arity without an additional boundary receipt. -/
theorem has_sufficient_fuel {invocation : Staging.Recursive.Scope} {sources : List Dynamic.Value}
    (packing : Dynamic.ValuesPack sources packedSource)
    {sourceSize : Nat} {sourceResult : Dynamic.Value} {after : Dynamic.Heap}
    (trace : Staging.Recursive.Size.Applies (Program.ofChecked recipe.compiled.sourceProgram) callStages sourceSize
      invocation anchor.function.context before entry.source sources (.value sourceResult) after) :
    ∃ value finalStore finalMap finalWorld required,
      (∀ executionFuel, required ≤ executionFuel → checkpoint.NativeDone executionFuel value finalStore) ∧
      ResultAt (registry := completion.result.context.registry) functions caller anchor.function.context result nativeResult
        (.value sourceResult) after value finalStore finalMap finalWorld callFaults := by
  exact has_sufficient_fuel_at_arity support receiver extension history physical entry member entryType input started parameterView metadata
    packing (.of_value trace) trace

end Meaning
end Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicPhysicalDirectCallableHistory
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicActualRegistryExportErrors
/-! An actual export error follows successful native and Source execution.
The returned public session retains all earlier handles at that exact after-heap. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicActualRegistryExportErrors
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open SourceCoreIndexedSession RecursiveNamedPublicStartMeaning
open RecursiveNamedPublicFunctionHistory (History Entry Caller)
open RecursiveNamedPublicDirectPackedInputMeaning (StartAt)
open RecursivePublicApplicationResult (ResultAt)
open CallableIndexedOwnedFunctionState
open CallableIndexedOwnedContextualTypedClosureReceipts (Association)

variable {recipe : Recipe}
variable
  {headers : List (CallableIndexedOwnedFunctionValues.Header recipe.compiled (Program.ofChecked recipe.compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key recipe.compiled (Program.ofChecked recipe.compiled.sourceProgram))}

section Meaning
variable {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver recipe.compiled.indexed}
  {bodyRegistry : SourceCoreRawMetadata.Registry} {semanticFaults : FunctionCalls.FaultRep}
  (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt recipe.compiled.indexed completion.entry
    completion.result.context.registry completion.result.extension completion.result.diagnostics)
  (stagePrepared : RecursiveNamedPreparedStageContracts.Prepared recipe.compiled
    recipe.compiled.indexed.ancestry.graph.inputs.callable)
  (profile : recipe.compiled.compatible.checked.catalog.callableContracts = true)
  {identities : Dynamic.Value → Word → Prop}
  (observations : CompatibleEquality.FunctionObservations recipe.compiled.compatible.checked.catalog
    (CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry semanticFaults profile) identities)
  (semantic : ∀ reason token, semanticFaults reason token →
    CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics (.semantic reason) token)
  (family : ∀ {mapping world function native bindings parameterCore resultCore}
    (association : Association headers keys bodyRegistry semanticFaults mapping world function native
      bindings parameterCore resultCore),
    CallableIndexedOwnedPreparedStagedOrdinarySequenceCallerBounds.OrdinarySequenceFor stagePrepared association)
  (namedTerminals : ∀ header, header ∈ headers →
    CallableIndexedOwnedPreparedStagedNamedBodies.Body header)
  (namedSupport : ∀ header (member : header ∈ headers),
    CallableIndexedOwnedPreparedStagedNamedBodiesSupport.Support headers keys bodyRegistry header
      (RecursiveNamedPreparedStageScopes.registry stagePrepared) (namedTerminals header member) semanticFaults)
  (wellFormed : ProgramWellFormed (Program.ofChecked recipe.compiled.sourceProgram))
  {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store : Store}
  {anchor : CallableIndexedOwnedFunctionValues.Header recipe.compiled (Program.ofChecked recipe.compiled.sourceProgram)}
  {caller : Caller headers keys mapping world before store}
  {artifact : Artifact} {session : Session artifact} {entries : List Entry}
  (history : History headers keys
    (CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry semanticFaults profile)
    completion.result.context.registry anchor session mapping world before store caller entries)
  (entry : Entry) (member : entry ∈ entries)
  {parameter result : TypeSystem.Ty}
  (entryType : entry.sourceType = .function parameter result)
  {argument : SourceCorePublicValues.Value} {packedSource : Dynamic.Value}
  (input : RecursiveNamedPublicFunctionHistoryInputs.Input entries anchor.function.context parameter argument packedSource)

  (atRecipe : ArtifactRecipe artifact recipe)

local notation "functions" => CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry semanticFaults profile
local notation "callStages" => RecursiveNamedPreparedStageScopes.registry stagePrepared

include receiver stagePrepared profile observations semantic family namedTerminals namedSupport wellFormed
  history entry member entryType input in
/-- Native success is reflected from the real export-error receipt. The
Source result and all effects remain available through the returned session. -/
theorem public_resume_export_error
    (atRegistry : session.RegistryAt completion.result.context.registry)
    (exportsReady : session.ExportsReady)
    {inputFuel : Nat} {checkpoint : Checkpoint artifact}
    {actualParameter actualResult : TypeSystem.Ty} {nativeParameter nativeResult : Core.Ty}
    {callable packed : Core.Value} {encodedValues : SourceCoreCompatibleValues.Context}
    (started : StartAt session entry.handle argument inputFuel checkpoint recipe world store
      actualParameter actualResult nativeParameter nativeResult callable packed encodedValues)
    {publicArtifact : SourceCoreExecution.Artifact}
    {publicCheckpoint : SourceCoreExecution.Checkpoint publicArtifact}
    {publicSession : SourceCoreExecution.Session publicArtifact}
    {executionFuel outputFuel : Nat} {error : SourceCoreIndexedSession.Error}
    (atCheckpoint : publicCheckpoint.IndexedAt checkpoint)
    (resumed : publicCheckpoint.ResumeAt executionFuel outputFuel (.exportError error publicSession))
    (invocation : Staging.Recursive.Scope) :
    ∃ receiving : CallableIndexedOwnedPublicFaultReceivers.Receiver recipe.compiled.indexed,
      receiving.result.context = encodedValues ∧
      CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt recipe.compiled.indexed receiving.entry
        receiving.result.context.registry receiving.result.extension receiving.result.diagnostics ∧
      SourceCoreRawMetadata.Extends completion.result.context.registry receiving.result.context.registry ∧
      (∀ token, checkpoint.diagnostic token = .ok (receiving.result.diagnostics.diagnostic? token)) ∧
    ∃ (actual : Session artifact) (generation : SourceCorePublicValues.ExportGeneration) (value : Core.Value) (finalStore : Store)
      (sources : List Dynamic.Value) (sourceSize : Nat) (source : Dynamic.Value)
      (after : Dynamic.Heap) (finalMap : LocationMap) (finalWorld : StoreTyping)
      (reached : Caller headers keys finalMap finalWorld after finalStore),
      checkpoint.ExportErrorResultAt executionFuel outputFuel generation value finalStore error actual ∧
      publicSession.IndexedAt actual ∧
      Dynamic.ValuesPack sources packedSource ∧
      Staging.Recursive.Size.Applies (Program.ofChecked recipe.compiled.sourceProgram) callStages sourceSize
        invocation anchor.function.context before entry.source sources (.value source) after ∧
      ResultAt (registry := receiving.result.context.registry) functions caller anchor.function.context result nativeResult
        (.value source) after value finalStore finalMap finalWorld
        (CallableIndexedOwnedPublicDecodedStagedCallFaults.faults receiving.result.diagnostics) ∧
      Relates caller reached ∧
      History headers keys functions receiving.result.context.registry anchor actual
        finalMap finalWorld after finalStore reached entries ∧
      actual.RegistryAt encodedValues.registry ∧ actual.ExportsReady := by
  obtain ⟨receiving, _indexed, contextAt, issued, extended, retained, _represented, _typed, diagnostics⟩ :=
    RecursiveNamedPublicActualRegistryStart.packed_input history atRegistry member entryType input started
  obtain ⟨program, present⟩ := RecursiveNamedPublicHistoryRegistryExtension.diagnostics_present history
  have semanticAt : ∀ reason token, semanticFaults reason token →
      CallableIndexedOwnedPublicDecodedStagedCallFaults.faults receiving.result.diagnostics (.semantic reason) token := by
    intro reason token related
    exact CompatibleRegistryDiagnosticExtension.staged_preserved recipe.compiled
      receiver issued present extended (semantic reason token related)
  have metadata : SourceCoreRawMetadata.Extends encodedValues.registry receiving.result.context.registry := by
    rw [contextAt]
    exact .refl _
  have imported := (history.current.2.2.2.2 entry member).1
  rw [entryType] at imported
  obtain ⟨parameterView, _resultView⟩ := TypeSystem.Ty.function.inj
    (started.selected.spec.2.1.symm.trans imported.function_type.symm)
  obtain ⟨actual, generation, value, finalStore, exported, sessionAt⟩ :=
    resumed.indexed_export_error atCheckpoint
  obtain ⟨sources, packing, sourceSize, outcome, after, finalMap, finalWorld, trace, resultAt⟩ :=
    RecursiveNamedPublicDirectCallableHistory.completed_reflects
      (completion := receiving) issued stagePrepared profile observations receiving.result.extension
      semanticAt family namedTerminals namedSupport wellFormed retained entry member entryType input
      started parameterView.symm metadata exported.1 invocation
  obtain ⟨payload, decoded⟩ := exported.succeeded
  obtain ⟨source, sourceValue, _represented, _heaps, _worldEq, _caller, _related, _stable, _typed, _sourceTyped⟩ :=
    RecursivePublicApplicationResult.returned_value resultAt decoded
  subst outcome
  obtain ⟨reached, related, continued⟩ := retained.after_packed_export_error started.original exported resultAt
  have returnedRegistry : actual.RegistryAt encodedValues.registry :=
    congrArg SourceCoreCompatibleValues.Context.registry (exported.values.trans started.values)
  have returnedReady := exported.exportsReady (started.original.initial_registry.exportsReady exportsReady)
  exact ⟨receiving, contextAt, issued, extended, diagnostics, actual, generation, value, finalStore,
    sources, sourceSize, source, after, finalMap, finalWorld, reached, exported, sessionAt, packing,
    trace, resultAt, related, continued, returnedRegistry, returnedReady⟩

include receiver stagePrepared profile observations semantic family namedTerminals namedSupport wellFormed
  history entry member entryType input atRecipe in
/-- An actual public invocation supplies its own startup and export error.
The earlier history continues at the exact successful Source after-heap. -/
theorem public_invoke_export_error
    (atRegistry : session.RegistryAt completion.result.context.registry)
    (exportsReady : session.ExportsReady)
    {publicArtifact : SourceCoreExecution.Artifact}
    {publicSession returned : SourceCoreExecution.Session publicArtifact}
    {options : SourceCoreExecution.RunOptions} {error : SourceCoreIndexedSession.Error}
    (atSession : publicSession.IndexedAt session)
    (invoked : publicSession.InvokeAt entry.handle argument options (.ok (.exportError error returned)))
    (invocation : Staging.Recursive.Scope) :
    ∃ (receiving : CallableIndexedOwnedPublicFaultReceivers.Receiver recipe.compiled.indexed)
      (checkpoint : Checkpoint artifact) (actual : Session artifact)
      (generation : SourceCorePublicValues.ExportGeneration) (value : Core.Value) (finalStore : Store)
      (actualParameter actualResult : TypeSystem.Ty) (nativeParameter nativeResult : Core.Ty)
      (callable packed : Core.Value) (encodedValues : SourceCoreCompatibleValues.Context)
      (sources : List Dynamic.Value) (sourceSize : Nat) (source : Dynamic.Value)
      (after : Dynamic.Heap) (finalMap : LocationMap) (finalWorld : StoreTyping)
      (reached : Caller headers keys finalMap finalWorld after finalStore),
      receiving.result.context = encodedValues ∧
      CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt recipe.compiled.indexed receiving.entry
        receiving.result.context.registry receiving.result.extension receiving.result.diagnostics ∧
      SourceCoreRawMetadata.Extends completion.result.context.registry receiving.result.context.registry ∧
      (∀ token, checkpoint.diagnostic token = .ok (receiving.result.diagnostics.diagnostic? token)) ∧
      StartAt session entry.handle argument options.inputValidationFuel checkpoint recipe world store
        actualParameter actualResult nativeParameter nativeResult callable packed encodedValues ∧
      SourceCoreRawMetadata.runtimeType actualParameter = SourceCoreRawMetadata.runtimeType parameter ∧
      SourceCoreRawMetadata.runtimeType actualResult = SourceCoreRawMetadata.runtimeType result ∧
      checkpoint.ExportErrorResultAt options.executionFuel options.outputValidationFuel generation value finalStore error actual ∧
      returned.IndexedAt actual ∧
      Dynamic.ValuesPack sources packedSource ∧
      Staging.Recursive.Size.Applies (Program.ofChecked recipe.compiled.sourceProgram) callStages sourceSize
        invocation anchor.function.context before entry.source sources (.value source) after ∧
      ResultAt (registry := receiving.result.context.registry) functions caller anchor.function.context result nativeResult
        (.value source) after value finalStore finalMap finalWorld
        (CallableIndexedOwnedPublicDecodedStagedCallFaults.faults receiving.result.diagnostics) ∧
      Relates caller reached ∧
      History headers keys functions receiving.result.context.registry anchor actual
        finalMap finalWorld after finalStore reached entries ∧
      actual.RegistryAt encodedValues.registry ∧ actual.ExportsReady := by
  obtain ⟨publicCheckpoint, accepted, resumed⟩ := invoked
  obtain ⟨checkpoint, atCheckpoint, original⟩ :=
    RecursiveNamedPublicDirectHandleMeaning.recover_handle_start atSession accepted
  have imported := (history.current.2.2.2.2 entry member).1
  rw [entryType] at imported
  obtain ⟨actualParameter, actualResult, nativeParameter, nativeResult, callable, packed, encodedValues,
    started, parameterView, resultView⟩ :=
    RecursiveNamedPublicDirectPackedInputMeaning.actual_start_compatible atRecipe history.current.1 imported original
  obtain ⟨receiving, contextAt, issued, extended, diagnostics, actual, generation, value, finalStore,
    sources, sourceSize, source, after, finalMap, finalWorld, reached, exported, sessionAt,
    packing, trace, resultAt, related, retained, registry, ready⟩ :=
    public_resume_export_error receiver stagePrepared profile observations semantic family namedTerminals
      namedSupport wellFormed history entry member entryType input atRegistry exportsReady started
      atCheckpoint resumed invocation
  exact ⟨receiving, checkpoint, actual, generation, value, finalStore, actualParameter, actualResult, nativeParameter,
    nativeResult, callable, packed, encodedValues, sources, sourceSize, source, after, finalMap,
    finalWorld, reached, contextAt, issued, extended, diagnostics, started, parameterView, resultView,
    exported, sessionAt, packing, trace, resultAt, related, retained, registry, ready⟩

end Meaning
end Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicActualRegistryExportErrors
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicActualRegistryFailurePreservation
/-! A Source fault determines the real public failure and reached history at
this call's actual metadata, including effects before the fault. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicActualRegistryFailurePreservation
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open SourceCoreIndexedSession RecursiveNamedPublicStartMeaning
open RecursiveNamedPublicFunctionHistory (History Entry Caller)
open RecursiveNamedPublicDirectPackedInputMeaning (StartAt)
open RecursivePublicApplicationResult (ResultAt)
open CallableIndexedOwnedFunctionState
open CallableIndexedOwnedContextualTypedClosureReceipts (Association)

variable {recipe : Recipe}
variable
  {headers : List (CallableIndexedOwnedFunctionValues.Header recipe.compiled (Program.ofChecked recipe.compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key recipe.compiled (Program.ofChecked recipe.compiled.sourceProgram))}

section Meaning
variable {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver recipe.compiled.indexed}
  {bodyRegistry : SourceCoreRawMetadata.Registry} {semanticFaults : FunctionCalls.FaultRep}
  (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt recipe.compiled.indexed completion.entry
    completion.result.context.registry completion.result.extension completion.result.diagnostics)
  (stagePrepared : RecursiveNamedPreparedStageContracts.Prepared recipe.compiled
    recipe.compiled.indexed.ancestry.graph.inputs.callable)
  (profile : recipe.compiled.compatible.checked.catalog.callableContracts = true)
  {identities : Dynamic.Value → Word → Prop}
  (observations : CompatibleEquality.FunctionObservations recipe.compiled.compatible.checked.catalog
    (CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry semanticFaults profile) identities)
  (semantic : ∀ reason token, semanticFaults reason token →
    CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics (.semantic reason) token)
  (family : ∀ {mapping world function native bindings parameterCore resultCore}
    (association : Association headers keys bodyRegistry semanticFaults mapping world function native
      bindings parameterCore resultCore),
    CallableIndexedOwnedPreparedStagedOrdinarySequenceCallerBounds.OrdinarySequenceFor stagePrepared association)
  (namedTerminals : ∀ header, header ∈ headers →
    CallableIndexedOwnedPreparedStagedNamedBodies.Body header)
  (namedSupport : ∀ header (member : header ∈ headers),
    CallableIndexedOwnedPreparedStagedNamedBodiesSupport.Support headers keys bodyRegistry header
      (RecursiveNamedPreparedStageScopes.registry stagePrepared) (namedTerminals header member) semanticFaults)
  (wellFormed : ProgramWellFormed (Program.ofChecked recipe.compiled.sourceProgram))
  {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store : Store}
  {anchor : CallableIndexedOwnedFunctionValues.Header recipe.compiled (Program.ofChecked recipe.compiled.sourceProgram)}
  {caller : Caller headers keys mapping world before store}
  {artifact : Artifact} {session : Session artifact} {entries : List Entry}
  (history : History headers keys
    (CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry semanticFaults profile)
    completion.result.context.registry anchor session mapping world before store caller entries)
  (entry : Entry) (member : entry ∈ entries)
  {parameter result : TypeSystem.Ty}
  (entryType : entry.sourceType = .function parameter result)
  {argument : SourceCorePublicValues.Value} {packedSource : Dynamic.Value}
  (input : RecursiveNamedPublicFunctionHistoryInputs.Input entries anchor.function.context parameter argument packedSource)

  (atRecipe : ArtifactRecipe artifact recipe)

local notation "functions" => CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry semanticFaults profile
local notation "callStages" => RecursiveNamedPreparedStageScopes.registry stagePrepared

include receiver stagePrepared profile observations semantic family namedTerminals namedSupport wellFormed
  history entry member entryType input in
/-- Every actual resume with enough execution fuel returns the represented
failure and preserves prior handles. Output validation fuel is unrestricted.
The Source argument count must match the callable: pack-equivalent argument
rows with a different count can produce Source-only arity faults. -/
theorem public_resume_has_sufficient_fuel
    (atRegistry : session.RegistryAt completion.result.context.registry)
    (exportsReady : session.ExportsReady)
    {inputFuel : Nat} {checkpoint : Checkpoint artifact}
    {actualParameter actualResult : TypeSystem.Ty} {nativeParameter nativeResult : Core.Ty}
    {callable packed : Core.Value} {encodedValues : SourceCoreCompatibleValues.Context}
    (started : StartAt session entry.handle argument inputFuel checkpoint recipe world store
      actualParameter actualResult nativeParameter nativeResult callable packed encodedValues)
    {invocation : Staging.Recursive.Scope} {sources : List Dynamic.Value}
    (packing : Dynamic.ValuesPack sources packedSource)
    (arity : RecursivePublicCallableArity.Arity (Program.ofChecked recipe.compiled.sourceProgram) entry.source sources.length)
    {sourceSize : Nat} {failure : Staging.Recursive.Failure} {after : Dynamic.Heap}
    (trace : Staging.Recursive.Size.Applies (Program.ofChecked recipe.compiled.sourceProgram) callStages sourceSize
      invocation anchor.function.context before entry.source sources (.fault failure) after)
    {publicArtifact : SourceCoreExecution.Artifact}
    {publicCheckpoint : SourceCoreExecution.Checkpoint publicArtifact}
    (atCheckpoint : publicCheckpoint.IndexedAt checkpoint) :
    ∃ receiving : CallableIndexedOwnedPublicFaultReceivers.Receiver recipe.compiled.indexed,
      receiving.result.context = encodedValues ∧
      CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt recipe.compiled.indexed receiving.entry
        receiving.result.context.registry receiving.result.extension receiving.result.diagnostics ∧
      SourceCoreRawMetadata.Extends completion.result.context.registry receiving.result.context.registry ∧
      (∀ token, checkpoint.diagnostic token = .ok (receiving.result.diagnostics.diagnostic? token)) ∧
    ∃ required token finalStore finalMap finalWorld,
      CallableIndexedOwnedPublicDecodedStagedCallFaults.faults receiving.result.diagnostics failure token ∧
      (∀ executionFuel, required ≤ executionFuel →
        checkpoint.NativeDone executionFuel (.inLeft nativeResult (.word token)) finalStore) ∧
      ResultAt (registry := receiving.result.context.registry) functions caller anchor.function.context
        result nativeResult (.fault failure) after (.inLeft nativeResult (.word token)) finalStore finalMap finalWorld
        (CallableIndexedOwnedPublicDecodedStagedCallFaults.faults receiving.result.diagnostics) ∧
      ∀ executionFuel outputFuel (outcome : SourceCoreExecution.Outcome publicArtifact),
        required ≤ executionFuel → publicCheckpoint.ResumeAt executionFuel outputFuel outcome →
        ∃ (returned : SourceCoreExecution.Session publicArtifact) (actual : Session artifact)
          (reached : Caller headers keys finalMap finalWorld after finalStore),
          outcome = .failed token returned ∧
          checkpoint.FailedResultAt executionFuel (.inLeft nativeResult (.word token)) finalStore token actual ∧
          returned.IndexedAt actual ∧ Relates caller reached ∧
          History headers keys functions receiving.result.context.registry anchor actual
            finalMap finalWorld after finalStore reached entries ∧
          actual.RegistryAt encodedValues.registry ∧ actual.ExportsReady := by
  obtain ⟨receiving, _indexed, contextAt, issued, extended, retained, _represented, inputTyped, diagnostics⟩ :=
    RecursiveNamedPublicActualRegistryStart.packed_input history atRegistry member entryType input started
  obtain ⟨program, present⟩ := RecursiveNamedPublicHistoryRegistryExtension.diagnostics_present history
  have semanticAt : ∀ reason token, semanticFaults reason token →
      CallableIndexedOwnedPublicDecodedStagedCallFaults.faults receiving.result.diagnostics (.semantic reason) token := by
    intro reason token related
    exact CompatibleRegistryDiagnosticExtension.staged_preserved recipe.compiled
      receiver issued present extended (semantic reason token related)
  have metadata : SourceCoreRawMetadata.Extends encodedValues.registry receiving.result.context.registry := by
    rw [contextAt]
    exact .refl _
  obtain ⟨imported, _calleeRep, calleeTyped⟩ := history.current.2.2.2.2 entry member
  rw [entryType] at imported calleeTyped
  obtain ⟨parameterView, _resultView⟩ := TypeSystem.Ty.function.inj
    (started.selected.spec.2.1.symm.trans imported.function_type.symm)
  obtain ⟨value, finalStore, finalMap, finalWorld, required, enough, resultAt⟩ :=
    RecursiveNamedPublicDirectCallableHistory.has_sufficient_fuel_at_arity
      (completion := receiving) issued stagePrepared profile observations receiving.result.extension
      semanticAt family namedTerminals namedSupport wellFormed retained entry member entryType input
      started parameterView.symm metadata packing arity trace
  obtain ⟨token, valueEq, faultRelated⟩ : ∃ token,
      value = .inLeft nativeResult (.word token) ∧
      CallableIndexedOwnedPublicDecodedStagedCallFaults.faults receiving.result.diagnostics failure token := by
    have represented := resultAt.1
    cases represented with
    | fault related => exact ⟨_, rfl, related⟩
  subst value
  have preserved := Staging.Recursive.FaultPreservation.applies wellFormed
    (RecursiveNamedPublicHistorySourceInputs.header_runtime wellFormed anchor)
    history.current.2.2.2.1 calleeTyped packing inputTyped trace
  have ready := started.original.initial_registry.exportsReady exportsReady
  refine ⟨receiving, contextAt, issued, extended, diagnostics, required, token,
    finalStore, finalMap, finalWorld, faultRelated, enough, resultAt, ?_⟩
  intro executionFuel outputFuel outcome bound resumed
  have completed := enough executionFuel bound
  obtain ⟨returned, outcomeEq⟩ := resumed.native_failed atCheckpoint completed rfl
  have failedResume : publicCheckpoint.ResumeAt executionFuel outputFuel (.failed token returned) := outcomeEq ▸ resumed
  obtain ⟨actual, _generation, actualValue, actualStore, actualCompleted, failed, returnedAt⟩ :=
    failedResume.indexed_failed atCheckpoint
  have same := completed.symm.trans actualCompleted
  cases same
  obtain ⟨reached, related, returnedHistory⟩ :=
    retained.after_packed_failure started.original failed resultAt preserved.1
  have registry : actual.RegistryAt encodedValues.registry :=
    congrArg SourceCoreCompatibleValues.Context.registry (failed.2.2.2.2.1.trans started.values)
  exact ⟨returned, actual, reached, outcomeEq, failed, returnedAt, related,
    returnedHistory, registry, failed.exportsReady ready⟩

end Meaning
end Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicActualRegistryFailurePreservation
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicActualRegistryNamedExportErrors
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicActualRegistryNamedExportErrors
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

open RecursiveNamedPublicHistoryFrontdoor

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
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
  (atRegistry : nativeSession.RegistryAt completion.result.context.registry)
  (atRecipe : ArtifactRecipe nativeArtifact recipe)
  {publicArtifact : SourceCoreExecution.Artifact}
  {publicSession : SourceCoreExecution.Session publicArtifact}
  {publicCheckpoint : SourceCoreExecution.Checkpoint publicArtifact}
  (atSession : publicSession.IndexedAt nativeSession)
  (exportsReady : publicSession.ExportsReady)
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
  (descriptors : ∀ request : Started (headers rows) prepared publicCheckpoint nativeSession key publicArguments
      options.inputValidationFuel world store,
    Nonempty (SourceCoreCallableContracts.Descriptor compiled.indexed.ancestry.graph.inputs.callable.table
      (.named request.header.named.signature.key)))

include receiver observations semantic family namedTerminals namedSupport wellFormed
  prepared complete history atRecipe atRegistry atSession exportsReady inputsFor descriptors in
/-- A following named call that completes but cannot export its value retains
all prior handles and the exact successful Source after-heap. -/
theorem public_run_export_error_retains
    {returned : SourceCoreExecution.Session publicArtifact} {error : SourceCoreIndexedSession.Error}
    (publicStart : publicSession.start key publicArguments options.inputValidationFuel = .ok publicCheckpoint)
    (publicRun : publicSession.RunAt key publicArguments options (.ok (.exportError error returned))) :
    ∃ (request : Started (headers rows) prepared publicCheckpoint nativeSession key publicArguments
      options.inputValidationFuel world store) (arguments : List Dynamic.Value),
      RecursiveNamedPublicFunctionHistoryInputs.Inputs entries request.header.function.context
        (request.header.bindings.map (fun binding => binding.1.scheme.body)) publicArguments arguments ∧
      ∃ receiving : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed,
        receiving.result.context = request.encodedValues ∧
        CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt compiled.indexed receiving.entry
          receiving.result.context.registry receiving.result.extension receiving.result.diagnostics ∧
        SourceCoreRawMetadata.Extends completion.result.context.registry receiving.result.context.registry ∧
        (∀ token, request.checkpoint.diagnostic token = .ok (receiving.result.diagnostics.diagnostic? token)) ∧
      ∃ (actual : SourceCoreIndexedSession.Session nativeArtifact)
        (generation : SourceCorePublicValues.ExportGeneration) (value : Core.Value) (finalStore : Store)
        (capture : CallableIndexedOwnedFunctionValues.NamedCapture rootHeaders (rootOwner).key request.header mapping world)
        (sourceSize : Nat) (source : Dynamic.Value) (after : Dynamic.Heap)
        (finalMap : LocationMap) (finalWorld : StoreTyping),
        request.checkpoint.ExportErrorResultAt options.executionFuel options.outputValidationFuel
          generation value finalStore error actual ∧
        returned.IndexedAt actual ∧
        Staging.Recursive.Size.Applies (Program.ofChecked compiled.sourceProgram)
          (RecursiveNamedPreparedStageScopes.registry stagePrepared) sourceSize invocation anchor.function.context before
          (.global request.function) arguments (.value source) after ∧
        ∃ _result : CallableIndexedOwnedPreparedStagedTerminalNamedInvocationBounds.ResultAt
          (registry := receiving.result.context.registry) (payloads := request.payloads)
          (scope := []) (canonical := SourceCoreCallableIndexedTemplates.globalEnvironment compiled.indexed)
          rootFunctions rootOwner caller request.header capture anchor.function.context
          (.value source) after value finalStore finalMap finalWorld
          (CallableIndexedOwnedPublicDecodedStagedCallFaults.faults receiving.result.diagnostics),
        ∃ reached : RecursiveNamedPublicFunctionHistory.Caller rootHeaders rootKeys finalMap finalWorld after finalStore,
          Relates caller reached ∧
          RecursiveNamedPublicFunctionHistory.History rootHeaders rootKeys rootFunctions
            receiving.result.context.registry anchor actual finalMap finalWorld after finalStore reached entries ∧
          actual.RegistryAt request.encodedValues.registry ∧ actual.ExportsReady := by
  have sameCompiled := Recipe.prepare_compiled prepared
  cases sameCompiled
  obtain ⟨request⟩ := recover_start prepared inputs rows complete atRecipe history.current.1 atSession publicStart
  obtain ⟨arguments, inputReceipts⟩ := inputsFor request
  obtain ⟨descriptor⟩ := descriptors request
  obtain ⟨receiving, _member, contextAt, issued, extended, retained, diagnostics⟩ :=
    RecursiveNamedPublicActualRegistryNamedStart.named_start history atRegistry request.started
  obtain ⟨program, present⟩ := RecursiveNamedPublicHistoryRegistryExtension.diagnostics_present history
  have semanticAt : ∀ reason token, semanticFaults reason token →
      CallableIndexedOwnedPublicDecodedStagedCallFaults.faults receiving.result.diagnostics (.semantic reason) token := by
    intro reason token related
    exact CompatibleRegistryDiagnosticExtension.staged_preserved recipe.compiled
      receiver issued present extended (semantic reason token related)
  have metadata : SourceCoreRawMetadata.Extends request.encodedValues.registry receiving.result.context.registry := by
    rw [contextAt]
    exact .refl _
  obtain ⟨stable, heaps, heapTyped, represented, argumentsTyped⟩ :=
    CallableIndexedOwnedPreparedStagedHistoryPublicBounds.current_arguments
      (completion := receiving) (inputs := inputs) (rows := rows) (profile := profile)
      (wellFormed := wellFormed) (prepared := prepared) (selected := request.selected)
      (history := retained) (started := request.started) (inputReceipts := inputReceipts) (metadata := metadata)
  have globalReference := CallableIndexedOwnedPreparedBootstrapGlobalReferences.global_reference
    rows request.header request.selected.member
  have supports := (RecursiveNamedPublicReturnedValues.header_context_supports request.header anchor wellFormed).2
  obtain ⟨resumedCheckpoint, accepted, resumed⟩ := publicRun
  have checkpointEq : resumedCheckpoint = publicCheckpoint := Except.ok.inj (accepted.symm.trans publicStart)
  subst resumedCheckpoint
  obtain ⟨actual, generation, value, finalStore, exported, sessionAt⟩ :=
    resumed.indexed_export_error request.atCheckpoint
  obtain ⟨capture, sourceSize, outcome, after, finalMap, finalWorld, trace, result⟩ :=
    CallableIndexedOwnedPreparedStagedOrdinarySequenceCallerBounds.reflects_root
      (stagePrepared := stagePrepared) (receiver := issued) (profile := profile)
      (observations := observations) (extension := receiving.result.extension) (semantic := semanticAt)
      (family := family) (namedTerminals := namedTerminals) (namedSupport := namedSupport)
      (acceptedPlan := SourceCoreUnifiedPreparationCertificates.compiled_planPrepared recipe.compiled)
      (wellFormed := wellFormed) (selected := request.selected) (owner := owner recipe.compiled)
      (caller := caller) (globalReference := globalReference) (stable := stable)
      (heapTyped := heapTyped) (argumentsTyped := argumentsTyped) (represented := represented)
      (heaps := heaps) (sourceAt := request.sourceAt) (supports := supports)
      descriptor (request.started.initial.native_done_iff.mp exported.1)
  obtain ⟨payload, decoded⟩ := exported.succeeded
  obtain ⟨source, sourceValue, _represented, _heaps, _worldEq, _caller, _related, _stable, _typed, _sourceTyped⟩ :=
    RecursiveNamedPublicReturnedValues.returned_value result decoded
  subst outcome
  obtain ⟨reached, related, continued⟩ := retained.after_export_error rfl request.started request.selected exported result
  have returnedRegistry : actual.RegistryAt request.encodedValues.registry :=
    congrArg SourceCoreCompatibleValues.Context.registry (exported.values.trans request.started.values)
  have nativeReady := atSession.exportsReady_iff.mp exportsReady
  have returnedReady := exported.exportsReady (request.started.original.initial_registry.exportsReady nativeReady)
  exact ⟨request, arguments, inputReceipts, receiving, contextAt, issued, extended, diagnostics,
    actual, generation, value, finalStore, capture, sourceSize, source, after, finalMap, finalWorld,
    exported, sessionAt, trace, result, reached, related, continued, returnedRegistry, returnedReady⟩

end Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicActualRegistryNamedExportErrors
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicActualRegistryNamedReflection
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicActualRegistryNamedReflection
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

open RecursiveNamedPublicHistoryFrontdoor

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
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
  (atRegistry : nativeSession.RegistryAt completion.result.context.registry)
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
  (descriptors : ∀ request : Started (headers rows) prepared publicCheckpoint nativeSession key publicArguments
      options.inputValidationFuel world store,
    Nonempty (SourceCoreCallableContracts.Descriptor compiled.indexed.ancestry.graph.inputs.callable.table
      (.named request.header.named.signature.key)))

include receiver observations semantic family namedTerminals namedSupport wellFormed
  prepared complete history atRecipe atRegistry atSession inputsFor descriptors in
/-- The actual named input encoder fixes the receiver, including metadata in
ordered arguments. Successful public execution returns the exact Source trace
and retained history without a caller-supplied receiving registry. -/
theorem public_run_succeeded_retains
    {publicCompletion : SourceCoreExecution.Completion publicArtifact}
    (publicStart : publicSession.start key publicArguments options.inputValidationFuel = .ok publicCheckpoint)
    (publicRun : publicSession.RunAt key publicArguments options (.ok (.succeeded publicCompletion))) :
    ∃ (request : Started (headers rows) prepared publicCheckpoint nativeSession key publicArguments
      options.inputValidationFuel world store) (arguments : List Dynamic.Value),
      RecursiveNamedPublicFunctionHistoryInputs.Inputs entries request.header.function.context
        (request.header.bindings.map (fun binding => binding.1.scheme.body)) publicArguments arguments ∧
      ∃ receiving : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed,
        receiving.result.context = request.encodedValues ∧
        CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt compiled.indexed receiving.entry
          receiving.result.context.registry receiving.result.extension receiving.result.diagnostics ∧
        SourceCoreRawMetadata.Extends completion.result.context.registry receiving.result.context.registry ∧
        (∀ token, request.checkpoint.diagnostic token = .ok (receiving.result.diagnostics.diagnostic? token)) ∧
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
          (registry := receiving.result.context.registry) (payloads := request.payloads)
          (scope := []) (canonical := SourceCoreCallableIndexedTemplates.globalEnvironment compiled.indexed)
          rootFunctions rootOwner caller request.header capture anchor.function.context
          outcome after value finalStore finalMap finalWorld (CallableIndexedOwnedPublicDecodedStagedCallFaults.faults receiving.result.diagnostics),
        ∃ reached : RecursiveNamedPublicFunctionHistory.Caller rootHeaders rootKeys finalMap finalWorld after finalStore,
          Relates caller reached ∧
          RecursiveNamedPublicFunctionHistory.History rootHeaders rootKeys rootFunctions
            receiving.result.context.registry anchor actual.session finalMap finalWorld after finalStore reached entries ∧
          actual.session.RegistryAt request.encodedValues.registry := by
  have sameCompiled := Recipe.prepare_compiled prepared
  cases sameCompiled
  obtain ⟨request⟩ := recover_start prepared inputs rows complete atRecipe history.current.1 atSession publicStart
  obtain ⟨arguments, inputReceipts⟩ := inputsFor request
  obtain ⟨descriptor⟩ := descriptors request
  obtain ⟨receiving, _member, contextAt, issued, extended, retained, diagnostics⟩ :=
    RecursiveNamedPublicActualRegistryNamedStart.named_start history atRegistry request.started
  obtain ⟨program, present⟩ := RecursiveNamedPublicHistoryRegistryExtension.diagnostics_present history
  have semanticAt : ∀ reason token, semanticFaults reason token →
      CallableIndexedOwnedPublicDecodedStagedCallFaults.faults receiving.result.diagnostics (.semantic reason) token := by
    intro reason token related
    exact CompatibleRegistryDiagnosticExtension.staged_preserved recipe.compiled
      receiver issued present extended (semantic reason token related)
  have metadata : SourceCoreRawMetadata.Extends request.encodedValues.registry receiving.result.context.registry := by
    rw [contextAt]
    exact .refl _
  obtain ⟨actual, generation, value, finalStore, capture, sourceSize, outcome, after, finalMap, finalWorld,
      succeeded, valueEq, typeEq, budgetEq, sessionAt, trace, result, reached, related, continued⟩ :=
    CallableIndexedOwnedPreparedStagedHistoryPublicContinuations.public_run_succeeded_retains
      (inputs := inputs) (rows := rows) (stagePrepared := stagePrepared) (receiver := issued) (profile := profile)
      (observations := observations) (extension := receiving.result.extension) (semantic := semanticAt)
      (family := family) (namedTerminals := namedTerminals) (namedSupport := namedSupport)
      (wellFormed := wellFormed) (prepared := prepared) (selected := request.selected)
      (caller := caller) (history := retained) (atCheckpoint := request.atCheckpoint) (started := request.started)
      (inputReceipts := inputReceipts) (metadata := metadata) (sourceAt := request.sourceAt)
      publicStart publicRun descriptor
  exact ⟨request, arguments, inputReceipts, receiving, contextAt, issued, extended, diagnostics,
    actual, generation, value, finalStore, capture, sourceSize,
    outcome, after, finalMap, finalWorld, succeeded, ⟨valueEq, typeEq, budgetEq, sessionAt⟩,
    trace, result, reached, related, continued, request.started.returned_registry succeeded⟩

include receiver observations semantic family namedTerminals namedSupport wellFormed
  prepared complete history atRecipe atRegistry atSession inputsFor descriptors in
/-- A failed following named call retains all earlier handles at the actual
Source after-heap and the same context used by the real input encoder. -/
theorem public_run_failed_retains
    {returned : SourceCoreExecution.Session publicArtifact} {reason : Word}
    (publicStart : publicSession.start key publicArguments options.inputValidationFuel = .ok publicCheckpoint)
    (publicRun : publicSession.RunAt key publicArguments options (.ok (.failed reason returned))) :
    ∃ (request : Started (headers rows) prepared publicCheckpoint nativeSession key publicArguments
      options.inputValidationFuel world store) (arguments : List Dynamic.Value),
      RecursiveNamedPublicFunctionHistoryInputs.Inputs entries request.header.function.context
        (request.header.bindings.map (fun binding => binding.1.scheme.body)) publicArguments arguments ∧
      ∃ receiving : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed,
        receiving.result.context = request.encodedValues ∧
        CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt compiled.indexed receiving.entry
          receiving.result.context.registry receiving.result.extension receiving.result.diagnostics ∧
        SourceCoreRawMetadata.Extends completion.result.context.registry receiving.result.context.registry ∧
        (∀ token, request.checkpoint.diagnostic token = .ok (receiving.result.diagnostics.diagnostic? token)) ∧
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
          (registry := receiving.result.context.registry) (payloads := request.payloads)
          (scope := []) (canonical := SourceCoreCallableIndexedTemplates.globalEnvironment compiled.indexed)
          rootFunctions rootOwner caller request.header capture anchor.function.context
          outcome after value finalStore finalMap finalWorld (CallableIndexedOwnedPublicDecodedStagedCallFaults.faults receiving.result.diagnostics),
        ∃ reached : RecursiveNamedPublicFunctionHistory.Caller rootHeaders rootKeys finalMap finalWorld after finalStore,
          Relates caller reached ∧
          RecursiveNamedPublicFunctionHistory.History rootHeaders rootKeys rootFunctions
            receiving.result.context.registry anchor actual finalMap finalWorld after finalStore reached entries ∧
          actual.RegistryAt request.encodedValues.registry := by
  have sameCompiled := Recipe.prepare_compiled prepared
  cases sameCompiled
  obtain ⟨request⟩ := recover_start prepared inputs rows complete atRecipe history.current.1 atSession publicStart
  obtain ⟨arguments, inputReceipts⟩ := inputsFor request
  obtain ⟨descriptor⟩ := descriptors request
  obtain ⟨receiving, _member, contextAt, issued, extended, retained, diagnostics⟩ :=
    RecursiveNamedPublicActualRegistryNamedStart.named_start history atRegistry request.started
  obtain ⟨program, present⟩ := RecursiveNamedPublicHistoryRegistryExtension.diagnostics_present history
  have semanticAt : ∀ reason token, semanticFaults reason token →
      CallableIndexedOwnedPublicDecodedStagedCallFaults.faults receiving.result.diagnostics (.semantic reason) token := by
    intro reason token related
    exact CompatibleRegistryDiagnosticExtension.staged_preserved recipe.compiled
      receiver issued present extended (semantic reason token related)
  have metadata : SourceCoreRawMetadata.Extends request.encodedValues.registry receiving.result.context.registry := by
    rw [contextAt]
    exact .refl _
  obtain ⟨actual, value, finalStore, capture, sourceSize, outcome, after, finalMap, finalWorld,
      failed, sessionAt, trace, result, reached, related, continued⟩ :=
    CallableIndexedOwnedPreparedStagedHistoryPublicFailures.public_run_failed_retains
      (inputs := inputs) (rows := rows) (stagePrepared := stagePrepared) (receiver := issued) (profile := profile)
      (observations := observations) (extension := receiving.result.extension) (semantic := semanticAt)
      (family := family) (namedTerminals := namedTerminals) (namedSupport := namedSupport)
      (wellFormed := wellFormed) (prepared := prepared) (selected := request.selected)
      (caller := caller) (history := retained) (atCheckpoint := request.atCheckpoint) (started := request.started)
      (inputReceipts := inputReceipts) (metadata := metadata) (sourceAt := request.sourceAt)
      publicStart publicRun descriptor
  have registryAt : actual.RegistryAt request.encodedValues.registry := by
    have returnedValues := failed.2.2.2.2.1
    have values := request.started.values
    rcases request with ⟨checkpoint, root, header, payloads, encodedValues, rawD, function,
      atCheckpoint, started, selected, sourceAt⟩
    cases checkpoint
    exact congrArg SourceCoreCompatibleValues.Context.registry (returnedValues.trans values)
  exact ⟨request, arguments, inputReceipts, receiving, contextAt, issued, extended, diagnostics,
    actual, value, finalStore, capture, sourceSize,
    outcome, after, finalMap, finalWorld, failed, sessionAt, trace, result, reached, related, continued, registryAt⟩

end Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicActualRegistryNamedReflection
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicActualRegistryOutputCollection
/-! Selected functions in returned constructor payloads and ordered mapping
rows join the actual session history. Both input and output use their original
codecs; Source meaning comes from the independent completed execution. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicActualRegistryOutputCollection
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open SourceCoreIndexedSession RecursiveNamedPublicStartMeaning
open RecursiveNamedPublicFunctionHistory (History Entry Caller)
open RecursiveNamedPublicDirectPackedInputMeaning (StartAt)
open RecursivePublicApplicationResult (ResultAt)
open CallableIndexedOwnedFunctionState
open CallableIndexedOwnedContextualTypedClosureReceipts (Association)

variable {recipe : Recipe}
variable
  {headers : List (CallableIndexedOwnedFunctionValues.Header recipe.compiled (Program.ofChecked recipe.compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key recipe.compiled (Program.ofChecked recipe.compiled.sourceProgram))}

section Meaning
variable {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver recipe.compiled.indexed}
  {bodyRegistry : SourceCoreRawMetadata.Registry} {semanticFaults : FunctionCalls.FaultRep}
  (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt recipe.compiled.indexed completion.entry
    completion.result.context.registry completion.result.extension completion.result.diagnostics)
  (stagePrepared : RecursiveNamedPreparedStageContracts.Prepared recipe.compiled
    recipe.compiled.indexed.ancestry.graph.inputs.callable)
  (profile : recipe.compiled.compatible.checked.catalog.callableContracts = true)
  {identities : Dynamic.Value → Word → Prop}
  (observations : CompatibleEquality.FunctionObservations recipe.compiled.compatible.checked.catalog
    (CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry semanticFaults profile) identities)
  (semantic : ∀ reason token, semanticFaults reason token →
    CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics (.semantic reason) token)
  (family : ∀ {mapping world function native bindings parameterCore resultCore}
    (association : Association headers keys bodyRegistry semanticFaults mapping world function native
      bindings parameterCore resultCore),
    CallableIndexedOwnedPreparedStagedOrdinarySequenceCallerBounds.OrdinarySequenceFor stagePrepared association)
  (namedTerminals : ∀ header, header ∈ headers →
    CallableIndexedOwnedPreparedStagedNamedBodies.Body header)
  (namedSupport : ∀ header (member : header ∈ headers),
    CallableIndexedOwnedPreparedStagedNamedBodiesSupport.Support headers keys bodyRegistry header
      (RecursiveNamedPreparedStageScopes.registry stagePrepared) (namedTerminals header member) semanticFaults)
  (wellFormed : ProgramWellFormed (Program.ofChecked recipe.compiled.sourceProgram))
  {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store : Store}
  {anchor : CallableIndexedOwnedFunctionValues.Header recipe.compiled (Program.ofChecked recipe.compiled.sourceProgram)}
  {caller : Caller headers keys mapping world before store}
  {artifact : Artifact} {session : Session artifact} {entries : List Entry}
  (history : History headers keys
    (CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry semanticFaults profile)
    completion.result.context.registry anchor session mapping world before store caller entries)
  (entry : Entry) (member : entry ∈ entries)
  {parameter result : TypeSystem.Ty}
  (entryType : entry.sourceType = .function parameter result)
  {argument : SourceCorePublicValues.Value} {packedSource : Dynamic.Value}
  (input : RecursiveNamedPublicFunctionHistoryInputs.Input entries anchor.function.context parameter argument packedSource)

  (atRecipe : ArtifactRecipe artifact recipe)

local notation "functions" => CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry semanticFaults profile
local notation "callStages" => RecursiveNamedPreparedStageScopes.registry stagePrepared

private theorem selected_of_cast {checked : SourceCoreCompatibleCatalog.Checked}
    {artifact : Artifact} {session : Session artifact} {sourceType : TypeSystem.Ty}
    {first second : SourceCorePublicValues.Value} (same : first = second)
    {selection : RecursiveNamedPublicNestedOutputSelections.Selection sourceType first}
    {source : Dynamic.Value} {native : Core.Value} {type : Core.Ty} {fuel : Nat} {entries : List Entry}
    (selected : RecursiveNamedPublicNestedOutputSelections.Selected checked session
      (same ▸ selection : RecursiveNamedPublicNestedOutputSelections.Selection sourceType second)
      source native type fuel entries) :
    RecursiveNamedPublicNestedOutputSelections.Selected checked session selection source native type fuel entries := by
  cases same
  exact selected

include receiver stagePrepared profile observations semantic family namedTerminals namedSupport wellFormed
  history entry member entryType input atRecipe in
/-- The real public invocation appends every selected output function in
payload/row order, including repeated keys and repeated handles. The returned
history uses the same current heap and actual metadata receiver. -/
theorem public_invoke_succeeded_collects
    (atRegistry : session.RegistryAt completion.result.context.registry)
    {publicArtifact : SourceCoreExecution.Artifact}
    {publicSession : SourceCoreExecution.Session publicArtifact}
    {publicCompletion : SourceCoreExecution.Completion publicArtifact}
    {options : SourceCoreExecution.RunOptions}
    (atSession : publicSession.IndexedAt session)
    (invoked : publicSession.InvokeAt entry.handle argument options (.ok (.succeeded publicCompletion)))
    (selection : RecursiveNamedPublicNestedOutputSelections.Selection result publicCompletion.value)
    (invocation : Staging.Recursive.Scope) :
    ∃ (receiving : CallableIndexedOwnedPublicFaultReceivers.Receiver recipe.compiled.indexed)
      (checkpoint : Checkpoint artifact) (actual : Completion artifact)
      (generation : SourceCorePublicValues.ExportGeneration) (value : Core.Value) (finalStore : Store)
      (actualParameter actualResult : TypeSystem.Ty) (nativeParameter nativeResult : Core.Ty)
      (callable packed : Core.Value) (encodedValues : SourceCoreCompatibleValues.Context)
      (sources : List Dynamic.Value) (sourceSize : Nat) (source : Dynamic.Value) (payload : Core.Value)
      (after : Dynamic.Heap) (finalMap : LocationMap) (finalWorld : StoreTyping)
      (reached : Caller headers keys finalMap finalWorld after finalStore) (added : List Entry),
      receiving.result.context = encodedValues ∧
      CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt recipe.compiled.indexed receiving.entry
        receiving.result.context.registry receiving.result.extension receiving.result.diagnostics ∧
      SourceCoreRawMetadata.Extends completion.result.context.registry receiving.result.context.registry ∧
      (∀ token, checkpoint.diagnostic token = .ok (receiving.result.diagnostics.diagnostic? token)) ∧
      StartAt session entry.handle argument options.inputValidationFuel checkpoint recipe world store
        actualParameter actualResult nativeParameter nativeResult callable packed encodedValues ∧
      SourceCoreRawMetadata.runtimeType actualParameter = SourceCoreRawMetadata.runtimeType parameter ∧
      SourceCoreRawMetadata.runtimeType actualResult = SourceCoreRawMetadata.runtimeType result ∧
      checkpoint.SucceededResultAt options.executionFuel options.outputValidationFuel generation value finalStore actual ∧
      publicCompletion.IndexedAt actual ∧
      Dynamic.ValuesPack sources packedSource ∧
      Staging.Recursive.Size.Applies (Program.ofChecked recipe.compiled.sourceProgram) callStages sourceSize
        invocation anchor.function.context before entry.source sources (.value source) after ∧
      ResultAt (registry := receiving.result.context.registry) functions caller anchor.function.context result nativeResult
        (.value source) after value finalStore finalMap finalWorld
        (CallableIndexedOwnedPublicDecodedStagedCallFaults.faults receiving.result.diagnostics) ∧
      value = .inRight .word payload ∧
      RecursiveNamedPublicNestedOutputSelections.Selected recipe.compiled.compatible.checked actual.session
        selection source payload nativeResult options.outputValidationFuel added ∧
      added.map Entry.handle = selection.handles ∧ Relates caller reached ∧
      History headers keys functions receiving.result.context.registry anchor actual.session
        finalMap finalWorld after finalStore reached (entries ++ added) ∧
      actual.session.RegistryAt encodedValues.registry := by
  obtain ⟨receiving, checkpoint, actual, generation, value, finalStore, actualParameter, actualResult,
    nativeParameter, nativeResult, callable, packed, encodedValues, sources, sourceSize, outcome, after,
    finalMap, finalWorld, _priorReached, contextAt, issued, extended, diagnostics, started, parameterView, resultView,
    succeeded, actualAt, packing, trace, resultAt, _priorRelated, _priorHistory, returnedRegistry⟩ :=
    RecursiveNamedPublicActualRegistryReflection.public_invoke_succeeded
      receiver stagePrepared profile observations semantic family namedTerminals namedSupport wellFormed
      history entry member entryType input atRecipe atRegistry atSession invoked invocation
  have current := RecursiveNamedPublicHistoryRegistryExtension.extend_history history extended
  have metadata : SourceCoreRawMetadata.Extends receiving.result.context.registry encodedValues.registry := by
    rw [contextAt]
    exact .refl _
  obtain ⟨reached, source, payload, added, sourceValue, nativeValue, selected, handles, related, retained⟩ :=
    current.collect_packed_nested_success rfl atRecipe started.original started.requested resultView.symm
      succeeded resultAt returnedRegistry metadata (actualAt.1 ▸ selection)
  have originalSelection := selected_of_cast actualAt.1 selected
  have originalHandles := handles.trans
    (RecursiveNamedPublicNestedOutputSelections.Selection.handles_cast actualAt.1 selection)
  rw [sourceValue] at trace resultAt
  exact ⟨receiving, checkpoint, actual, generation, value, finalStore, actualParameter, actualResult,
    nativeParameter, nativeResult, callable, packed, encodedValues, sources, sourceSize, source, payload, after,
    finalMap, finalWorld, reached, added, contextAt, issued, extended, diagnostics, started, parameterView, resultView,
    succeeded, actualAt, packing, trace, resultAt, nativeValue, originalSelection, originalHandles,
    related, retained, returnedRegistry⟩

end Meaning
end Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicActualRegistryOutputCollection
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicActualRegistryOutputPreservation
/-! Independent Source success determines native execution and general public
output export at the registry produced by this call's real input encoder. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicActualRegistryOutputPreservation
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open SourceCoreIndexedSession RecursiveNamedPublicStartMeaning
open RecursiveNamedPublicFunctionHistory (History Entry Caller)
open RecursiveNamedPublicDirectPackedInputMeaning (StartAt)
open RecursivePublicApplicationResult (ResultAt)
open CallableIndexedOwnedFunctionState
open CallableIndexedOwnedContextualTypedClosureReceipts (Association)

variable {recipe : Recipe}
variable
  {headers : List (CallableIndexedOwnedFunctionValues.Header recipe.compiled (Program.ofChecked recipe.compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key recipe.compiled (Program.ofChecked recipe.compiled.sourceProgram))}

section Meaning
variable {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver recipe.compiled.indexed}
  {bodyRegistry : SourceCoreRawMetadata.Registry} {semanticFaults : FunctionCalls.FaultRep}
  (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt recipe.compiled.indexed completion.entry
    completion.result.context.registry completion.result.extension completion.result.diagnostics)
  (stagePrepared : RecursiveNamedPreparedStageContracts.Prepared recipe.compiled
    recipe.compiled.indexed.ancestry.graph.inputs.callable)
  (profile : recipe.compiled.compatible.checked.catalog.callableContracts = true)
  {identities : Dynamic.Value → Word → Prop}
  (observations : CompatibleEquality.FunctionObservations recipe.compiled.compatible.checked.catalog
    (CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry semanticFaults profile) identities)
  (semantic : ∀ reason token, semanticFaults reason token →
    CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics (.semantic reason) token)
  (family : ∀ {mapping world function native bindings parameterCore resultCore}
    (association : Association headers keys bodyRegistry semanticFaults mapping world function native
      bindings parameterCore resultCore),
    CallableIndexedOwnedPreparedStagedOrdinarySequenceCallerBounds.OrdinarySequenceFor stagePrepared association)
  (namedTerminals : ∀ header, header ∈ headers →
    CallableIndexedOwnedPreparedStagedNamedBodies.Body header)
  (namedSupport : ∀ header (member : header ∈ headers),
    CallableIndexedOwnedPreparedStagedNamedBodiesSupport.Support headers keys bodyRegistry header
      (RecursiveNamedPreparedStageScopes.registry stagePrepared) (namedTerminals header member) semanticFaults)
  (wellFormed : ProgramWellFormed (Program.ofChecked recipe.compiled.sourceProgram))
  {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store : Store}
  {anchor : CallableIndexedOwnedFunctionValues.Header recipe.compiled (Program.ofChecked recipe.compiled.sourceProgram)}
  {caller : Caller headers keys mapping world before store}
  {artifact : Artifact} {session : Session artifact} {entries : List Entry}
  (history : History headers keys
    (CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry semanticFaults profile)
    completion.result.context.registry anchor session mapping world before store caller entries)
  (entry : Entry) (member : entry ∈ entries)
  {parameter result : TypeSystem.Ty}
  (entryType : entry.sourceType = .function parameter result)
  {argument : SourceCorePublicValues.Value} {packedSource : Dynamic.Value}
  (input : RecursiveNamedPublicFunctionHistoryInputs.Input entries anchor.function.context parameter argument packedSource)

  (atRecipe : ArtifactRecipe artifact recipe)

local notation "functions" => CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry semanticFaults profile
local notation "callStages" => RecursiveNamedPreparedStageScopes.registry stagePrepared

include receiver stagePrepared profile observations semantic family namedTerminals namedSupport wellFormed
  history entry member entryType input in
/-- Every sufficiently funded actual public resume exports the Source result
and retains all previous captures. Both fuel bounds precede the actual resume;
no native completion or output success is a caller assumption. -/
theorem public_resume_has_sufficient_fuel
    (atRegistry : session.RegistryAt completion.result.context.registry)
    (exportsReady : session.ExportsReady)
    {inputFuel : Nat} {checkpoint : Checkpoint artifact}
    {actualParameter actualResult : TypeSystem.Ty} {nativeParameter nativeResult : Core.Ty}
    {callable packed : Core.Value} {encodedValues : SourceCoreCompatibleValues.Context}
    (started : StartAt session entry.handle argument inputFuel checkpoint recipe world store
      actualParameter actualResult nativeParameter nativeResult callable packed encodedValues)
    {invocation : Staging.Recursive.Scope} {sources : List Dynamic.Value}
    (packing : Dynamic.ValuesPack sources packedSource)
    {sourceSize : Nat} {sourceResult : Dynamic.Value} {after : Dynamic.Heap}
    (trace : Staging.Recursive.Size.Applies (Program.ofChecked recipe.compiled.sourceProgram) callStages sourceSize
      invocation anchor.function.context before entry.source sources (.value sourceResult) after)
    {publicArtifact : SourceCoreExecution.Artifact}
    {publicCheckpoint : SourceCoreExecution.Checkpoint publicArtifact}
    (atCheckpoint : publicCheckpoint.IndexedAt checkpoint) :
    ∃ receiving : CallableIndexedOwnedPublicFaultReceivers.Receiver recipe.compiled.indexed,
      receiving.result.context = encodedValues ∧
      CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt recipe.compiled.indexed receiving.entry
        receiving.result.context.registry receiving.result.extension receiving.result.diagnostics ∧
      SourceCoreRawMetadata.Extends completion.result.context.registry receiving.result.context.registry ∧
      (∀ token, checkpoint.diagnostic token = .ok (receiving.result.diagnostics.diagnostic? token)) ∧
    ∃ requiredExecution requiredOutput payload finalStore finalMap finalWorld,
      (∀ executionFuel, requiredExecution ≤ executionFuel →
        checkpoint.NativeDone executionFuel (.inRight .word payload) finalStore) ∧
      ResultAt (registry := receiving.result.context.registry) functions caller anchor.function.context
        result nativeResult (.value sourceResult) after (.inRight .word payload) finalStore finalMap finalWorld
        (CallableIndexedOwnedPublicDecodedStagedCallFaults.faults receiving.result.diagnostics) ∧
      ∀ executionFuel outputFuel (outcome : SourceCoreExecution.Outcome publicArtifact),
        requiredExecution ≤ executionFuel → requiredOutput ≤ outputFuel →
        publicCheckpoint.ResumeAt executionFuel outputFuel outcome →
        ∃ (publicCompletion : SourceCoreExecution.Completion publicArtifact)
          (actual : Completion artifact) (generation : SourceCorePublicValues.ExportGeneration)
          (reached : Caller headers keys finalMap finalWorld after finalStore),
          outcome = .succeeded publicCompletion ∧
          checkpoint.SucceededResultAt executionFuel outputFuel generation (.inRight .word payload) finalStore actual ∧
          publicCompletion.IndexedAt actual ∧ Relates caller reached ∧
          History headers keys functions receiving.result.context.registry anchor actual.session
            finalMap finalWorld after finalStore reached entries ∧
          actual.session.RegistryAt encodedValues.registry ∧ actual.session.ExportsReady := by
  obtain ⟨receiving, _indexed, contextAt, issued, extended, retained, _represented, _typed, diagnostics⟩ :=
    RecursiveNamedPublicActualRegistryStart.packed_input history atRegistry member entryType input started
  obtain ⟨program, present⟩ := RecursiveNamedPublicHistoryRegistryExtension.diagnostics_present history
  have semanticAt : ∀ reason token, semanticFaults reason token →
      CallableIndexedOwnedPublicDecodedStagedCallFaults.faults receiving.result.diagnostics (.semantic reason) token := by
    intro reason token related
    exact CompatibleRegistryDiagnosticExtension.staged_preserved recipe.compiled
      receiver issued present extended (semantic reason token related)
  have metadata : SourceCoreRawMetadata.Extends encodedValues.registry receiving.result.context.registry := by
    rw [contextAt]
    exact .refl _
  have imported := (history.current.2.2.2.2 entry member).1
  rw [entryType] at imported
  obtain ⟨parameterView, resultView⟩ := TypeSystem.Ty.function.inj
    (started.selected.spec.2.1.symm.trans imported.function_type.symm)
  obtain ⟨value, finalStore, finalMap, finalWorld, required, enough, resultAt⟩ :=
    RecursiveNamedPublicDirectCallableHistory.has_sufficient_fuel
      (completion := receiving) issued stagePrepared profile observations receiving.result.extension
      semanticAt family namedTerminals namedSupport wellFormed retained entry member entryType input
      started parameterView.symm metadata packing trace
  have success : ∃ payload, value = .inRight .word payload := by
    have represented := resultAt.1
    cases represented with
    | value related => exact ⟨_, rfl⟩
  obtain ⟨payload, rfl⟩ := success
  have represented : ValueRep recipe.compiled.compatible.checked receiving.result.context.registry
      functions finalMap finalWorld result sourceResult payload nativeResult := by
    have represented := resultAt.1
    cases represented with
    | value related => exact related
  have shape : SourceCorePublicOutputShapes.Output recipe.compiled.compatible.checked encodedValues.registry
      (finalStore.map Core.Value.type) recipe.program.layouts.definitions actualResult payload := by
    have shaped := CompatiblePublicOutputShapes.ValueRep.output represented
    rw [contextAt] at shaped
    rw [resultAt.2.1.runtime_hasTypes.world_eq] at shaped
    exact .compatible resultView shaped
  have checkpointRegistry : checkpoint.RegistryAt encodedValues.registry := by
    have values := started.values
    cases checkpoint
    change _ = encodedValues at values
    exact congrArg SourceCoreCompatibleValues.Context.registry values
  have ready := started.original.initial_registry.exportsReady exportsReady
  obtain ⟨requiredOutput, exports⟩ := publicCheckpoint.output_succeeded_uniform
    atCheckpoint started.recipe_eq checkpointRegistry ready started.requested shape
  refine ⟨receiving, contextAt, issued, extended, diagnostics, required, requiredOutput,
    payload, finalStore, finalMap, finalWorld, enough, resultAt, ?_⟩
  intro executionFuel outputFuel outcome executionBound outputBound resumed
  obtain ⟨publicCompletion, actual, generation, succeeded, exported, actualAt, returnedReady⟩ :=
    exports executionFuel (enough executionFuel executionBound) outputFuel outputBound outcome resumed
  obtain ⟨reached, related, returned⟩ := retained.after_packed_success started.original exported resultAt
  exact ⟨publicCompletion, actual, generation, reached, succeeded, exported, actualAt,
    related, returned, started.returned_registry exported, returnedReady⟩

end Meaning
end Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicActualRegistryOutputPreservation
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicActualRegistryOutputCollectionPreservation
/-! Source success produces sufficient public execution and export fuel,
then every selected nested output function joins the actual returned history. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicActualRegistryOutputCollectionPreservation
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open SourceCoreIndexedSession RecursiveNamedPublicStartMeaning
open RecursiveNamedPublicFunctionHistory (History Entry Caller)
open RecursiveNamedPublicDirectPackedInputMeaning (StartAt)
open RecursivePublicApplicationResult (ResultAt)
open CallableIndexedOwnedFunctionState
open CallableIndexedOwnedContextualTypedClosureReceipts (Association)

variable {recipe : Recipe}
variable
  {headers : List (CallableIndexedOwnedFunctionValues.Header recipe.compiled (Program.ofChecked recipe.compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key recipe.compiled (Program.ofChecked recipe.compiled.sourceProgram))}

section Meaning
variable {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver recipe.compiled.indexed}
  {bodyRegistry : SourceCoreRawMetadata.Registry} {semanticFaults : FunctionCalls.FaultRep}
  (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt recipe.compiled.indexed completion.entry
    completion.result.context.registry completion.result.extension completion.result.diagnostics)
  (stagePrepared : RecursiveNamedPreparedStageContracts.Prepared recipe.compiled
    recipe.compiled.indexed.ancestry.graph.inputs.callable)
  (profile : recipe.compiled.compatible.checked.catalog.callableContracts = true)
  {identities : Dynamic.Value → Word → Prop}
  (observations : CompatibleEquality.FunctionObservations recipe.compiled.compatible.checked.catalog
    (CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry semanticFaults profile) identities)
  (semantic : ∀ reason token, semanticFaults reason token →
    CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics (.semantic reason) token)
  (family : ∀ {mapping world function native bindings parameterCore resultCore}
    (association : Association headers keys bodyRegistry semanticFaults mapping world function native
      bindings parameterCore resultCore),
    CallableIndexedOwnedPreparedStagedOrdinarySequenceCallerBounds.OrdinarySequenceFor stagePrepared association)
  (namedTerminals : ∀ header, header ∈ headers →
    CallableIndexedOwnedPreparedStagedNamedBodies.Body header)
  (namedSupport : ∀ header (member : header ∈ headers),
    CallableIndexedOwnedPreparedStagedNamedBodiesSupport.Support headers keys bodyRegistry header
      (RecursiveNamedPreparedStageScopes.registry stagePrepared) (namedTerminals header member) semanticFaults)
  (wellFormed : ProgramWellFormed (Program.ofChecked recipe.compiled.sourceProgram))
  {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store : Store}
  {anchor : CallableIndexedOwnedFunctionValues.Header recipe.compiled (Program.ofChecked recipe.compiled.sourceProgram)}
  {caller : Caller headers keys mapping world before store}
  {artifact : Artifact} {session : Session artifact} {entries : List Entry}
  (history : History headers keys
    (CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry semanticFaults profile)
    completion.result.context.registry anchor session mapping world before store caller entries)
  (entry : Entry) (member : entry ∈ entries)
  {parameter result : TypeSystem.Ty}
  (entryType : entry.sourceType = .function parameter result)
  {argument : SourceCorePublicValues.Value} {packedSource : Dynamic.Value}
  (input : RecursiveNamedPublicFunctionHistoryInputs.Input entries anchor.function.context parameter argument packedSource)

  (atRecipe : ArtifactRecipe artifact recipe)

local notation "functions" => CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry semanticFaults profile
local notation "callStages" => RecursiveNamedPreparedStageScopes.registry stagePrepared

private theorem selected_of_cast {checked : SourceCoreCompatibleCatalog.Checked}
    {artifact : Artifact} {session : Session artifact} {sourceType : TypeSystem.Ty}
    {first second : SourceCorePublicValues.Value} (same : first = second)
    {selection : RecursiveNamedPublicNestedOutputSelections.Selection sourceType first}
    {source : Dynamic.Value} {native : Core.Value} {type : Core.Ty} {fuel : Nat} {entries : List Entry}
    (selected : RecursiveNamedPublicNestedOutputSelections.Selected checked session
      (same ▸ selection : RecursiveNamedPublicNestedOutputSelections.Selection sourceType second)
      source native type fuel entries) :
    RecursiveNamedPublicNestedOutputSelections.Selected checked session selection source native type fuel entries := by
  cases same
  exact selected

include receiver stagePrepared profile observations semantic family namedTerminals namedSupport wellFormed
  history entry member entryType input atRecipe in
/-- Both execution and output fuel bounds precede the actual resume. A structural
selection over that returned public value retains its functions in payload/row
order at the same Source after-heap, including repeated mapping entries. -/
theorem public_resume_has_sufficient_fuel
    (atRegistry : session.RegistryAt completion.result.context.registry)
    (exportsReady : session.ExportsReady)
    {inputFuel : Nat} {checkpoint : Checkpoint artifact}
    {actualParameter actualResult : TypeSystem.Ty} {nativeParameter nativeResult : Core.Ty}
    {callable packed : Core.Value} {encodedValues : SourceCoreCompatibleValues.Context}
    (started : StartAt session entry.handle argument inputFuel checkpoint recipe world store
      actualParameter actualResult nativeParameter nativeResult callable packed encodedValues)
    {invocation : Staging.Recursive.Scope} {sources : List Dynamic.Value}
    (packing : Dynamic.ValuesPack sources packedSource)
    {sourceSize : Nat} {sourceResult : Dynamic.Value} {after : Dynamic.Heap}
    (trace : Staging.Recursive.Size.Applies (Program.ofChecked recipe.compiled.sourceProgram) callStages sourceSize
      invocation anchor.function.context before entry.source sources (.value sourceResult) after)
    {publicArtifact : SourceCoreExecution.Artifact}
    {publicCheckpoint : SourceCoreExecution.Checkpoint publicArtifact}
    (atCheckpoint : publicCheckpoint.IndexedAt checkpoint) :
    ∃ receiving : CallableIndexedOwnedPublicFaultReceivers.Receiver recipe.compiled.indexed,
      receiving.result.context = encodedValues ∧
      CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt recipe.compiled.indexed receiving.entry
        receiving.result.context.registry receiving.result.extension receiving.result.diagnostics ∧
      SourceCoreRawMetadata.Extends completion.result.context.registry receiving.result.context.registry ∧
      (∀ token, checkpoint.diagnostic token = .ok (receiving.result.diagnostics.diagnostic? token)) ∧
    ∃ requiredExecution requiredOutput payload finalStore finalMap finalWorld,
      (∀ executionFuel, requiredExecution ≤ executionFuel →
        checkpoint.NativeDone executionFuel (.inRight .word payload) finalStore) ∧
      ResultAt (registry := receiving.result.context.registry) functions caller anchor.function.context
        result nativeResult (.value sourceResult) after (.inRight .word payload) finalStore finalMap finalWorld
        (CallableIndexedOwnedPublicDecodedStagedCallFaults.faults receiving.result.diagnostics) ∧
      ∀ executionFuel outputFuel (outcome : SourceCoreExecution.Outcome publicArtifact),
        requiredExecution ≤ executionFuel → requiredOutput ≤ outputFuel →
        publicCheckpoint.ResumeAt executionFuel outputFuel outcome →
        ∃ (publicCompletion : SourceCoreExecution.Completion publicArtifact)
          (actual : Completion artifact) (generation : SourceCorePublicValues.ExportGeneration),
          outcome = .succeeded publicCompletion ∧
          checkpoint.SucceededResultAt executionFuel outputFuel generation (.inRight .word payload) finalStore actual ∧
          publicCompletion.IndexedAt actual ∧
          actual.session.RegistryAt encodedValues.registry ∧ actual.session.ExportsReady ∧
          ∀ selection : RecursiveNamedPublicNestedOutputSelections.Selection result publicCompletion.value,
            ∃ (reached : Caller headers keys finalMap finalWorld after finalStore) (added : List Entry),
              RecursiveNamedPublicNestedOutputSelections.Selected recipe.compiled.compatible.checked actual.session
                selection sourceResult payload nativeResult outputFuel added ∧
              added.map Entry.handle = selection.handles ∧ Relates caller reached ∧
              History headers keys functions receiving.result.context.registry anchor actual.session
                finalMap finalWorld after finalStore reached (entries ++ added) := by
  obtain ⟨receiving, contextAt, issued, extended, diagnostics, requiredExecution, requiredOutput,
      payload, finalStore, finalMap, finalWorld, enough, resultAt, resumes⟩ :=
    RecursiveNamedPublicActualRegistryOutputPreservation.public_resume_has_sufficient_fuel
      receiver stagePrepared profile observations semantic family namedTerminals namedSupport wellFormed
      history entry member entryType input atRegistry exportsReady started packing trace atCheckpoint
  have retained := RecursiveNamedPublicHistoryRegistryExtension.extend_history history extended
  have metadata : SourceCoreRawMetadata.Extends receiving.result.context.registry encodedValues.registry := by
    rw [contextAt]
    exact .refl _
  have imported := (history.current.2.2.2.2 entry member).1
  rw [entryType] at imported
  obtain ⟨_parameterView, resultView⟩ := TypeSystem.Ty.function.inj
    (started.selected.spec.2.1.symm.trans imported.function_type.symm)
  refine ⟨receiving, contextAt, issued, extended, diagnostics, requiredExecution, requiredOutput,
    payload, finalStore, finalMap, finalWorld, enough, resultAt, ?_⟩
  intro executionFuel outputFuel outcome executionBound outputBound resumed
  obtain ⟨publicCompletion, actual, generation, _priorReached, succeeded, exported, actualAt,
      _priorRelated, _priorHistory, returnedRegistry, returnedReady⟩ :=
    resumes executionFuel outputFuel outcome executionBound outputBound resumed
  refine ⟨publicCompletion, actual, generation, succeeded, exported, actualAt,
    returnedRegistry, returnedReady, ?_⟩
  intro selection
  obtain ⟨reached, source, native, added, sourceValue, nativeValue, selected, handles, related, continued⟩ :=
    retained.collect_packed_nested_success rfl atRecipe started.original started.requested resultView.symm
      exported resultAt returnedRegistry metadata (actualAt.1 ▸ selection)
  have sourceEq := Staging.Recursive.Outcome.value.inj sourceValue
  have nativeEq : payload = native := (Core.Value.inRight.inj nativeValue).2
  cases sourceEq
  cases nativeEq
  have originalSelection : RecursiveNamedPublicNestedOutputSelections.Selected
      recipe.compiled.compatible.checked actual.session selection sourceResult payload nativeResult outputFuel added := selected_of_cast actualAt.1 selected
  have originalHandles := handles.trans
    (RecursiveNamedPublicNestedOutputSelections.Selection.handles_cast actualAt.1 selection)
  exact ⟨reached, added, originalSelection, originalHandles, related, continued⟩

end Meaning
end Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicActualRegistryOutputCollectionPreservation
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicHistoryIssuance
/-! Public issuance extends the semantic history attached to the same actual
session. The returned completion preserves the exact indexed handle and
current caller, ready for the existing history input and execution theorems. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicHistoryIssuance
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open SourceCoreIndexedSession RecursiveNamedPublicStartMeaning
open RecursiveNamedPublicFunctionHistory (Entry History Caller)
open CallableIndexedOwnedFunctionValues (Header)
open CallableIndexedOwnedPreparedFiniteNamedInventories (Input Issued Inventory headers)
open CallableIndexedOwnedPreparedBootstrapRootState (keys)

private theorem indexed_artifact_eq
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    {leftArtifact rightArtifact : SourceCoreIndexedSession.Artifact}
    {left : SourceCoreIndexedSession.Session leftArtifact} {right : SourceCoreIndexedSession.Session rightArtifact}
    (first : session.IndexedAt left) (second : session.IndexedAt right) : leftArtifact = rightArtifact := by
  rcases artifact with ⟨compilation, opened⟩
  cases opened with
  | empty selected => exact False.elim first
  | indexed recipe selected native atRecipe =>
      cases session
      exact first.1.symm.trans second.1

/-- The public named issuance supplies the exact new entry at the existing
current caller, without a representation or Source typing premise. -/
theorem named_remembered
    {compiled : SourceCoreUnifiedCompilation.Compiled} {recipe : Recipe}
    (prepared : Recipe.prepare compiled = .ok recipe)
    (inputs : List (Input compiled)) (rows : Inventory inputs)
    {input : Input compiled} (packet : Issued input) (member : Inventory.HasRow packet rows)
    (bodyRegistry registry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep)
    (profile : compiled.compatible.checked.catalog.callableContracts = true)
    {nativeArtifact : SourceCoreIndexedSession.Artifact} {nativeSession : SourceCoreIndexedSession.Session nativeArtifact}
    {entries : List Entry} {mapping : LocationMap} {world : StoreTyping} {heap : Dynamic.Heap} {store : Store}
    {caller : Caller (headers rows) (keys compiled) mapping world heap store}
    {anchor : Header compiled (Program.ofChecked compiled.sourceProgram)}
    (history : History (headers rows) (keys compiled)
      (CallableIndexedOwnedContextualCellOrigins.functions (headers rows) (keys compiled) bodyRegistry faults profile)
      registry anchor nativeSession mapping world heap store caller entries)
    (atRecipe : ArtifactRecipe nativeArtifact recipe)
    {publicArtifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session publicArtifact}
    (atSession : session.IndexedAt nativeSession)
    {issued : SourceCoreExecution.Completion publicArtifact} {issuanceFuel : Nat}
    (issuance : session.NamedIssuedAt packet.header.named.signature.key issuanceFuel issued)
    {handle : Handle} (handleValue : issued.value = .function handle)
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram)) :
    ∃ (actual : SourceCoreIndexedSession.Completion nativeArtifact) (native : Core.Value),
      issued.IndexedAt actual ∧
      History (headers rows) (keys compiled)
        (CallableIndexedOwnedContextualCellOrigins.functions (headers rows) (keys compiled) bodyRegistry faults profile)
        registry anchor actual.session mapping world heap store caller
        (entries ++ [⟨packet.header.named.specialized.function.type,
          .global (CallableNamedReversal.global (CallableNamedMetadata.global
            packet.header.named.specialized input.prepared.available)), handle, native,
          CallableContract.functionType packet.header.named.signature.parameterType packet.header.named.signature.resultType,
          issuanceFuel⟩]) := by
  obtain ⟨actualArtifact, before, actual, beforeAt, actualIssuance, completedAt⟩ := issuance
  have sameArtifact := indexed_artifact_eq atSession beforeAt
  cases sameArtifact
  have sameSession := atSession.unique beforeAt
  cases sameSession
  obtain ⟨native, extended⟩ := History.remember_named prepared inputs rows packet member
    bodyRegistry registry faults profile history actualIssuance atRecipe
    (completedAt.1.symm.trans handleValue) wellFormed
  exact ⟨actual, native, completedAt, extended⟩

/-- The public builtin issuance joins the same history and leaves its native
and Source heaps unchanged, retaining all earlier exported closures. -/
theorem builtin_remembered
    {compiled : SourceCoreUnifiedCompilation.Compiled} {recipe : Recipe}
    (prepared : Recipe.prepare compiled = .ok recipe)
    (headers : List (Header compiled (Program.ofChecked compiled.sourceProgram)))
    (keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram)))
    (bodyRegistry registry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep)
    (profile : compiled.compatible.checked.catalog.callableContracts = true)
    {nativeArtifact : SourceCoreIndexedSession.Artifact} {nativeSession : SourceCoreIndexedSession.Session nativeArtifact}
    {entries : List Entry} {mapping : LocationMap} {world : StoreTyping} {heap : Dynamic.Heap} {store : Store}
    {caller : Caller headers keys mapping world heap store}
    {anchor : Header compiled (Program.ofChecked compiled.sourceProgram)}
    (history : History headers keys
      (CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry faults profile)
      registry anchor nativeSession mapping world heap store caller entries)
    (atRecipe : ArtifactRecipe nativeArtifact recipe)
    {publicArtifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session publicArtifact}
    (atSession : session.IndexedAt nativeSession)
    {issued : SourceCoreExecution.Completion publicArtifact} {function : BuiltinFunctionId} {issuanceFuel : Nat}
    (issuance : session.BuiltinIssuedAt function issuanceFuel issued)
    {handle : Handle} (handleValue : issued.value = .function handle) :
    ∃ (actual : SourceCoreIndexedSession.Completion nativeArtifact) (native : Core.Value),
      issued.IndexedAt actual ∧
      History headers keys
        (CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry faults profile)
        registry anchor actual.session mapping world heap store caller
        (entries ++ [⟨function.type, .builtin ⟨function⟩, handle, native,
          CallableContract.functionType (SourceCoreInteger.builtinParameter function) (SourceCoreInteger.builtinResult function),
          issuanceFuel⟩]) := by
  obtain ⟨actualArtifact, before, actual, beforeAt, actualIssuance, completedAt⟩ := issuance
  have sameArtifact := indexed_artifact_eq atSession beforeAt
  cases sameArtifact
  have sameSession := atSession.unique beforeAt
  cases sameSession
  obtain ⟨native, extended⟩ := History.remember_builtin prepared headers keys bodyRegistry registry faults profile
    history actualIssuance atRecipe (completedAt.1.symm.trans handleValue)
  exact ⟨actual, native, completedAt, extended⟩

end Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicHistoryIssuance
end
