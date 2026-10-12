import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicReturnedInputRegistry
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicHistoryFrontdoor
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicActualRegistryNamedStart
import Solcore.SourceSemantics.CoreLowering.CompatibleRegistryDiagnosticExtension

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
