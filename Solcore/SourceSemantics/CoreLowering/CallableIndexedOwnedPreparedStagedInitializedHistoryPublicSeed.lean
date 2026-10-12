import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedBodiesSupport
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedInitializedNestedPublicBounds
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicFunctionHistory

/-! Actual bootstrap, original nested input encoding and a successful public
function export establish the first retained history entry. The owned caller,
Source captures and returned heap are produced by the existing public theorem.
Subsequent history continuations need no separate representation assumption. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedInitializedHistoryPublicSeed
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState
open CallableIndexedOwnedPreparedBootstrapRootState (keys owner)
open CallableIndexedOwnedPreparedFiniteNamedInventories (Input Inventory headers)
open CallableIndexedOwnedContextualTypedClosureReceipts (Association)
open CallableIndexedOwnedPreparedStagedOrdinarySequenceCallerBounds (OrdinarySequenceFor)
open CallableIndexedOwnedPreparedStagedNamedBodies (Body)
open CallableIndexedOwnedPreparedStagedNamedBodiesSupport (Support)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {completion : SourceCoreCallableIndexedPrograms.Completion compiled.indexed}
  (inputs : List (Input compiled)) (rows : Inventory inputs)
  (distinct : (inputs.map (fun input => input.prepared.index)).Nodup)
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
  {root : SourceCoreIndexedSession.Root compiled}
  {header : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)}
  (selected : RecursiveNamedPublicRootMeaning.RootSelection
    (values := .initial compiled.compatible.checked)
    (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
    (program := Program.ofChecked compiled.sourceProgram) (headers rows) root header)
  {publicCompiled : SourceCoreExecution.Compiled} {publicArtifact : SourceCoreExecution.Artifact}
  {publicBootstrap : SourceCoreExecution.Bootstrap publicArtifact}
  {bootstrapSession publicSession : SourceCoreExecution.Session publicArtifact}
  {publicCheckpoint : SourceCoreExecution.Checkpoint publicArtifact}
  {nativeArtifact : SourceCoreIndexedSession.Artifact}
  {nativeSession : SourceCoreIndexedSession.Session nativeArtifact}
  {nativeCheckpoint : SourceCoreIndexedSession.Checkpoint nativeArtifact}
  {key : SourceCoreIndexedSession.Key} {publicArguments : List SourceCorePublicValues.Value}
  {bootstrapFuel : Nat} {options : SourceCoreExecution.RunOptions}
  {world : StoreTyping} {store : Store} {payloads : Environment}
  {encodedValues : SourceCoreCompatibleValues.Context}
  (opened : publicArtifact.IndexedAt publicCompiled recipe nativeArtifact)
  (fresh : publicBootstrap.FreshAt)
  (ready : publicBootstrap.ReadyAt bootstrapFuel bootstrapSession)
  (sameRuntime : bootstrapSession.SameRuntime publicSession)
  (atSession : publicSession.IndexedAt nativeSession)
  (atCheckpoint : publicCheckpoint.IndexedAt nativeCheckpoint)
  (started : RecursiveNamedPublicStartMeaning.StartAt nativeSession key publicArguments
    options.inputValidationFuel nativeCheckpoint recipe
    ((SourceCoreIndexedSession.Recipe.prepare_compiled prepared).symm ▸ root)
    world store payloads encodedValues)
  {arguments : List Dynamic.Value}
  (inputReceipts : RecursiveNamedPublicNestedInputs.Inputs rows nativeSession
    header.function.context (header.bindings.map (fun binding => binding.1.scheme.body))
    publicArguments arguments)
  (metadata : SourceCoreRawMetadata.Extends encodedValues.registry completion.result.context.registry)
  {rawD : SourceTypedRuntime.RuntimeEvidenceEnvironment} {function : Dynamic.GlobalFunction}
  (sourceAt : CallableIndexedOwnedFunctionValues.NamedSourceAt header rawD function)
  {invocation : Staging.Recursive.Scope}

local notation "rootHeaders" => headers rows
local notation "rootKeys" => keys compiled
local notation "rootOwner" => owner compiled
local notation "rootFunctions" => CallableIndexedOwnedContextualCellOrigins.functions rootHeaders rootKeys bodyRegistry semanticFaults profile
local notation "rootModel" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked completion.result.context.registry rootFunctions
local notation "rootFaults" => CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics

include distinct receiver observations extension semantic family namedTerminals namedSupport wellFormed
  prepared selected opened fresh ready sameRuntime atSession atCheckpoint started inputReceipts metadata sourceAt in
/-- A first actual public function export seeds the complete continuation
history, including its captured environment and real returned session. -/
theorem public_run_succeeded_remembers
    {publicCompletion : SourceCoreExecution.Completion publicArtifact}
    (publicStart : publicSession.start key publicArguments options.inputValidationFuel = .ok publicCheckpoint)
    (publicRun : publicSession.RunAt key publicArguments options (.ok (.succeeded publicCompletion)))
    {handle : SourceCorePublicValues.Handle}
    (returnedHandle : publicCompletion.value = .function handle)
    (descriptor : SourceCoreCallableContracts.Descriptor compiled.indexed.ancestry.graph.inputs.callable.table
      (.named header.named.signature.key)) :
    ∃ caller : State rootHeaders rootKeys
        ⟨[], [], world, ⟨[]⟩, store, SourceCoreCallableIndexedTemplates.globalEnvironment compiled.indexed⟩,
      ∃ (actual : SourceCoreIndexedSession.Completion nativeArtifact)
        (generation : SourceCorePublicValues.ExportGeneration) (value : Value) (finalStore : Store)
        (capture : CallableIndexedOwnedFunctionValues.NamedCapture rootHeaders (rootOwner).key header [] world)
        (sourceSize : Nat) (outcome : Staging.Recursive.Outcome) (after : Dynamic.Heap)
        (finalMap : LocationMap) (finalWorld : StoreTyping),
        nativeCheckpoint.SucceededResultAt options.executionFuel options.outputValidationFuel
          generation value finalStore actual ∧
        publicCompletion.value = actual.value ∧ publicCompletion.sourceType = actual.sourceType ∧
        publicCompletion.boundaryFuel = actual.boundaryFuel ∧ publicCompletion.session.IndexedAt actual.session ∧
        Staging.Recursive.Size.Applies (Program.ofChecked compiled.sourceProgram)
          (RecursiveNamedPreparedStageScopes.registry stagePrepared) sourceSize invocation header.function.context ⟨[]⟩
          (.global function) arguments outcome after ∧
        ∃ _result : CallableIndexedOwnedPreparedStagedTerminalNamedInvocationBounds.ResultAt
          (registry := completion.result.context.registry) (payloads := payloads)
          (scope := []) (canonical := SourceCoreCallableIndexedTemplates.globalEnvironment compiled.indexed)
          rootFunctions rootOwner caller header capture header.function.context outcome after value finalStore finalMap finalWorld rootFaults,
        ∃ returned : RecursiveNamedPublicFunctionHistory.Caller rootHeaders rootKeys finalMap finalWorld after finalStore,
        ∃ source payload, outcome = .value source ∧ value = .inRight .word payload ∧
          Relates caller returned ∧
          RecursiveNamedPublicFunctionHistory.History rootHeaders rootKeys rootFunctions
            completion.result.context.registry header actual.session finalMap finalWorld after finalStore
            returned
            [⟨header.function.resultType, source, handle, payload, header.output,
              options.outputValidationFuel⟩] := by
  have sameCompiled := SourceCoreIndexedSession.Recipe.prepare_compiled prepared
  cases sameCompiled
  have supports := (RecursiveNamedPublicReturnedValues.header_context_supports header header wellFormed).2
  obtain ⟨caller, actual, generation, value, finalStore, capture, sourceSize, outcome, after, finalMap, finalWorld,
      succeeded, valueEq, typeEq, budgetEq, sessionAt, trace, result⟩ :=
    CallableIndexedOwnedPreparedStagedInitializedNestedPublicBounds.public_run_succeeded_reflects
      (inputs := inputs) (rows := rows) (distinct := distinct) (stagePrepared := stagePrepared)
      (receiver := receiver) (profile := profile) (observations := observations)
      (extension := extension) (semantic := semantic) (family := family)
      (namedTerminals := namedTerminals) (namedSupport := namedSupport)
      (acceptedPlan := SourceCoreUnifiedPreparationCertificates.compiled_planPrepared recipe.compiled) (wellFormed := wellFormed) (prepared := prepared) (selected := selected)
      (opened := opened) (fresh := fresh) (ready := ready) (sameRuntime := sameRuntime)
      (atSession := atSession) (atCheckpoint := atCheckpoint) (started := started)
      (inputReceipts := inputReceipts) (metadata := metadata) (sourceAt := sourceAt) (supports := supports)
      publicStart publicRun descriptor
  have atRecipe : nativeArtifact.RecipeAt recipe := by
    cases nativeArtifact
    exact started.recipe_eq
  have requested := started.original.result_type_at atRecipe started.selected
  have rawResult := (RecursiveNamedPublicRootSourceSignature.inputs_and_result selected).2
  rw [rawResult] at requested
  obtain ⟨reached, source, payload, sourceValue, nativeValue, related, retained⟩ :=
    RecursiveNamedPublicFunctionHistory.first_remembered rfl started selected requested succeeded result
      (valueEq.symm.trans returnedHandle)
  exact ⟨caller, actual, generation, value, finalStore, capture, sourceSize, outcome, after, finalMap, finalWorld,
    succeeded, valueEq, typeEq, budgetEq, sessionAt, trace, result, reached, source, payload,
    sourceValue, nativeValue, related, retained⟩

include distinct receiver observations extension semantic family namedTerminals namedSupport wellFormed
  prepared selected opened fresh ready sameRuntime atSession atCheckpoint started inputReceipts metadata sourceAt in
/-- Selected function leaves from the first actual public product output
seed a history with their original captures and recursive validation budgets. -/
theorem public_run_succeeded_collects
    {publicCompletion : SourceCoreExecution.Completion publicArtifact}
    (publicStart : publicSession.start key publicArguments options.inputValidationFuel = .ok publicCheckpoint)
    (publicRun : publicSession.RunAt key publicArguments options (.ok (.succeeded publicCompletion)))
    (outputSelection : RecursiveNamedPublicOutputSelections.Selection
      header.function.resultType publicCompletion.value)
    (descriptor : SourceCoreCallableContracts.Descriptor compiled.indexed.ancestry.graph.inputs.callable.table
      (.named header.named.signature.key)) :
    ∃ caller : State rootHeaders rootKeys
        ⟨[], [], world, ⟨[]⟩, store, SourceCoreCallableIndexedTemplates.globalEnvironment compiled.indexed⟩,
      ∃ (actual : SourceCoreIndexedSession.Completion nativeArtifact)
        (generation : SourceCorePublicValues.ExportGeneration) (value : Value) (finalStore : Store)
        (capture : CallableIndexedOwnedFunctionValues.NamedCapture rootHeaders (rootOwner).key header [] world)
        (sourceSize : Nat) (outcome : Staging.Recursive.Outcome) (after : Dynamic.Heap)
        (finalMap : LocationMap) (finalWorld : StoreTyping),
        nativeCheckpoint.SucceededResultAt options.executionFuel options.outputValidationFuel
          generation value finalStore actual ∧
        publicCompletion.value = actual.value ∧ publicCompletion.sourceType = actual.sourceType ∧
        publicCompletion.boundaryFuel = actual.boundaryFuel ∧ publicCompletion.session.IndexedAt actual.session ∧
        Staging.Recursive.Size.Applies (Program.ofChecked compiled.sourceProgram)
          (RecursiveNamedPreparedStageScopes.registry stagePrepared) sourceSize invocation header.function.context ⟨[]⟩
          (.global function) arguments outcome after ∧
        ∃ _result : CallableIndexedOwnedPreparedStagedTerminalNamedInvocationBounds.ResultAt
          (registry := completion.result.context.registry) (payloads := payloads)
          (scope := []) (canonical := SourceCoreCallableIndexedTemplates.globalEnvironment compiled.indexed)
          rootFunctions rootOwner caller header capture header.function.context outcome after value finalStore finalMap finalWorld rootFaults,
        ∃ returned : RecursiveNamedPublicFunctionHistory.Caller rootHeaders rootKeys finalMap finalWorld after finalStore,
        ∃ added : List RecursiveNamedPublicFunctionHistory.Entry,
          added.map RecursiveNamedPublicFunctionHistory.Entry.handle = outputSelection.handles ∧
          Relates caller returned ∧
          RecursiveNamedPublicFunctionHistory.History rootHeaders rootKeys rootFunctions
            completion.result.context.registry header actual.session finalMap finalWorld after finalStore
            returned added := by
  have sameCompiled := SourceCoreIndexedSession.Recipe.prepare_compiled prepared
  cases sameCompiled
  have supports := (RecursiveNamedPublicReturnedValues.header_context_supports header header wellFormed).2
  obtain ⟨caller, actual, generation, value, finalStore, capture, sourceSize, outcome, after, finalMap, finalWorld,
      succeeded, valueEq, typeEq, budgetEq, sessionAt, trace, result⟩ :=
    CallableIndexedOwnedPreparedStagedInitializedNestedPublicBounds.public_run_succeeded_reflects
      (inputs := inputs) (rows := rows) (distinct := distinct) (stagePrepared := stagePrepared)
      (receiver := receiver) (profile := profile) (observations := observations)
      (extension := extension) (semantic := semantic) (family := family)
      (namedTerminals := namedTerminals) (namedSupport := namedSupport)
      (acceptedPlan := SourceCoreUnifiedPreparationCertificates.compiled_planPrepared recipe.compiled) (wellFormed := wellFormed) (prepared := prepared) (selected := selected)
      (opened := opened) (fresh := fresh) (ready := ready) (sameRuntime := sameRuntime)
      (atSession := atSession) (atCheckpoint := atCheckpoint) (started := started)
      (inputReceipts := inputReceipts) (metadata := metadata) (sourceAt := sourceAt) (supports := supports)
      publicStart publicRun descriptor
  have atRecipe : nativeArtifact.RecipeAt recipe := by
    cases nativeArtifact
    exact started.recipe_eq
  have requested := started.original.result_type_at atRecipe started.selected
  have rawResult := (RecursiveNamedPublicRootSourceSignature.inputs_and_result selected).2
  rw [rawResult] at requested
  let actualSelection : RecursiveNamedPublicOutputSelections.Selection header.function.resultType actual.value :=
    valueEq ▸ outputSelection
  obtain ⟨reached, added, handles, related, retained⟩ :=
    RecursiveNamedPublicFunctionHistory.first_collected rfl started selected requested succeeded result actualSelection
  have sameHandles : actualSelection.handles = outputSelection.handles :=
    RecursiveNamedPublicOutputSelections.Selection.handles_cast valueEq outputSelection
  exact ⟨caller, actual, generation, value, finalStore, capture, sourceSize, outcome, after, finalMap, finalWorld,
    succeeded, valueEq, typeEq, budgetEq, sessionAt, trace, result, reached, added,
    handles.trans sameHandles, related, retained⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedInitializedHistoryPublicSeed
