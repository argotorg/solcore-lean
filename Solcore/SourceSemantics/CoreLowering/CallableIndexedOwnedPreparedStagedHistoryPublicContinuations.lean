import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedHistoryPublicBounds

/-! Public success returns a new semantic history for the actual returned
session. Data results retain older exports; a newly returned function may be
recorded alongside all previous closures before the following public call. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedHistoryPublicContinuations
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState
open CallableIndexedOwnedPreparedBootstrapRootState (keys owner)
open CallableIndexedOwnedPreparedFiniteNamedInventories (Input Inventory headers)
open CallableIndexedOwnedContextualTypedClosureReceipts (Association)
open CallableIndexedOwnedPreparedStagedOrdinarySequenceCallerBounds (OrdinarySequenceFor)
open CallableIndexedOwnedPreparedStagedTerminalNamedGlobalDispatch (Terminal)
open CallableIndexedOwnedPreparedStagedSelectedBodyStaticSupport (NamedSupport)

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
  (namedTerminals : ∀ header, header ∈ headers rows → Terminal header)
  (namedSupport : ∀ header (member : header ∈ headers rows),
    NamedSupport header (RecursiveNamedPreparedStageScopes.registry stagePrepared)
      (namedTerminals header member) semanticFaults)
  {beforePlan : SourceCompilationPlan.Plan} {planFuel planBudget : Nat}
  (acceptedPlan : SourceCompilationPlan.prepareExecutablePlanEvidenceWithBudget
    compiled.sourceProgram beforePlan planFuel planBudget = .ok compiled.indexed.base.plan)
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

include receiver observations extension semantic family namedTerminals namedSupport acceptedPlan wellFormed
  prepared selected history atCheckpoint started inputReceipts metadata sourceAt in
/-- Successful calls retain every earlier export at their real returned state. -/
theorem public_run_succeeded_retains
    {publicCompletion : SourceCoreExecution.Completion publicArtifact}
    (publicStart : publicSession.start key publicArguments options.inputValidationFuel = .ok publicCheckpoint)
    (publicRun : publicSession.RunAt key publicArguments options (.ok (.succeeded publicCompletion)))
    (descriptor : SourceCoreCallableContracts.Descriptor compiled.indexed.ancestry.graph.inputs.callable.table
      (.named header.named.signature.key)) :
    ∃ (actual : SourceCoreIndexedSession.Completion nativeArtifact)
        (generation : SourceCorePublicValues.ExportGeneration) (value : Value) (finalStore : Store)
        (capture : CallableIndexedOwnedFunctionValues.NamedCapture rootHeaders (rootOwner).key header mapping world)
        (sourceSize : Nat) (outcome : Staging.Recursive.Outcome) (after : Dynamic.Heap)
        (finalMap : LocationMap) (finalWorld : StoreTyping),
        nativeCheckpoint.SucceededResultAt options.executionFuel options.outputValidationFuel
          generation value finalStore actual ∧
        publicCompletion.value = actual.value ∧ publicCompletion.sourceType = actual.sourceType ∧
        publicCompletion.boundaryFuel = actual.boundaryFuel ∧ publicCompletion.session.IndexedAt actual.session ∧
        Staging.Recursive.Size.Applies (Program.ofChecked compiled.sourceProgram)
          (RecursiveNamedPreparedStageScopes.registry stagePrepared) sourceSize invocation anchor.function.context before
          (.global function) arguments outcome after ∧
        ∃ _result : CallableIndexedOwnedPreparedStagedTerminalNamedInvocationBounds.ResultAt
          (registry := completion.result.context.registry) (payloads := payloads)
          (scope := []) (canonical := SourceCoreCallableIndexedTemplates.globalEnvironment compiled.indexed)
          rootFunctions rootOwner caller header capture anchor.function.context outcome after value finalStore finalMap finalWorld rootFaults,
        ∃ reached : RecursiveNamedPublicFunctionHistory.Caller rootHeaders rootKeys finalMap finalWorld after finalStore,
        Relates caller reached ∧
          RecursiveNamedPublicFunctionHistory.History rootHeaders rootKeys rootFunctions
            completion.result.context.registry anchor actual.session finalMap finalWorld after finalStore
            reached entries := by
  have sameCompiled := SourceCoreIndexedSession.Recipe.prepare_compiled prepared
  cases sameCompiled
  obtain ⟨actual, generation, value, finalStore, capture, sourceSize, outcome, after, finalMap, finalWorld,
      succeeded, valueEq, typeEq, budgetEq, sessionAt, trace, result⟩ :=
    CallableIndexedOwnedPreparedStagedHistoryPublicBounds.public_run_succeeded_reflects
      (inputs := inputs) (rows := rows) (stagePrepared := stagePrepared) (receiver := receiver) (profile := profile)
      (observations := observations) (extension := extension) (semantic := semantic)
      (family := family) (namedTerminals := namedTerminals) (namedSupport := namedSupport)
      (acceptedPlan := acceptedPlan) (wellFormed := wellFormed) (prepared := prepared) (selected := selected)
      (caller := caller) (history := history) (atCheckpoint := atCheckpoint) (started := started)
      (inputReceipts := inputReceipts) (metadata := metadata) (sourceAt := sourceAt)
      publicStart publicRun descriptor
  exact ⟨actual, generation, value, finalStore, capture, sourceSize, outcome, after, finalMap, finalWorld,
    succeeded, valueEq, typeEq, budgetEq, sessionAt, trace, result,
    history.after_success rfl started selected succeeded result⟩

include receiver observations extension semantic family namedTerminals namedSupport acceptedPlan wellFormed
  prepared selected history atCheckpoint started inputReceipts metadata sourceAt in
/-- A newly exported function joins the history of the real returned session. -/
theorem public_run_succeeded_remembers
    {publicCompletion : SourceCoreExecution.Completion publicArtifact}
    (publicStart : publicSession.start key publicArguments options.inputValidationFuel = .ok publicCheckpoint)
    (publicRun : publicSession.RunAt key publicArguments options (.ok (.succeeded publicCompletion)))
    {handle : SourceCorePublicValues.Handle}
    (returnedHandle : publicCompletion.value = .function handle)
    (descriptor : SourceCoreCallableContracts.Descriptor compiled.indexed.ancestry.graph.inputs.callable.table
      (.named header.named.signature.key)) :
    ∃ (actual : SourceCoreIndexedSession.Completion nativeArtifact)
        (generation : SourceCorePublicValues.ExportGeneration) (value : Value) (finalStore : Store)
        (capture : CallableIndexedOwnedFunctionValues.NamedCapture rootHeaders (rootOwner).key header mapping world)
        (sourceSize : Nat) (outcome : Staging.Recursive.Outcome) (after : Dynamic.Heap)
        (finalMap : LocationMap) (finalWorld : StoreTyping),
        nativeCheckpoint.SucceededResultAt options.executionFuel options.outputValidationFuel
          generation value finalStore actual ∧
        publicCompletion.value = actual.value ∧ publicCompletion.sourceType = actual.sourceType ∧
        publicCompletion.boundaryFuel = actual.boundaryFuel ∧ publicCompletion.session.IndexedAt actual.session ∧
        Staging.Recursive.Size.Applies (Program.ofChecked compiled.sourceProgram)
          (RecursiveNamedPreparedStageScopes.registry stagePrepared) sourceSize invocation anchor.function.context before
          (.global function) arguments outcome after ∧
        ∃ _result : CallableIndexedOwnedPreparedStagedTerminalNamedInvocationBounds.ResultAt
          (registry := completion.result.context.registry) (payloads := payloads)
          (scope := []) (canonical := SourceCoreCallableIndexedTemplates.globalEnvironment compiled.indexed)
          rootFunctions rootOwner caller header capture anchor.function.context outcome after value finalStore finalMap finalWorld rootFaults,
        ∃ reached : RecursiveNamedPublicFunctionHistory.Caller rootHeaders rootKeys finalMap finalWorld after finalStore,
        ∃ source payload, outcome = .value source ∧ value = .inRight .word payload ∧
          Relates caller reached ∧
          RecursiveNamedPublicFunctionHistory.History rootHeaders rootKeys rootFunctions
            completion.result.context.registry anchor actual.session finalMap finalWorld after finalStore
            reached
            (entries ++ [⟨header.function.resultType, source, handle, payload, header.output,
              options.outputValidationFuel⟩]) := by
  have sameCompiled := SourceCoreIndexedSession.Recipe.prepare_compiled prepared
  cases sameCompiled
  obtain ⟨actual, generation, value, finalStore, capture, sourceSize, outcome, after, finalMap, finalWorld,
      succeeded, valueEq, typeEq, budgetEq, sessionAt, trace, result⟩ :=
    CallableIndexedOwnedPreparedStagedHistoryPublicBounds.public_run_succeeded_reflects
      (inputs := inputs) (rows := rows) (stagePrepared := stagePrepared) (receiver := receiver) (profile := profile)
      (observations := observations) (extension := extension) (semantic := semantic)
      (family := family) (namedTerminals := namedTerminals) (namedSupport := namedSupport)
      (acceptedPlan := acceptedPlan) (wellFormed := wellFormed) (prepared := prepared) (selected := selected)
      (caller := caller) (history := history) (atCheckpoint := atCheckpoint) (started := started)
      (inputReceipts := inputReceipts) (metadata := metadata) (sourceAt := sourceAt)
      publicStart publicRun descriptor
  have atRecipe : nativeArtifact.RecipeAt recipe := by
    cases nativeArtifact
    exact started.recipe_eq
  have requested := started.original.result_type_at atRecipe started.selected
  have rawResult := (RecursiveNamedPublicRootSourceSignature.inputs_and_result selected).2
  rw [rawResult] at requested
  obtain ⟨reached, source, payload, sourceValue, nativeValue, related, retained⟩ :=
    history.remember_success rfl started selected requested succeeded result (valueEq.symm.trans returnedHandle)
  exact ⟨actual, generation, value, finalStore, capture, sourceSize, outcome, after, finalMap, finalWorld,
    succeeded, valueEq, typeEq, budgetEq, sessionAt, trace, result, reached, source, payload,
    sourceValue, nativeValue, related, retained⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedHistoryPublicContinuations
