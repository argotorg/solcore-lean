import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedBootstrapGlobalReferences
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicReturnedValues
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicFunctionHistory
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicFunctionHistoryArgumentsReceiving
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedOrdinarySequenceCallerBounds

/-! Multiple exported functions retain their Source captures through actual
successful executions. A finite history supplies the current owned caller,
heap and all retained handles. The original startup selects those handles
inside arbitrary ordered arguments and data containers before the supported
public execution theorem is invoked. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedHistoryPublicBounds
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

include wellFormed prepared selected history started inputReceipts metadata in
/-- History supplies the current state and every retained function's meaning.
The actual encoder supplies all new data and argument positions. -/
private theorem current_arguments :
    CallableIndexedOwnedIndirectExpressionHeads.StableRows caller ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked completion.result.context.registry
        rootFunctions mapping world before store ∧
      Dynamic.HeapWellTyped header.function.context before ∧
      CallableIndexedParameterMeaning.Arguments rootModel mapping world header.bindings arguments payloads ∧
      Dynamic.ValuesHaveTypes header.function.context before arguments header.types := by
  have sameCompiled := SourceCoreIndexedSession.Recipe.prepare_compiled prepared
  cases sameCompiled
  obtain ⟨_nativeAt, heaps, stable, heapTyped, retained⟩ := history.current
  have contexts := RecursiveNamedPublicReturnedValues.header_context_supports anchor header wellFormed
  obtain ⟨represented, argumentsTyped⟩ :=
    RecursiveNamedPublicFunctionHistoryArgumentsReceiving.StartAt.history_arguments_receiving
      started _ selected entries (fun entry member => (retained entry member).1)
      (fun entry member => (retained entry member).2.1)
      (fun entry member => (retained entry member).2.2.transportContext contexts.1)
      inputReceipts metadata wellFormed
  exact ⟨stable, heaps, heapTyped.transportContext contexts.1, represented, argumentsTyped⟩

include receiver observations extension semantic family namedTerminals namedSupport acceptedPlan wellFormed
  prepared selected history atCheckpoint started inputReceipts metadata sourceAt in
/-- Actual history feeds the public outcome at the current captured state. -/
theorem public_run_succeeded_reflects
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
        CallableIndexedOwnedPreparedStagedTerminalNamedInvocationBounds.ResultAt
          (registry := completion.result.context.registry) (payloads := payloads)
          (scope := []) (canonical := SourceCoreCallableIndexedTemplates.globalEnvironment compiled.indexed)
          rootFunctions rootOwner caller header capture anchor.function.context outcome after value finalStore finalMap finalWorld rootFaults := by
  obtain ⟨stable, heaps, heapTyped, represented, argumentsTyped⟩ :=
    current_arguments (inputs := inputs) (rows := rows) (profile := profile)
      (wellFormed := wellFormed) (prepared := prepared) (selected := selected)
      (history := history) (started := started) (inputReceipts := inputReceipts) (metadata := metadata)
  have globalReference := CallableIndexedOwnedPreparedBootstrapGlobalReferences.global_reference rows header selected.member
  have supports := (RecursiveNamedPublicReturnedValues.header_context_supports header anchor wellFormed).2
  exact CallableIndexedOwnedPreparedStagedOrdinarySequenceCallerBounds.public_run_succeeded_reflects
      (stagePrepared := stagePrepared) (receiver := receiver) (profile := profile)
      (observations := observations) (extension := extension) (semantic := semantic)
      (family := family) (namedTerminals := namedTerminals) (namedSupport := namedSupport)
      (acceptedPlan := acceptedPlan) (wellFormed := wellFormed) (selected := selected)
      (owner := rootOwner) (caller := caller) (globalReference := globalReference) (stable := stable)
      (heapTyped := heapTyped) (argumentsTyped := argumentsTyped) (represented := represented)
      (heaps := heaps) (sourceAt := sourceAt) (supports := supports)
      (sameCompiled := SourceCoreIndexedSession.Recipe.prepare_compiled prepared) (started := started)
      publicStart atCheckpoint publicRun descriptor

include receiver observations extension semantic family namedTerminals namedSupport acceptedPlan wellFormed
  prepared selected history atCheckpoint started inputReceipts metadata sourceAt in
/-- Actual history feeds the public outcome at the current captured state. -/
theorem public_run_failed_reflects
    {returned : SourceCoreExecution.Session publicArtifact} {reason : Word}
    (publicStart : publicSession.start key publicArguments options.inputValidationFuel = .ok publicCheckpoint)
    (publicRun : publicSession.RunAt key publicArguments options (.ok (.failed reason returned)))
    (descriptor : SourceCoreCallableContracts.Descriptor compiled.indexed.ancestry.graph.inputs.callable.table
      (.named header.named.signature.key)) :
    ∃ (actual : SourceCoreIndexedSession.Session nativeArtifact) (value : Value) (finalStore : Store)
        (capture : CallableIndexedOwnedFunctionValues.NamedCapture rootHeaders (rootOwner).key header mapping world)
        (sourceSize : Nat) (outcome : Staging.Recursive.Outcome) (after : Dynamic.Heap)
        (finalMap : LocationMap) (finalWorld : StoreTyping),
        nativeCheckpoint.FailedResultAt options.executionFuel value finalStore reason actual ∧
        returned.IndexedAt actual ∧
        Staging.Recursive.Size.Applies (Program.ofChecked compiled.sourceProgram)
          (RecursiveNamedPreparedStageScopes.registry stagePrepared) sourceSize invocation anchor.function.context before
          (.global function) arguments outcome after ∧
        CallableIndexedOwnedPreparedStagedTerminalNamedInvocationBounds.ResultAt
          (registry := completion.result.context.registry) (payloads := payloads)
          (scope := []) (canonical := SourceCoreCallableIndexedTemplates.globalEnvironment compiled.indexed)
          rootFunctions rootOwner caller header capture anchor.function.context outcome after value finalStore finalMap finalWorld rootFaults := by
  obtain ⟨stable, heaps, heapTyped, represented, argumentsTyped⟩ :=
    current_arguments (inputs := inputs) (rows := rows) (profile := profile)
      (wellFormed := wellFormed) (prepared := prepared) (selected := selected)
      (history := history) (started := started) (inputReceipts := inputReceipts) (metadata := metadata)
  have globalReference := CallableIndexedOwnedPreparedBootstrapGlobalReferences.global_reference rows header selected.member
  have supports := (RecursiveNamedPublicReturnedValues.header_context_supports header anchor wellFormed).2
  exact CallableIndexedOwnedPreparedStagedOrdinarySequenceCallerBounds.public_run_failed_reflects
      (stagePrepared := stagePrepared) (receiver := receiver) (profile := profile)
      (observations := observations) (extension := extension) (semantic := semantic)
      (family := family) (namedTerminals := namedTerminals) (namedSupport := namedSupport)
      (acceptedPlan := acceptedPlan) (wellFormed := wellFormed) (selected := selected)
      (owner := rootOwner) (caller := caller) (globalReference := globalReference) (stable := stable)
      (heapTyped := heapTyped) (argumentsTyped := argumentsTyped) (represented := represented)
      (heaps := heaps) (sourceAt := sourceAt) (supports := supports)
      (sameCompiled := SourceCoreIndexedSession.Recipe.prepare_compiled prepared) (started := started)
      publicStart atCheckpoint publicRun descriptor

include receiver observations extension semantic family namedTerminals namedSupport acceptedPlan wellFormed
  prepared selected history atCheckpoint started inputReceipts metadata sourceAt in
/-- Actual history feeds the public outcome at the current captured state. -/
theorem public_word_preserved
    (outputWord : header.output = .word) (resultWord : header.function.resultType = .word)
    (outputBudget : Nat) (positive : 0 < outputBudget)
    {size : Nat} {word : Word} {after : Dynamic.Heap}
    (trace : Staging.Recursive.Size.Applies (Program.ofChecked compiled.sourceProgram)
      (RecursiveNamedPreparedStageScopes.registry stagePrepared) size invocation anchor.function.context before
      (.global function) arguments (.value (.word word)) after) :
    ∃ (capture : CallableIndexedOwnedFunctionValues.NamedCapture rootHeaders (rootOwner).key header mapping world)
        (finalStore : Store) (finalMap : LocationMap) (finalWorld : StoreTyping) (required : Nat),
        (∀ fuel, required ≤ fuel → ∀ outcome, publicCheckpoint.ResumeAt fuel outputBudget outcome →
          ∃ exported, outcome = .succeeded exported ∧ exported.value = .word word) ∧
        CallableIndexedOwnedPreparedStagedTerminalNamedInvocationBounds.ResultAt
          (registry := completion.result.context.registry) (payloads := payloads)
          (scope := []) (canonical := SourceCoreCallableIndexedTemplates.globalEnvironment compiled.indexed)
          rootFunctions rootOwner caller header capture anchor.function.context (.value (.word word)) after
            (.inRight .word (.word word)) finalStore finalMap finalWorld rootFaults := by
  obtain ⟨stable, heaps, heapTyped, represented, argumentsTyped⟩ :=
    current_arguments (inputs := inputs) (rows := rows) (profile := profile)
      (wellFormed := wellFormed) (prepared := prepared) (selected := selected)
      (history := history) (started := started) (inputReceipts := inputReceipts) (metadata := metadata)
  have globalReference := CallableIndexedOwnedPreparedBootstrapGlobalReferences.global_reference rows header selected.member
  have supports := (RecursiveNamedPublicReturnedValues.header_context_supports header anchor wellFormed).2
  exact CallableIndexedOwnedPreparedStagedOrdinarySequenceCallerBounds.public_word_preserved
      (stagePrepared := stagePrepared) (receiver := receiver) (profile := profile)
      (observations := observations) (extension := extension) (semantic := semantic)
      (family := family) (namedTerminals := namedTerminals) (namedSupport := namedSupport)
      (acceptedPlan := acceptedPlan) (wellFormed := wellFormed) (selected := selected)
      (owner := rootOwner) (caller := caller) (globalReference := globalReference) (stable := stable)
      (heapTyped := heapTyped) (argumentsTyped := argumentsTyped) (represented := represented)
      (heaps := heaps) (sourceAt := sourceAt) (supports := supports)
      (sameCompiled := SourceCoreIndexedSession.Recipe.prepare_compiled prepared) (started := started)
      atCheckpoint outputWord resultWord outputBudget positive trace

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedHistoryPublicBounds
