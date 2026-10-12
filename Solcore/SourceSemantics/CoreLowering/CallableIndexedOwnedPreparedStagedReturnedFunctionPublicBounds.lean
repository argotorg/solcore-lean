import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedBodiesSupport
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedBootstrapGlobalReferences
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicReturnedValues
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicReturnedSessionInputs
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicReturnedArgumentsReceiving
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedOrdinarySequenceCallerBounds

/-! An actual successful public call supplies the closure and the reached
owned state for the next public call. Captured environments, locations, heap
contents and stable histories are retained through export and reimport.
The returned handle may pass through real named/builtin issuance before the
next call. Inputs may repeat this handle inside data containers. Both calls
use the same receiving body model and metadata. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedReturnedFunctionPublicBounds
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
  {previousCheckpoint : SourceCoreIndexedSession.Checkpoint nativeArtifact}
  {previousCompletion : SourceCoreIndexedSession.Completion nativeArtifact}
  {previousFuel outputFuel : Nat} {previousGeneration : SourceCorePublicValues.ExportGeneration}
  {previousValue : Value} {returnedStore : Store}
  (previousSuccess : previousCheckpoint.SucceededResultAt previousFuel outputFuel
    previousGeneration previousValue returnedStore previousCompletion)
  {previousHeader : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)}
  (requested : previousCheckpoint.ResultTypeAt previousHeader.function.resultType)
  {handle : SourceCorePublicValues.Handle}
  (previousHandle : previousCompletion.value = .function handle)
  {nativeSession : SourceCoreIndexedSession.Session nativeArtifact}
  (continued : previousCompletion.session.IssuanceChain nativeSession)
  {previousMap : LocationMap} {previousWorld : StoreTyping} {previousHeap : Dynamic.Heap}
  {previousStore : Store}
  (previousCaller : State (headers rows) (keys compiled)
    ⟨[], previousMap, previousWorld, previousHeap, previousStore,
      SourceCoreCallableIndexedTemplates.globalEnvironment compiled.indexed⟩)
  {previousCapture : CallableIndexedOwnedFunctionValues.NamedCapture (headers rows)
    (owner compiled).key previousHeader previousMap previousWorld}
  {previousPayloads : List Value} {previousOutcome : Staging.Recursive.Outcome}
  {before : Dynamic.Heap} {mapping : LocationMap} {returnedWorld : StoreTyping}
  (previousResult : CallableIndexedOwnedPreparedStagedTerminalNamedInvocationBounds.ResultAt
    (registry := completion.result.context.registry) (payloads := previousPayloads)
    (scope := []) (canonical := SourceCoreCallableIndexedTemplates.globalEnvironment compiled.indexed)
    (CallableIndexedOwnedContextualCellOrigins.functions (headers rows) (keys compiled)
      bodyRegistry semanticFaults profile)
    (owner compiled) previousCaller previousHeader previousCapture previousHeader.function.context
    previousOutcome before previousValue returnedStore mapping returnedWorld
    (CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics))
  {publicArtifact : SourceCoreExecution.Artifact}
  {publicSession : SourceCoreExecution.Session publicArtifact}
  {publicCheckpoint : SourceCoreExecution.Checkpoint publicArtifact}
  {nativeCheckpoint : SourceCoreIndexedSession.Checkpoint nativeArtifact}
  {key : SourceCoreIndexedSession.Key} {options : SourceCoreExecution.RunOptions}
  {publicArguments : List SourceCorePublicValues.Value}
  {arguments : Dynamic.Value → List Dynamic.Value}
  {world : StoreTyping} {store : Store} {payloads : Environment}
  {encodedValues : SourceCoreCompatibleValues.Context}
  (atCheckpoint : publicCheckpoint.IndexedAt nativeCheckpoint)
  (started : RecursiveNamedPublicStartMeaning.StartAt nativeSession key publicArguments
    options.inputValidationFuel nativeCheckpoint recipe
    ((SourceCoreIndexedSession.Recipe.prepare_compiled prepared).symm ▸ root)
    world store payloads encodedValues)
  (inputReceipts : ∀ source, previousOutcome = .value source →
    RecursiveNamedPublicReturnedInputs.Inputs previousHeader.function.resultType (.function handle) source
      header.function.context (header.bindings.map (fun binding => binding.1.scheme.body))
      publicArguments (arguments source))
  (metadata : SourceCoreRawMetadata.Extends encodedValues.registry completion.result.context.registry)
  {rawD : SourceTypedRuntime.RuntimeEvidenceEnvironment} {function : Dynamic.GlobalFunction}
  (sourceAt : CallableIndexedOwnedFunctionValues.NamedSourceAt header rawD function)
  {invocation : Staging.Recursive.Scope} {context : SourceSemantics.Context}
  (supports : Dynamic.TypeContextSupports header.context context)

local notation "rootHeaders" => headers rows
local notation "rootKeys" => keys compiled
local notation "rootOwner" => owner compiled
local notation "rootFunctions" => CallableIndexedOwnedContextualCellOrigins.functions rootHeaders rootKeys bodyRegistry semanticFaults profile
local notation "rootModel" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked completion.result.context.registry rootFunctions
local notation "rootFaults" => CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics

include wellFormed prepared selected previousSuccess requested previousHandle continued previousResult started inputReceipts metadata in
/-- The actual previous result constructs every dynamic premise for the next
call. No initial caller, heap law, capture representation or source-value
admission is supplied independently of that result. -/
private theorem continued_arguments :
    ∃ source, previousOutcome = .value source ∧
      ∃ caller : State rootHeaders rootKeys
        ⟨[], mapping, world, before, store, SourceCoreCallableIndexedTemplates.globalEnvironment compiled.indexed⟩,
      Relates previousCaller caller ∧
      CallableIndexedOwnedIndirectExpressionHeads.StableRows caller ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked completion.result.context.registry
        rootFunctions mapping world before store ∧
      Dynamic.HeapWellTyped header.function.context before ∧
      CallableIndexedParameterMeaning.Arguments rootModel mapping world header.bindings (arguments source) payloads ∧
      Dynamic.ValuesHaveTypes header.function.context before (arguments source) header.types := by
  have sameCompiled := SourceCoreIndexedSession.Recipe.prepare_compiled prepared
  cases sameCompiled
  obtain ⟨payload, decoded, _encoded⟩ := previousSuccess.reimports
  obtain ⟨_sourceType, _nativeAt, imported⟩ :=
    previousSuccess.reimports_function_after requested decoded previousHandle continued
  obtain ⟨source, outcomeEq, represented, heaps, worldEq, caller, related, stable, heapTyped, sourceTyped⟩ :=
    RecursiveNamedPublicReturnedValues.returned_value previousResult decoded
  obtain ⟨currentWorld, currentStore⟩ :=
    RecursiveNamedPublicReturnedSessionInputs.StartAt.after_succeeded previousSuccess continued started
  subst returnedWorld
  subst world
  subst store
  have contexts := RecursiveNamedPublicReturnedValues.header_context_supports previousHeader header wellFormed
  obtain ⟨representedArguments, argumentsTyped⟩ :=
    RecursiveNamedPublicReturnedArgumentsReceiving.StartAt.returned_arguments_receiving
      started _ selected imported rfl represented (.refl _)
      (sourceTyped.transportContext contexts.1) (inputReceipts source outcomeEq) metadata wellFormed
  exact ⟨source, outcomeEq, caller, related, stable, heaps,
    heapTyped.transportContext contexts.1, representedArguments, argumentsTyped⟩

include receiver observations extension semantic family namedTerminals namedSupport acceptedPlan wellFormed
  prepared selected previousSuccess requested previousHandle continued previousResult atCheckpoint started inputReceipts metadata sourceAt supports in
/-- Actual returned-state admission feeds the existing public endpoint. -/
theorem public_run_succeeded_reflects
    {publicCompletion : SourceCoreExecution.Completion publicArtifact}
    (publicStart : publicSession.start key publicArguments options.inputValidationFuel = .ok publicCheckpoint)
    (publicRun : publicSession.RunAt key publicArguments options (.ok (.succeeded publicCompletion)))
    (descriptor : SourceCoreCallableContracts.Descriptor compiled.indexed.ancestry.graph.inputs.callable.table
      (.named header.named.signature.key)) :
    ∃ source, previousOutcome = .value source ∧
      ∃ caller : State rootHeaders rootKeys
        ⟨[], mapping, world, before, store, SourceCoreCallableIndexedTemplates.globalEnvironment compiled.indexed⟩,
      Relates previousCaller caller ∧
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
          (RecursiveNamedPreparedStageScopes.registry stagePrepared) sourceSize invocation context before
          (.global function) (arguments source) outcome after ∧
        CallableIndexedOwnedPreparedStagedTerminalNamedInvocationBounds.ResultAt
          (registry := completion.result.context.registry) (payloads := payloads)
          (scope := []) (canonical := SourceCoreCallableIndexedTemplates.globalEnvironment compiled.indexed)
          rootFunctions rootOwner caller header capture context outcome after value finalStore finalMap finalWorld rootFaults := by
  obtain ⟨source, outcomeEq, caller, related, stable, heaps, heapTyped, represented, argumentsTyped⟩ :=
    continued_arguments (inputs := inputs) (rows := rows)
      (profile := profile) (wellFormed := wellFormed) (prepared := prepared) (selected := selected)
      (previousSuccess := previousSuccess) (requested := requested) (previousHandle := previousHandle)
      (continued := continued) (previousCaller := previousCaller) (previousResult := previousResult)
      (started := started) (inputReceipts := inputReceipts) (metadata := metadata)
  have globalReference := CallableIndexedOwnedPreparedBootstrapGlobalReferences.global_reference rows header selected.member
  refine ⟨source, outcomeEq, caller, related, ?_⟩
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
  prepared selected previousSuccess requested previousHandle continued previousResult atCheckpoint started inputReceipts metadata sourceAt supports in
/-- Actual returned-state admission feeds the existing public endpoint. -/
theorem public_run_failed_reflects
    {returned : SourceCoreExecution.Session publicArtifact} {reason : Word}
    (publicStart : publicSession.start key publicArguments options.inputValidationFuel = .ok publicCheckpoint)
    (publicRun : publicSession.RunAt key publicArguments options (.ok (.failed reason returned)))
    (descriptor : SourceCoreCallableContracts.Descriptor compiled.indexed.ancestry.graph.inputs.callable.table
      (.named header.named.signature.key)) :
    ∃ source, previousOutcome = .value source ∧
      ∃ caller : State rootHeaders rootKeys
        ⟨[], mapping, world, before, store, SourceCoreCallableIndexedTemplates.globalEnvironment compiled.indexed⟩,
      Relates previousCaller caller ∧
      ∃ (actual : SourceCoreIndexedSession.Session nativeArtifact) (value : Value) (finalStore : Store)
        (capture : CallableIndexedOwnedFunctionValues.NamedCapture rootHeaders (rootOwner).key header mapping world)
        (sourceSize : Nat) (outcome : Staging.Recursive.Outcome) (after : Dynamic.Heap)
        (finalMap : LocationMap) (finalWorld : StoreTyping),
        nativeCheckpoint.FailedResultAt options.executionFuel value finalStore reason actual ∧
        returned.IndexedAt actual ∧
        Staging.Recursive.Size.Applies (Program.ofChecked compiled.sourceProgram)
          (RecursiveNamedPreparedStageScopes.registry stagePrepared) sourceSize invocation context before
          (.global function) (arguments source) outcome after ∧
        CallableIndexedOwnedPreparedStagedTerminalNamedInvocationBounds.ResultAt
          (registry := completion.result.context.registry) (payloads := payloads)
          (scope := []) (canonical := SourceCoreCallableIndexedTemplates.globalEnvironment compiled.indexed)
          rootFunctions rootOwner caller header capture context outcome after value finalStore finalMap finalWorld rootFaults := by
  obtain ⟨source, outcomeEq, caller, related, stable, heaps, heapTyped, represented, argumentsTyped⟩ :=
    continued_arguments (inputs := inputs) (rows := rows)
      (profile := profile) (wellFormed := wellFormed) (prepared := prepared) (selected := selected)
      (previousSuccess := previousSuccess) (requested := requested) (previousHandle := previousHandle)
      (continued := continued) (previousCaller := previousCaller) (previousResult := previousResult)
      (started := started) (inputReceipts := inputReceipts) (metadata := metadata)
  have globalReference := CallableIndexedOwnedPreparedBootstrapGlobalReferences.global_reference rows header selected.member
  refine ⟨source, outcomeEq, caller, related, ?_⟩
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
  prepared selected previousSuccess requested previousHandle continued previousResult atCheckpoint started inputReceipts metadata sourceAt supports in
/-- Actual returned-state admission feeds the existing public endpoint. -/
theorem public_word_preserved
    {source : Dynamic.Value} (previousSource : previousOutcome = .value source)
    (outputWord : header.output = .word) (resultWord : header.function.resultType = .word)
    (outputBudget : Nat) (positive : 0 < outputBudget)
    {size : Nat} {word : Word} {after : Dynamic.Heap}
    (trace : Staging.Recursive.Size.Applies (Program.ofChecked compiled.sourceProgram)
      (RecursiveNamedPreparedStageScopes.registry stagePrepared) size invocation context before
      (.global function) (arguments source) (.value (.word word)) after) :
    ∃ caller : State rootHeaders rootKeys
        ⟨[], mapping, world, before, store, SourceCoreCallableIndexedTemplates.globalEnvironment compiled.indexed⟩,
      Relates previousCaller caller ∧
      ∃ (capture : CallableIndexedOwnedFunctionValues.NamedCapture rootHeaders (rootOwner).key header mapping world)
        (finalStore : Store) (finalMap : LocationMap) (finalWorld : StoreTyping) (required : Nat),
        (∀ fuel, required ≤ fuel → ∀ outcome, publicCheckpoint.ResumeAt fuel outputBudget outcome →
          ∃ exported, outcome = .succeeded exported ∧ exported.value = .word word) ∧
        CallableIndexedOwnedPreparedStagedTerminalNamedInvocationBounds.ResultAt
          (registry := completion.result.context.registry) (payloads := payloads)
          (scope := []) (canonical := SourceCoreCallableIndexedTemplates.globalEnvironment compiled.indexed)
          rootFunctions rootOwner caller header capture context (.value (.word word)) after
            (.inRight .word (.word word)) finalStore finalMap finalWorld rootFaults := by
  obtain ⟨actualSource, outcomeEq, caller, related, stable, heaps, heapTyped, represented, argumentsTyped⟩ :=
    continued_arguments (inputs := inputs) (rows := rows)
      (profile := profile) (wellFormed := wellFormed) (prepared := prepared) (selected := selected)
      (previousSuccess := previousSuccess) (requested := requested) (previousHandle := previousHandle)
      (continued := continued) (previousCaller := previousCaller) (previousResult := previousResult)
      (started := started) (inputReceipts := inputReceipts) (metadata := metadata)
  have globalReference := CallableIndexedOwnedPreparedBootstrapGlobalReferences.global_reference rows header selected.member
  have same : actualSource = source := Staging.Recursive.Outcome.value.inj (outcomeEq.symm.trans previousSource)
  subst actualSource
  refine ⟨caller, related, ?_⟩
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

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedReturnedFunctionPublicBounds
