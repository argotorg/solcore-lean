import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedPhysicalBodyPublicInvocationBounds
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedPhysicalNamedInvocationBounds
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedPhysicalNamedInvocationPreservation
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedTerminalNamedGlobalDispatch
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedOrdinarySequenceCallerBounds

/-! Internal public boundary adapters consume physical body laws produced by
the numeric family. Actual public starts and outcomes select the same cache,
parameter state and returned store as the original Source application. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedPhysicalFunctionPublicInvocationBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState
variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {bodyRegistry : SourceCoreRawMetadata.Registry} {semanticFaults : FunctionCalls.FaultRep}
  (stagePrepared : RecursiveNamedPreparedStageContracts.Prepared compiled
    compiled.indexed.ancestry.graph.inputs.callable)
variable {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
  (functions : FunctionModel compiled.compatible.checked.catalog
    (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {identities : Dynamic.Value → Word → Prop}
  (observations : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog
    (functions) identities)
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  {root : SourceCoreIndexedSession.Root compiled}
  {header : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)}
  (selected : RecursiveNamedPublicRootMeaning.RootSelection
    (values := .initial compiled.compatible.checked)
    (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
    (program := Program.ofChecked compiled.sourceProgram) headers root header)
  (packet : CallableIndexedOwnedPreparedStagedTerminalNamedGlobalDispatch.Terminal header)
  {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store : Store}
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (caller : State headers keys
    ⟨[], mapping, world, before, store, SourceCoreCallableIndexedTemplates.globalEnvironment compiled.indexed⟩)
  (globalReference : (SourceCoreCallableIndexedTemplates.globalEnvironment compiled.indexed)[header.slot]? =
    some (.cellRef (OptionalCell.cellType header.named.signature.functionType) (owner.key.locations header)))
  (keyPhysical : CallableIndexedOwnedNamedPhysicalCaptures.KeyPhysical owner.key headers)
  (physical : CallableIndexedOwnedPhysicalGlobals.Authority compiled mapping store)
  (stable : CallableIndexedOwnedIndirectExpressionHeads.StableRows caller)
  (heapTyped : Dynamic.HeapWellTyped header.function.context before)
  {arguments : List Dynamic.Value} {payloads : List Value}
  (argumentsTyped : Dynamic.ValuesHaveTypes header.function.context before arguments header.types)
  (represented : CallableIndexedParameterMeaning.Arguments
    (CompatibleAmbientHeap.payloadModel compiled.compatible.checked completion.result.context.registry
      (functions))
    mapping world header.bindings arguments payloads)
  (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked completion.result.context.registry
    (functions)
    mapping world before store)
  {rawD : SourceTypedRuntime.RuntimeEvidenceEnvironment} {function : Dynamic.GlobalFunction}
  (sourceAt : CallableIndexedOwnedFunctionValues.NamedSourceAt header rawD function)
  {invocation : Staging.Recursive.Scope} {context : SourceSemantics.Context}
  (supports : Dynamic.TypeContextSupports header.context context)

local notation "rootFunctions" => functions
local notation "rootModel" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked completion.result.context.registry rootFunctions
local notation "rootFaults" => CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics
local notation "rootBridge" => CallableIndexedOwnedBodyRestorationAdmission.bridge (headers := headers) (keys := keys)

variable
  (preservesBodies : ∀ budget {child : Staging.Recursive.Scope},
    (RecursiveNamedPreparedStageScopes.registry stagePrepared).Closure header.function child →
    CallableIndexedOwnedPreparedStagedPhysicalNamedBodyPorts.PreservesBelow
      (headers := headers) (keys := keys) header (CompatibleAmbientHeap.payloadModel compiled.compatible.checked completion.result.context.registry
        (functions))
      (RecursiveNamedPreparedStageScopes.registry stagePrepared) child (CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics) budget)
  (reflectsBodies : ∀ budget {child : Staging.Recursive.Scope},
    (RecursiveNamedPreparedStageScopes.registry stagePrepared).Closure header.function child →
    CallableIndexedOwnedPreparedStagedPhysicalNamedBodyPorts.ReflectsBelow
      (headers := headers) (keys := keys) header (CompatibleAmbientHeap.payloadModel compiled.compatible.checked completion.result.context.registry
        (functions))
      (RecursiveNamedPreparedStageScopes.registry stagePrepared) child (CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics) budget)

include packet keyPhysical physical wellFormed preservesBodies
  selected owner caller globalReference stable heapTyped argumentsTyped represented heaps sourceAt supports in
/-- The actual cached root consumes the mixed numeric family. Ordinary closure
packets come from preparation, and the selected named packet supplies its own
static roots. The exact optional-cell read, parameter entry, body, restoration
and root argument packing are all executed by the existing producers. -/
theorem preserves_root
    {size : Nat} {outcome : Staging.Recursive.Outcome} {after : Dynamic.Heap}
    (trace : Staging.Recursive.Size.Applies (Program.ofChecked compiled.sourceProgram)
      (RecursiveNamedPreparedStageScopes.registry stagePrepared) size invocation context before
      (.global function) arguments outcome after) :
    ∃ capture : CallableIndexedOwnedFunctionValues.NamedCapture headers owner.key header mapping world,
      ∃ value finalStore finalMap finalWorld required,
        (∀ fuel, required ≤ fuel → runStateful fuel
          (.initial root.body
            (payloads.reverse ++ SourceCoreCallableIndexedTemplates.globalEnvironment compiled.indexed) store) =
          .done value finalStore) ∧
        CallableIndexedOwnedPreparedStagedTerminalNamedInvocationBounds.ResultAt
          (registry := completion.result.context.registry) (payloads := payloads)
          (scope := []) (canonical := SourceCoreCallableIndexedTemplates.globalEnvironment compiled.indexed)
          rootFunctions owner caller header capture context outcome after value finalStore finalMap finalWorld rootFaults := by
  exact CallableIndexedOwnedPreparedStagedPhysicalBodyPublicInvocationBounds.preserves_root
    (stagePrepared := stagePrepared)
    (functions := functions)
    (packet := CallableIndexedOwnedPreparedStagedNamedBodies.of_terminal packet)
    (keyPhysical := keyPhysical)
    (physical := physical)
    (wellFormed := wellFormed)
    (selected := selected)
    (owner := owner)
    (caller := caller)
    (globalReference := globalReference)
    (stable := stable)
    (heapTyped := heapTyped)
    (argumentsTyped := argumentsTyped)
    (represented := represented)
    (heaps := heaps)
    (sourceAt := sourceAt)
    (supports := supports)
    (preservesBodies := preservesBodies)
    (trace := trace)

include packet keyPhysical physical wellFormed reflectsBodies
  selected owner caller globalReference stable heapTyped argumentsTyped represented heaps sourceAt supports in
/-- A completed original root exposes its exact cached named body. Numeric
reflection supplies the staged application and actual returned pool; a staged
rejection remains a staged rejection rather than an ordinary Dynamic fault. -/
theorem reflects_root
    (descriptor : SourceCoreCallableContracts.Descriptor compiled.indexed.ancestry.graph.inputs.callable.table
      (.named header.named.signature.key))
    {fuel : Nat} {value : Value} {finalStore : Store}
    (completed : runStateful fuel
      (.initial root.body
        (payloads.reverse ++ SourceCoreCallableIndexedTemplates.globalEnvironment compiled.indexed) store) =
      .done value finalStore) :
    ∃ capture : CallableIndexedOwnedFunctionValues.NamedCapture headers owner.key header mapping world,
      ∃ sourceSize outcome after finalMap finalWorld,
        Staging.Recursive.Size.Applies (Program.ofChecked compiled.sourceProgram)
          (RecursiveNamedPreparedStageScopes.registry stagePrepared) sourceSize invocation context before
          (.global function) arguments outcome after ∧
        CallableIndexedOwnedPreparedStagedTerminalNamedInvocationBounds.ResultAt
          (registry := completion.result.context.registry) (payloads := payloads)
          (scope := []) (canonical := SourceCoreCallableIndexedTemplates.globalEnvironment compiled.indexed)
          rootFunctions owner caller header capture context outcome after value finalStore finalMap finalWorld rootFaults := by
  exact CallableIndexedOwnedPreparedStagedPhysicalBodyPublicInvocationBounds.reflects_root
    (stagePrepared := stagePrepared)
    (functions := functions)
    (packet := CallableIndexedOwnedPreparedStagedNamedBodies.of_terminal packet)
    (keyPhysical := keyPhysical)
    (physical := physical)
    (wellFormed := wellFormed)
    (selected := selected)
    (owner := owner)
    (caller := caller)
    (globalReference := globalReference)
    (stable := stable)
    (heapTyped := heapTyped)
    (argumentsTyped := argumentsTyped)
    (represented := represented)
    (heaps := heaps)
    (sourceAt := sourceAt)
    (supports := supports)
    (reflectsBodies := reflectsBodies)
    (descriptor := descriptor)
    (completed := completed)

variable {recipe : SourceCoreIndexedSession.Recipe} {nativeArtifact : SourceCoreIndexedSession.Artifact}
  {nativeSession : SourceCoreIndexedSession.Session nativeArtifact}
  {nativeCheckpoint : SourceCoreIndexedSession.Checkpoint nativeArtifact}
  {key : SourceCoreIndexedSession.Key} {publicArguments : List SourceCorePublicValues.Value}
  {encodedValues : SourceCoreCompatibleValues.Context} {options : SourceCoreExecution.RunOptions}
  (sameCompiled : recipe.compiled = compiled)
  (started : RecursiveNamedPublicStartMeaning.StartAt nativeSession key publicArguments
    options.inputValidationFuel nativeCheckpoint recipe (sameCompiled.symm ▸ root)
    world store payloads encodedValues)

include packet keyPhysical physical wellFormed reflectsBodies
  selected owner caller globalReference stable heapTyped argumentsTyped represented heaps sourceAt supports
  sameCompiled started in
/-- An actual public success reaches the same cached named body and staged
Source application. Export metadata and the body model's receiving metadata
retain their own actual receipts; no registry equality is invented. -/
theorem public_run_succeeded_reflects
    {publicArtifact : SourceCoreExecution.Artifact}
    {publicSession : SourceCoreExecution.Session publicArtifact}
    {publicCheckpoint : SourceCoreExecution.Checkpoint publicArtifact}
    {publicCompletion : SourceCoreExecution.Completion publicArtifact}
    (publicStart : publicSession.start key publicArguments options.inputValidationFuel = .ok publicCheckpoint)
    (atCheckpoint : publicCheckpoint.IndexedAt nativeCheckpoint)
    (publicRun : publicSession.RunAt key publicArguments options (.ok (.succeeded publicCompletion)))
    (descriptor : SourceCoreCallableContracts.Descriptor compiled.indexed.ancestry.graph.inputs.callable.table
      (.named header.named.signature.key)) :
    ∃ (actual : SourceCoreIndexedSession.Completion nativeArtifact)
      (generation : SourceCorePublicValues.ExportGeneration) (value : Value) (finalStore : Store)
      (capture : CallableIndexedOwnedFunctionValues.NamedCapture headers owner.key header mapping world)
      (sourceSize : Nat) (outcome : Staging.Recursive.Outcome) (after : Dynamic.Heap)
      (finalMap : LocationMap) (finalWorld : StoreTyping),
      nativeCheckpoint.SucceededResultAt options.executionFuel options.outputValidationFuel
        generation value finalStore actual ∧
      publicCompletion.value = actual.value ∧ publicCompletion.sourceType = actual.sourceType ∧
      publicCompletion.boundaryFuel = actual.boundaryFuel ∧ publicCompletion.session.IndexedAt actual.session ∧
      Staging.Recursive.Size.Applies (Program.ofChecked compiled.sourceProgram)
        (RecursiveNamedPreparedStageScopes.registry stagePrepared) sourceSize invocation context before
        (.global function) arguments outcome after ∧
      CallableIndexedOwnedPreparedStagedTerminalNamedInvocationBounds.ResultAt
        (registry := completion.result.context.registry) (payloads := payloads)
        (scope := []) (canonical := SourceCoreCallableIndexedTemplates.globalEnvironment compiled.indexed)
        rootFunctions owner caller header capture context outcome after value finalStore finalMap finalWorld rootFaults := by
  exact CallableIndexedOwnedPreparedStagedPhysicalBodyPublicInvocationBounds.public_run_succeeded_reflects
    (stagePrepared := stagePrepared)
    (functions := functions)
    (packet := CallableIndexedOwnedPreparedStagedNamedBodies.of_terminal packet)
    (keyPhysical := keyPhysical)
    (physical := physical)
    (wellFormed := wellFormed)
    (selected := selected)
    (owner := owner)
    (caller := caller)
    (globalReference := globalReference)
    (stable := stable)
    (heapTyped := heapTyped)
    (argumentsTyped := argumentsTyped)
    (represented := represented)
    (heaps := heaps)
    (sourceAt := sourceAt)
    (supports := supports)
    (reflectsBodies := reflectsBodies)
    (sameCompiled := sameCompiled)
    (started := started)
    (publicStart := publicStart)
    (atCheckpoint := atCheckpoint)
    (publicRun := publicRun)
    (descriptor := descriptor)

include packet keyPhysical physical wellFormed reflectsBodies
  selected owner caller globalReference stable heapTyped argumentsTyped represented heaps sourceAt supports
  sameCompiled started in
/-- Public failure retains the actual staged failure relation. In particular,
a nested stage rejection is not relabeled as a Dynamic semantic fault. -/
theorem public_run_failed_reflects
    {publicArtifact : SourceCoreExecution.Artifact}
    {publicSession : SourceCoreExecution.Session publicArtifact}
    {publicCheckpoint : SourceCoreExecution.Checkpoint publicArtifact}
    {returned : SourceCoreExecution.Session publicArtifact} {reason : Word}
    (publicStart : publicSession.start key publicArguments options.inputValidationFuel = .ok publicCheckpoint)
    (atCheckpoint : publicCheckpoint.IndexedAt nativeCheckpoint)
    (publicRun : publicSession.RunAt key publicArguments options (.ok (.failed reason returned)))
    (descriptor : SourceCoreCallableContracts.Descriptor compiled.indexed.ancestry.graph.inputs.callable.table
      (.named header.named.signature.key)) :
    ∃ (actual : SourceCoreIndexedSession.Session nativeArtifact) (value : Value) (finalStore : Store)
      (capture : CallableIndexedOwnedFunctionValues.NamedCapture headers owner.key header mapping world)
      (sourceSize : Nat) (outcome : Staging.Recursive.Outcome) (after : Dynamic.Heap)
      (finalMap : LocationMap) (finalWorld : StoreTyping),
      nativeCheckpoint.FailedResultAt options.executionFuel value finalStore reason actual ∧
      returned.IndexedAt actual ∧
      Staging.Recursive.Size.Applies (Program.ofChecked compiled.sourceProgram)
        (RecursiveNamedPreparedStageScopes.registry stagePrepared) sourceSize invocation context before
        (.global function) arguments outcome after ∧
      CallableIndexedOwnedPreparedStagedTerminalNamedInvocationBounds.ResultAt
        (registry := completion.result.context.registry) (payloads := payloads)
        (scope := []) (canonical := SourceCoreCallableIndexedTemplates.globalEnvironment compiled.indexed)
        rootFunctions owner caller header capture context outcome after value finalStore finalMap finalWorld rootFaults := by
  exact CallableIndexedOwnedPreparedStagedPhysicalBodyPublicInvocationBounds.public_run_failed_reflects
    (stagePrepared := stagePrepared)
    (functions := functions)
    (packet := CallableIndexedOwnedPreparedStagedNamedBodies.of_terminal packet)
    (keyPhysical := keyPhysical)
    (physical := physical)
    (wellFormed := wellFormed)
    (selected := selected)
    (owner := owner)
    (caller := caller)
    (globalReference := globalReference)
    (stable := stable)
    (heapTyped := heapTyped)
    (argumentsTyped := argumentsTyped)
    (represented := represented)
    (heaps := heaps)
    (sourceAt := sourceAt)
    (supports := supports)
    (reflectsBodies := reflectsBodies)
    (sameCompiled := sameCompiled)
    (started := started)
    (publicStart := publicStart)
    (atCheckpoint := atCheckpoint)
    (publicRun := publicRun)
    (descriptor := descriptor)

include packet keyPhysical physical wellFormed preservesBodies observations
  selected owner caller globalReference stable heapTyped argumentsTyped represented heaps sourceAt supports
  sameCompiled started in
/-- A staged Source Word result is preserved by the same public checkpoint
at sufficient native fuel. The actual export budget remains independent of
the input budget and the staged trace is retained unchanged. -/
theorem public_word_preserved
    {publicArtifact : SourceCoreExecution.Artifact}
    {publicCheckpoint : SourceCoreExecution.Checkpoint publicArtifact}
    (atCheckpoint : publicCheckpoint.IndexedAt nativeCheckpoint)
    (outputWord : header.output = .word) (resultWord : header.function.resultType = .word)
    (outputBudget : Nat) (positive : 0 < outputBudget)
    {size : Nat} {word : Word} {after : Dynamic.Heap}
    (trace : Staging.Recursive.Size.Applies (Program.ofChecked compiled.sourceProgram)
      (RecursiveNamedPreparedStageScopes.registry stagePrepared) size invocation context before
      (.global function) arguments (.value (.word word)) after) :
    ∃ (capture : CallableIndexedOwnedFunctionValues.NamedCapture headers owner.key header mapping world)
      (finalStore : Store) (finalMap : LocationMap) (finalWorld : StoreTyping) (required : Nat),
      (∀ fuel, required ≤ fuel → ∀ outcome, publicCheckpoint.ResumeAt fuel outputBudget outcome →
        ∃ exported, outcome = .succeeded exported ∧ exported.value = .word word) ∧
      CallableIndexedOwnedPreparedStagedTerminalNamedInvocationBounds.ResultAt
        (registry := completion.result.context.registry) (payloads := payloads)
        (scope := []) (canonical := SourceCoreCallableIndexedTemplates.globalEnvironment compiled.indexed)
        rootFunctions owner caller header capture context (.value (.word word)) after
          (.inRight .word (.word word)) finalStore finalMap finalWorld rootFaults := by
  exact CallableIndexedOwnedPreparedStagedPhysicalBodyPublicInvocationBounds.public_word_preserved
    (stagePrepared := stagePrepared)
    (functions := functions)
    (packet := CallableIndexedOwnedPreparedStagedNamedBodies.of_terminal packet)
    (keyPhysical := keyPhysical)
    (physical := physical)
    (wellFormed := wellFormed)
    (selected := selected)
    (owner := owner)
    (caller := caller)
    (globalReference := globalReference)
    (stable := stable)
    (heapTyped := heapTyped)
    (argumentsTyped := argumentsTyped)
    (represented := represented)
    (heaps := heaps)
    (sourceAt := sourceAt)
    (supports := supports)
    (preservesBodies := preservesBodies)
    (sameCompiled := sameCompiled)
    (started := started)
    (observations := observations)
    (atCheckpoint := atCheckpoint)
    (outputWord := outputWord)
    (resultWord := resultWord)
    (outputBudget := outputBudget)
    (positive := positive)
    (trace := trace)

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedPhysicalFunctionPublicInvocationBounds
