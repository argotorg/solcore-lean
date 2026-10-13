import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedBodies
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedPhysicalNamedInvocationBounds
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedPhysicalNamedInvocationPreservation
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedTerminalNamedGlobalDispatch
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedOrdinarySequenceCallerBounds

/-! Public boundary adapters for every accepted named body consume physical laws produced by
the numeric family. Actual public starts and outcomes select the same cache,
parameter state and returned store as the original Source application. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedPhysicalBodyPublicInvocationBounds
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
  (packet : CallableIndexedOwnedPreparedStagedNamedBodies.Body header)
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
  obtain ⟨capture⟩ := CallableIndexedOwnedNamedPhysicalCaptures.of_headerAt
    packet.prepared packet.aligned selected.member keyPhysical physical heaps.runtime_hasTypes
  let nativeCapture := capture.named
  obtain ⟨value, finalStore, finalMap, finalWorld, result⟩ :=
    CallableIndexedOwnedPreparedStagedPhysicalNamedInvocationPreservation.preserves_invocation
      (functions := rootFunctions) (registry := completion.result.context.registry)
      (owner := owner) (caller := caller) (header := header) (physicalCapture := capture)
      (scope := []) (canonical := SourceCoreCallableIndexedTemplates.globalEnvironment compiled.indexed)
      (sourceAt := sourceAt)
      packet.layouts physical selected.member wellFormed stable heapTyped argumentsTyped represented heaps
      supports size (fun {child} selected => preservesBodies size selected) trace (Nat.le_refl _)
  have argumentsEvaluated := selected.arguments_evaluate represented store
  have actualReference :
      (payloads.reverse ++ SourceCoreCallableIndexedTemplates.globalEnvironment compiled.indexed)[header.slot + root.types.length]? =
      some (.cellRef (OptionalCell.cellType header.named.signature.functionType) (owner.key.locations header)) := by
    simpa only [selected.argument_length represented, RecursiveGlobalInitializationMeaning.shift] using
      (RecursiveNamedPublicRootMeaning.globals_agree payloads
        (SourceCoreCallableIndexedTemplates.globalEnvironment compiled.indexed) globalReference)
  have read := OptionalCell.read_success Word.zero
    (show Evaluates
      (DataPatternValues.packValues payloads :: payloads.reverse ++
        SourceCoreCallableIndexedTemplates.globalEnvironment compiled.indexed) store
      (.var (header.slot + root.types.length + 1))
      (.cellRef (OptionalCell.cellType header.named.signature.functionType) (owner.key.locations header)) store
      from .var actualReference) capture.read
  have called := SourceCoreCalls.call_success argumentsEvaluated read result.1
  have rootEvaluation : Evaluates
      (payloads.reverse ++ SourceCoreCallableIndexedTemplates.globalEnvironment compiled.indexed)
      store root.body value finalStore := by
    simpa only [selected.shape.2] using called
  obtain ⟨required, run⟩ := evaluation_runStateful_complete_with_sufficient_fuel rootEvaluation
  exact ⟨nativeCapture, value, finalStore, finalMap, finalWorld, required, run, result⟩

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
  obtain ⟨capture⟩ := CallableIndexedOwnedNamedPhysicalCaptures.of_headerAt
    packet.prepared packet.aligned selected.member keyPhysical physical heaps.runtime_hasTypes
  let nativeCapture := capture.named
  have argumentsEvaluated := selected.arguments_evaluate represented store
  have actualReference :
      (payloads.reverse ++ SourceCoreCallableIndexedTemplates.globalEnvironment compiled.indexed)[header.slot + root.types.length]? =
      some (.cellRef (OptionalCell.cellType header.named.signature.functionType) (owner.key.locations header)) := by
    simpa only [selected.argument_length represented, RecursiveGlobalInitializationMeaning.shift] using
      (RecursiveNamedPublicRootMeaning.globals_agree payloads
        (SourceCoreCallableIndexedTemplates.globalEnvironment compiled.indexed) globalReference)
  obtain ⟨size, measured⟩ := evaluation_has_size (runStateful_evaluation_sound completed)
  rw [selected.shape.2] at measured
  obtain ⟨bodySize, smaller, bodyEvaluation⟩ := RecursiveNamedCallBounds.call_body
    argumentsEvaluated actualReference capture.read measured
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, result⟩ :=
    CallableIndexedOwnedPreparedStagedPhysicalNamedInvocationBounds.reflects_invocation
      (functions := rootFunctions) (registry := completion.result.context.registry)
      (owner := owner) (caller := caller) (header := header) (physicalCapture := capture)
      (scope := []) (canonical := SourceCoreCallableIndexedTemplates.globalEnvironment compiled.indexed)
      (prepared := packet.prepared) (aligned := packet.aligned) (stagePrepared := stagePrepared)
      (descriptor := descriptor) (sourceAt := sourceAt)
      packet.layouts physical selected.member wellFormed stable heapTyped argumentsTyped represented heaps
      supports size (fun {child} selected => reflectsBodies size selected) bodyEvaluation (Nat.le_of_lt smaller)
  exact ⟨nativeCapture, sourceSize, outcome, after, finalMap, finalWorld, trace, result⟩

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
  cases sameCompiled
  obtain ⟨actualCheckpoint, accepted, resumed⟩ := publicRun
  have same : actualCheckpoint = publicCheckpoint := Except.ok.inj (accepted.symm.trans publicStart)
  subst actualCheckpoint
  obtain ⟨actual, generation, value, finalStore, completed, exported, valueEq, typeEq, budgetEq, sessionAt⟩ :=
    resumed.indexed_succeeded atCheckpoint
  obtain ⟨capture, sourceSize, outcome, after, finalMap, finalWorld, trace, result⟩ :=
    reflects_root
      (stagePrepared := stagePrepared) (functions := functions)
      (packet := packet) (keyPhysical := keyPhysical) (physical := physical)
      (wellFormed := wellFormed) (selected := selected)
      (owner := owner) (caller := caller) (globalReference := globalReference) (stable := stable)
      (heapTyped := heapTyped) (argumentsTyped := argumentsTyped) (represented := represented)
      (heaps := heaps) (sourceAt := sourceAt) (supports := supports) (reflectsBodies := reflectsBodies) descriptor
      (started.initial.native_done_iff.mp completed)
  exact ⟨actual, generation, value, finalStore, capture, sourceSize, outcome, after, finalMap, finalWorld,
    exported, valueEq, typeEq, budgetEq, sessionAt, trace, result⟩

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
  cases sameCompiled
  obtain ⟨actualCheckpoint, accepted, resumed⟩ := publicRun
  have same : actualCheckpoint = publicCheckpoint := Except.ok.inj (accepted.symm.trans publicStart)
  subst actualCheckpoint
  obtain ⟨actual, _generation, value, finalStore, completed, failed, sessionAt⟩ :=
    resumed.indexed_failed atCheckpoint
  obtain ⟨capture, sourceSize, outcome, after, finalMap, finalWorld, trace, result⟩ :=
    reflects_root
      (stagePrepared := stagePrepared) (functions := functions)
      (packet := packet) (keyPhysical := keyPhysical) (physical := physical)
      (wellFormed := wellFormed) (selected := selected)
      (owner := owner) (caller := caller) (globalReference := globalReference) (stable := stable)
      (heapTyped := heapTyped) (argumentsTyped := argumentsTyped) (represented := represented)
      (heaps := heaps) (sourceAt := sourceAt) (supports := supports) (reflectsBodies := reflectsBodies) descriptor
      (started.initial.native_done_iff.mp completed)
  exact ⟨actual, value, finalStore, capture, sourceSize, outcome, after, finalMap, finalWorld,
    failed, sessionAt, trace, result⟩

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
  cases sameCompiled
  obtain ⟨capture, value, finalStore, finalMap, finalWorld, required, completes, result⟩ :=
    preserves_root
      (stagePrepared := stagePrepared) (functions := functions)
      (packet := packet) (keyPhysical := keyPhysical) (physical := physical)
      (wellFormed := wellFormed) (selected := selected)
      (owner := owner) (caller := caller) (globalReference := globalReference) (stable := stable)
      (heapTyped := heapTyped) (argumentsTyped := argumentsTyped) (represented := represented)
      (heaps := heaps) (sourceAt := sourceAt) (supports := supports) (preservesBodies := preservesBodies) trace
  have represented := result.2.1
  rw [outputWord] at represented
  have nativeWord : value = .inRight .word (.word word) := by
    cases represented with
    | value payload =>
        obtain ⟨actualWord, sourceEq, nativeEq⟩ := CompatiblePlaceModifier.word_fields observations payload
        have same : word = actualWord := Dynamic.Value.word.inj sourceEq
        cases same
        exact congrArg (fun payload => Core.Value.inRight .word payload) nativeEq
  rw [nativeWord] at completes result
  have atRecipe : nativeArtifact.RecipeAt recipe := by
    cases nativeArtifact
    exact started.recipe_eq
  have requested := started.original.result_type_at atRecipe started.selected
  have rootWord := (RecursiveNamedPublicRootSourceSignature.inputs_and_result selected).2.trans resultWord
  rw [rootWord] at requested
  exact ⟨capture, finalStore, finalMap, finalWorld, required,
    fun fuel enough outcome resumed => RecursiveNamedPublicExecutionMeaning.resume_word_succeeded
      atCheckpoint resumed (started.initial.native_done_iff.mpr (completes fuel enough)) requested positive,
    result⟩


end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedPhysicalBodyPublicInvocationBounds
