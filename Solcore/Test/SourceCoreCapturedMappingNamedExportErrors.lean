import Solcore.Test.SourceCoreCapturedMappingExportError
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedInitializedExportErrors
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicActualRegistryNamedExportErrors

/-! Initial and following named export errors preserve the actual completed
Source heap. A closure exported between those errors remains callable. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreCapturedMapping
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open RecursiveNamedPublicFunctionHistory (Entry)

structure ObservedNamedExportError {artifact : SourceCoreExecution.Artifact}
    (session : SourceCoreExecution.Session artifact) (key : SourceCoreIndexedSession.Key) where
  checkpoint : SourceCoreExecution.Checkpoint artifact
  started : session.start key [.word seed] zeroOutputOptions.inputValidationFuel = .ok checkpoint
  error : SourceCoreIndexedSession.Error
  returned : SourceCoreExecution.Session artifact
  executed : session.RunAt key [.word seed] zeroOutputOptions (.ok (.exportError error returned))

def observeNamedExportError {artifact : SourceCoreExecution.Artifact}
    (session : SourceCoreExecution.Session artifact) (key : SourceCoreIndexedSession.Key) :
    IO (ObservedNamedExportError session key) := do
  match started : session.start key [.word seed] zeroOutputOptions.inputValidationFuel with
  | .error error => throw (IO.userError (reprStr error))
  | .ok checkpoint =>
    let executed ← session.runWithReceipt key [.word seed] zeroOutputOptions
    match result : executed.val with
    | .error error => throw (IO.userError (reprStr error))
    | .ok (.failed _ _) => throw (IO.userError "named factory failed before export")
    | .ok (.outOfFuel _) => throw (IO.userError "named factory execution exhausted")
    | .ok (.succeeded _) => throw (IO.userError "zero output fuel exported a function")
    | .ok (.exportError error returned) =>
      return ⟨checkpoint, started, error, returned, result ▸ executed.property⟩

structure ObservedInitialNamedExport (fixture : CompiledFixture) (observed : ObservedFactory fixture) where
  artifact : SourceCoreExecution.Artifact
  opened : artifact.CompiledAt fixture.facadeCompiled
  bootstrap : SourceCoreExecution.Bootstrap artifact
  fresh : bootstrap.FreshAt
  authority : bootstrap.ExportAuthorityAt
  session : SourceCoreExecution.Session artifact
  ready : bootstrap.resume 100000 = .ready session
  call : ObservedNamedExportError session observed.row.key

def observeInitialNamedExport (fixture : CompiledFixture) (observed : ObservedFactory fixture) :
    IO (ObservedInitialNamedExport fixture observed) := do
  let opened ← fixture.facadeCompiled.openWithReceipt
  let bootstrap ← opened.val.bootstrapWithExportReceipt
  match ready : bootstrap.val.resume 100000 with
  | .error error => throw (IO.userError (reprStr error))
  | .outOfFuel _ => throw (IO.userError "initial named export bootstrap exhausted")
  | .ready session =>
    let call ← observeNamedExportError session observed.row.key
    return ⟨opened.val, opened.property, bootstrap.val, bootstrap.property.1,
      bootstrap.property.2, session, ready, call⟩

private theorem same_recipe {compiled : SourceCoreExecution.Compiled}
    {first second : SourceCoreIndexedSession.Recipe}
    (left : RecursiveNamedPreparedStageContracts.PublicRecipe compiled first)
    (right : RecursiveNamedPreparedStageContracts.PublicRecipe compiled second) : first = second := by
  cases compiled
  exact Option.some.inj (left.symm.trans right)

theorem initial_named_export_meaning {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    {receiver : ObservedReceiver fixture observed} (support : PublicSupports receiver)
    (stages : ObservedStages fixture observed) (first : ObservedInitialNamedExport fixture observed) :
    ∃ source : Dynamic.Value, ∃ state : RetainedState support first.call.returned [],
      SourceCall support support.actual.header
        (RecursiveStageRegistry.scope stages.sidecar [] support.actual.header.function)
        ⟨[]⟩ [.word seed] (.value source) state.heap ∧ first.call.returned.ExportsReady := by
  obtain ⟨recipe, artifact, session, checkpoint, root, world, store, native, encodedValues,
      opened, prepared, _program, sessionAt, checkpointAt, started⟩ :=
    RecursiveNamedPublicExecutionMeaning.actual_start fixture.accepted first.opened first.call.started
  have same := same_recipe opened.compiled_recipe fixture.issued
  cases same
  obtain ⟨selectedHeader, selected⟩ := started.selection prepared support.complete
  have selectedEq : selectedHeader = support.actual.header := by
    have member := selected.member
    change List.Mem _ _ at member
    rw [support.header_list] at member
    exact List.mem_singleton.mp member
  subst selectedHeader
  have inputs : RecursiveNamedPublicNestedInputs.Inputs support.rows session support.actual.header.function.context
      (support.actual.header.bindings.map (fun binding => binding.1.scheme.body)) [.word seed] [.word seed] := by
    rw [support.actual.input_types]
    exact .cons (.leaf (.data
      ⟨.word seed, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word seed⟩
      ⟨.word seed, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word seed⟩)) .nil
  have sourceAt : CallableIndexedOwnedFunctionValues.NamedSourceAt support.actual.header support.input.prepared.available
      (CallableNamedReversal.global (CallableNamedMetadata.global support.packet.header.named.specialized support.input.prepared.available)) := by
    rw [support.headerEq]
    exact support.packet.sourceAt
  obtain ⟨receiving, contextAt, issued, extended, _diagnostics, caller, actual, generation,
      value, finalStore, capture, sourceSize, source, after, finalMap, finalWorld,
      exported, returnedAt, trace, _result, reached, _related, retained, registry, ready⟩ :=
    CallableIndexedOwnedPreparedStagedInitializedExportErrors.public_run_export_error_seeds
      (inputs := [support.input]) (rows := support.rows) (distinct := by simp)
      (stagePrepared := actualStagePrepared fixture) (receiver := receiver.issued)
      (profile := observed.profile) (bodyRegistry := receiver.completion.result.context.registry)
      (semanticFaults := CallableIndexedOwnedPublicDecodedCallFaults.faults receiver.completion.result.diagnostics)
      (observations := support.observations) (baseRegistry := receiver.registry)
      (semantic := by intro reason token represented; exact represented)
      (family := support.family) (namedTerminals := fun header member =>
        CallableIndexedOwnedPreparedStagedNamedBodies.of_terminal (support.terminals header member))
      (namedSupport := support.supports) (wellFormed := fixture.source_wellFormed)
      (prepared := prepared) (selected := selected) (opened := opened) (fresh := first.fresh)
      (ready := .single first.ready) (authority := first.authority) (atSession := sessionAt)
      (atCheckpoint := checkpointAt) (started := started) (inputReceipts := inputs) (sourceAt := sourceAt)
      (invocation := RecursiveStageRegistry.scope stages.sidecar [] support.actual.header.function)
      first.call.started first.call.executed support.descriptor
  let state : RetainedState support first.call.returned [] := {
    artifact := artifact, session := actual, mapping := finalMap, world := finalWorld,
    heap := after, store := finalStore, caller := reached, atSession := returnedAt,
    atRecipe := started.recipe_eq, receiving := receiving, issued := issued,
    extension := extended, registry := (congrArg (·.registry) contextAt).symm ▸ registry,
    history := retained }
  exact ⟨source, state, ⟨support.input.prepared.available, _, sourceSize, sourceAt, trace⟩,
    returnedAt.exportsReady_iff.mpr ready⟩

theorem next_named_export_meaning {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    {receiver : ObservedReceiver fixture observed} {support : PublicSupports receiver}
    {publicArtifact : SourceCoreExecution.Artifact} {publicSession : SourceCoreExecution.Session publicArtifact}
    {entries : List Entry} (state : RetainedState support publicSession entries)
    (call : ObservedNamedExportError publicSession observed.row.key)
    (exportsReady : publicSession.ExportsReady) (invocation : Staging.Recursive.Scope) :
    ∃ source : Dynamic.Value, ∃ after : RetainedState support call.returned entries,
      SourceCall support support.actual.header invocation state.heap [.word seed] (.value source) after.heap ∧
      call.returned.ExportsReady := by
  have selected : ∀ request : RecursiveNamedPublicHistoryFrontdoor.Started
      (CallableIndexedOwnedPreparedFiniteNamedInventories.headers support.rows) fixture.recipePrepared
      call.checkpoint state.session observed.row.key [.word seed] zeroOutputOptions.inputValidationFuel
      state.world state.store, request.header = support.actual.header := by
    intro request
    have only : ∀ header, header ∈ CallableIndexedOwnedPreparedFiniteNamedInventories.headers support.rows →
        header = support.actual.header := by
      intro header member
      rw [support.header_list] at member
      exact List.mem_singleton.mp member
    exact only _ request.selected.member
  obtain ⟨program, present⟩ := RecursiveNamedPublicHistoryRegistryExtension.diagnostics_present state.history
  have semantic : ∀ reason token,
      CallableIndexedOwnedPublicDecodedCallFaults.faults receiver.completion.result.diagnostics reason token →
      CallableIndexedOwnedPublicDecodedStagedCallFaults.faults state.receiving.result.diagnostics (.semantic reason) token := by
    intro reason token represented
    exact CompatibleRegistryDiagnosticExtension.semantic_preserved fixture.recipe.compiled
      receiver.issued state.issued present state.extension represented
  obtain ⟨request, arguments, inputs, receiving, contextAt, issued, extended, _diagnostics,
      actual, generation, value, finalStore, capture, sourceSize, source, after, finalMap, finalWorld,
      exported, returnedAt, trace, _result, reached, _related, retained, registry, ready⟩ :=
    RecursiveNamedPublicActualRegistryNamedExportErrors.public_run_export_error_retains
      (inputs := [support.input]) (rows := support.rows) (stagePrepared := actualStagePrepared fixture)
      (completion := state.receiving) (receiver := state.issued) (profile := observed.profile)
      (bodyRegistry := receiver.completion.result.context.registry)
      (semanticFaults := CallableIndexedOwnedPublicDecodedCallFaults.faults receiver.completion.result.diagnostics)
      (observations := support.observations) (semantic := semantic)
      (family := support.family) (namedTerminals := fun header member =>
        CallableIndexedOwnedPreparedStagedNamedBodies.of_terminal (support.terminals header member))
      (namedSupport := support.supports) (wellFormed := fixture.source_wellFormed)
      (prepared := fixture.recipePrepared) (complete := support.complete) (history := state.history)
      (atRegistry := state.registry) (atRecipe := state.atRecipe) (atSession := state.atSession)
      (exportsReady := exportsReady) (invocation := invocation)
      (inputsFor := by
        intro request
        refine ⟨[.word seed], ?_⟩
        rw [selected request, support.actual.input_types]
        exact .cons (.data
          ⟨.word seed, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word seed⟩
          ⟨.word seed, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word seed⟩) .nil)
      (descriptors := by intro request; rw [selected request]; exact ⟨support.descriptor⟩)
      call.started call.executed
  have args : arguments = [.word seed] := by
    rw [selected request, support.actual.input_types] at inputs
    cases inputs with
    | cons head tail =>
      cases tail
      generalize rawEq : TypeSystem.Ty.word = raw at head
      generalize publicEq : SourceCorePublicValues.Value.word seed = publicValue at head
      cases head with
      | retained entry member => cases publicEq
      | data typed meaning =>
        subst publicValue
        obtain ⟨data, publicEq, meaning⟩ := meaning
        cases data <;> simp_all [SourceCoreIndexedSession.DataInput.publicValue]
        cases meaning
        rfl
      | product => cases publicEq
      | constructed => cases publicEq
      | mapping => cases publicEq
      | comptime => cases rawEq
  let next : RetainedState support call.returned entries := {
    artifact := state.artifact, session := actual, mapping := finalMap, world := finalWorld,
    heap := after, store := finalStore, caller := reached, atSession := returnedAt,
    atRecipe := state.atRecipe, receiving := receiving, issued := issued,
    extension := state.extension.trans extended,
    registry := (congrArg (·.registry) contextAt).symm ▸ registry, history := retained }
  exact ⟨source, next, ⟨request.rawD, request.function, sourceSize, selected request ▸ request.sourceAt,
    by simpa only [args] using trace⟩, returnedAt.exportsReady_iff.mpr ready⟩

structure ObservedNamedFactoryCall {artifact : SourceCoreExecution.Artifact}
    (session : SourceCoreExecution.Session artifact) (key : SourceCoreIndexedSession.Key) where
  checkpoint : SourceCoreExecution.Checkpoint artifact
  started : session.start key [.word seed] runOptions.inputValidationFuel = .ok checkpoint
  completion : SourceCoreExecution.Completion artifact
  executed : session.RunAt key [.word seed] runOptions (.ok (.succeeded completion))
  handle : SourceCorePublicValues.Handle
  returned : completion.value = .function handle

def observeNamedFactoryCall {artifact : SourceCoreExecution.Artifact}
    (session : SourceCoreExecution.Session artifact) (key : SourceCoreIndexedSession.Key) :
    IO (ObservedNamedFactoryCall session key) := do
  match started : session.start key [.word seed] runOptions.inputValidationFuel with
  | .error error => throw (IO.userError (reprStr error))
  | .ok checkpoint =>
    let executed ← session.runWithReceipt key [.word seed] runOptions
    match result : executed.val with
    | .error error => throw (IO.userError (reprStr error))
    | .ok (.failed _ _) => throw (IO.userError "following factory failed")
    | .ok (.outOfFuel _) => throw (IO.userError "following factory execution exhausted")
    | .ok (.exportError error _) => throw (IO.userError (reprStr error))
    | .ok (.succeeded completion) =>
      match returned : completion.value with
      | .function handle => return ⟨checkpoint, started, completion, result ▸ executed.property, handle, returned⟩
      | _ => throw (IO.userError "following factory did not return a function")

theorem named_factory_meaning {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    {receiver : ObservedReceiver fixture observed} {support : PublicSupports receiver}
    {publicArtifact : SourceCoreExecution.Artifact} {publicSession : SourceCoreExecution.Session publicArtifact}
    {entries : List Entry} (state : RetainedState support publicSession entries)
    (call : ObservedNamedFactoryCall publicSession observed.row.key) (invocation : Staging.Recursive.Scope) :
    ∃ entry : Entry, entry.sourceType = .function (.mapping .word .word) .word ∧ entry.handle = call.handle ∧
      call.handle.sourceType = .function (.mapping .word .word) .word ∧
      ∃ after : RetainedState support call.completion.session (entries ++ [entry]),
        SourceCall support support.actual.header invocation state.heap [.word seed] (.value entry.source) after.heap := by
  obtain ⟨request⟩ := RecursiveNamedPublicHistoryFrontdoor.recover_start
    fixture.recipePrepared [support.input] support.rows support.complete
    state.atRecipe state.history.current.1 state.atSession call.started
  have selected : request.header = support.actual.header := by
    have only : ∀ header, header ∈ CallableIndexedOwnedPreparedFiniteNamedInventories.headers support.rows →
        header = support.actual.header := by
      intro header member
      rw [support.header_list] at member
      exact List.mem_singleton.mp member
    exact only _ request.selected.member
  have inputs : RecursiveNamedPublicFunctionHistoryInputs.Inputs entries request.header.function.context
      (request.header.bindings.map (fun binding => binding.1.scheme.body)) [.word seed] [.word seed] := by
    rw [selected, support.actual.input_types]
    exact .cons (.data
      ⟨.word seed, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word seed⟩
      ⟨.word seed, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word seed⟩) .nil
  have registryAt : request.encodedValues.registry = state.receiving.result.context.registry := by
    apply request.started.simple_registry state.registry
    intro value member
    have same : value = .word seed := List.mem_singleton.mp member
    exact same ▸ SourceCoreIndexedSession.SimplePublic.word seed
  have descriptor : SourceCoreCallableContracts.Descriptor
      fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable.table
      (.named request.header.named.signature.key) := by
    rw [selected]
    exact support.descriptor
  obtain ⟨program, present⟩ := RecursiveNamedPublicHistoryRegistryExtension.diagnostics_present state.history
  have semantic : ∀ reason token,
      CallableIndexedOwnedPublicDecodedCallFaults.faults receiver.completion.result.diagnostics reason token →
      CallableIndexedOwnedPublicDecodedStagedCallFaults.faults state.receiving.result.diagnostics (.semantic reason) token := by
    intro reason token represented
    exact CompatibleRegistryDiagnosticExtension.semantic_preserved fixture.recipe.compiled
      receiver.issued state.issued present state.extension represented
  obtain ⟨actual, generation, nativeValue, finalStore, capture, sourceSize, outcome, heap, mapping, world,
      succeeded, valueEq, _typeEq, _budgetEq, returnedAt, trace, _result,
      caller, source, payload, sourceValue, _nativePayload, _related, continued⟩ :=
    CallableIndexedOwnedPreparedStagedHistoryPublicContinuations.public_run_succeeded_remembers
      (inputs := [support.input]) (rows := support.rows)
      (stagePrepared := actualStagePrepared fixture) (completion := state.receiving) (receiver := state.issued)
      (profile := observed.profile) (bodyRegistry := receiver.completion.result.context.registry)
      (semanticFaults := CallableIndexedOwnedPublicDecodedCallFaults.faults receiver.completion.result.diagnostics)
      (observations := support.observations) (extension := state.receiving.result.extension) (semantic := semantic)
      (family := support.family) (namedTerminals := fun header member =>
        CallableIndexedOwnedPreparedStagedNamedBodies.of_terminal (support.terminals header member))
      (namedSupport := support.supports) (wellFormed := fixture.source_wellFormed)
      (prepared := fixture.recipePrepared) (selected := request.selected) (caller := state.caller)
      (history := state.history) (atCheckpoint := request.atCheckpoint) (started := request.started)
      (invocation := invocation) (inputReceipts := inputs)
      (metadata := by rw [registryAt]; exact .refl _) (sourceAt := request.sourceAt)
      call.started call.executed call.returned descriptor
  let entry : Entry := ⟨request.header.function.resultType, source, call.handle, payload,
    request.header.output, runOptions.outputValidationFuel⟩
  let after : RetainedState support call.completion.session (entries ++ [entry]) := {
    artifact := state.artifact, session := actual.session, mapping := mapping, world := world,
    heap := heap, store := finalStore, caller := caller, atSession := returnedAt, atRecipe := state.atRecipe,
    receiving := state.receiving, issued := state.issued, extension := state.extension,
    registry := registryAt ▸ request.started.returned_registry succeeded, history := continued }
  have atRecipe : state.artifact.RecipeAt fixture.recipe := by
    have convert : ∀ (artifact : SourceCoreIndexedSession.Artifact) (recipe : SourceCoreIndexedSession.Recipe),
        RecursiveNamedPublicStartMeaning.ArtifactRecipe artifact recipe → artifact.RecipeAt recipe :=
      fun artifact _ atRecipe => by cases artifact; exact atRecipe
    exact convert _ _ state.atRecipe
  have requested := request.started.original.result_type_at atRecipe request.started.selected
  have resultType := (RecursiveNamedPublicRootSourceSignature.inputs_and_result request.selected).2
  rw [resultType, selected, support.actual.result_type] at requested
  have handleType := succeeded.function_source_type requested (valueEq.symm.trans call.returned)
  refine ⟨entry, ?_, rfl, handleType, after, request.rawD, request.function, sourceSize, selected ▸ request.sourceAt, ?_⟩
  · change request.header.function.resultType = .function (.mapping .word .word) .word
    rw [selected, support.actual.result_type]
  · simpa only [entry, after, sourceValue] using trace

structure ObservedNamedExportSequence (fixture : CompiledFixture) (observed : ObservedFactory fixture) where
  first : ObservedInitialNamedExport fixture observed
  factory : ObservedNamedFactoryCall first.call.returned observed.row.key
  noOutput : ObservedNamedExportError factory.completion.session observed.row.key
  reused : ObservedInvocation noOutput.returned factory.handle firstArgument
  result : reused.completion.value = .word seed

def observeNamedExportSequence (fixture : CompiledFixture) (observed : ObservedFactory fixture) :
    IO (ObservedNamedExportSequence fixture observed) := do
  let first ← observeInitialNamedExport fixture observed
  let factory ← observeNamedFactoryCall first.call.returned observed.row.key
  let noOutput ← observeNamedExportError factory.completion.session observed.row.key
  let reused ← observeInvocation noOutput.returned factory.handle firstArgument
  if result : reused.completion.value = .word seed then
    return ⟨first, factory, noOutput, reused, result⟩
  else throw (IO.userError "named export error lost earlier closure capture")

/-- All four observations are consumed by one connected Source execution
sequence. The heap after each actual export error is the next call's heap. -/
theorem closed_named_export_sequence_meaning (fixture : CompiledFixture) (observed : ObservedFactory fixture)
    (stages : ObservedStages fixture observed) (sequence : ObservedNamedExportSequence fixture observed) :
    ∃ (receiver : ObservedReceiver fixture observed) (support : PublicSupports receiver),
      let scope := RecursiveStageRegistry.scope stages.sidecar [] support.actual.header.function
      ∃ (firstSource followingSource : Dynamic.Value) (entry : Entry),
        entry.sourceType = .function (.mapping .word .word) .word ∧ entry.handle = sequence.factory.handle ∧
      ∃ first : RetainedState support sequence.first.call.returned [],
      ∃ factory : RetainedState support sequence.factory.completion.session [entry],
      ∃ noOutput : RetainedState support sequence.noOutput.returned [entry],
      ∃ reused : RetainedState support sequence.reused.completion.session [entry],
        SourceCall support support.actual.header scope ⟨[]⟩ [.word seed] (.value firstSource) first.heap ∧
        SourceCall support support.actual.header scope first.heap [.word seed] (.value entry.source) factory.heap ∧
        SourceCall support support.actual.header scope factory.heap [.word seed] (.value followingSource) noOutput.heap ∧
        sequence.first.call.returned.ExportsReady ∧ sequence.noOutput.returned.ExportsReady ∧
        SourceInvocation support scope noOutput.heap entry.source firstArgument (.value (.word seed)) reused.heap := by
  obtain ⟨receiver⟩ := initial_receiver fixture observed
  obtain ⟨support⟩ := static_supports fixture observed stages receiver.completion.result.context.registry receiver.issued
  let scope := RecursiveStageRegistry.scope stages.sidecar [] support.actual.header.function
  obtain ⟨firstSource, first, firstTrace, firstReady⟩ := initial_named_export_meaning support stages sequence.first
  obtain ⟨entry, entryType, handle, handleType, factory, factoryTrace⟩ := named_factory_meaning first sequence.factory scope
  have factoryReady := sequence.factory.executed.exportsReady firstReady
  obtain ⟨followingSource, noOutput, nextTrace, noOutputReady⟩ :=
    next_named_export_meaning factory sequence.noOutput factoryReady scope
  obtain ⟨reused, reusedTrace⟩ := invoke noOutput entry (by simp) entryType handle handleType
    sequence.reused sequence.result scope
  exact ⟨receiver, support, firstSource, followingSource, entry, entryType, handle,
    first, factory, noOutput, reused, firstTrace, factoryTrace, nextTrace, firstReady, noOutputReady, reusedTrace⟩

def runNamedExportErrors : IO Unit := do
  let fixture ← compiledFixture
  let observed ← observeFactory fixture
  let stages ← observeStages fixture observed
  let sequence ← observeNamedExportSequence fixture observed
  have _meaning := closed_named_export_sequence_meaning fixture observed stages sequence
  IO.println "Actual named export errors: initial export error, exported closure, following export error, retained closure returns 10"

end Tests.SourceCoreCapturedMapping
