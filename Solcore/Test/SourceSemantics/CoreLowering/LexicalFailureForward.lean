import Solcore.Test.SourceSemantics.CoreLowering.Direct.Calls
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.InitializedPublicBounds
import Solcore.Test.SourceSemantics.CoreLowering.LexicalFailure
import Solcore.SourceSemantics.CoreLowering.PublicOutputs
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.PublicActualRegistry
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.PublicInputRegistries

/-!
# Lexical failure forward tests

Forward simulation of lexical failures: seeds, steps and public execution from initial locals, and
selected source-first runs. They stay apart because `Selected/Faulting` opens the initial failure namespace
and must not see its public names.
-/

section
-- leanmerge: from Solcore.Test.SourceCoreInitialFunctionForward
/-! The genuine bootstrap authority receipt also closes the first factory's
Source-to-public direction. No native completion or export-success premise is
needed by the sufficient-fuel endpoint. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreInitialFunctionForward
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open Tests.SourceCoreCapturedReuse
open RecursiveNamedPublicFunctionHistory (Entry)

/-- Every sufficiently fueled resume uses the original first-call checkpoint.
Its newly exported closure carries the same independently established capture
and heap into a reusable singleton history. -/
def ForwardFunctionAt {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed} (support : PublicSupports receiver)
    (first : ObservedPublicRun fixture observed.makeRow) (source : Dynamic.Value) (after : Dynamic.Heap) : Prop :=
  ∃ required,
    ∀ executionFuel outputFuel (outcome : SourceCoreExecution.Outcome first.artifact),
      required ≤ executionFuel → 1 ≤ outputFuel →
      first.checkpoint.ResumeAt executionFuel outputFuel outcome →
      ∃ (completion : SourceCoreExecution.Completion first.artifact) (exported : Entry),
        outcome = .succeeded completion ∧ completion.value = .function exported.handle ∧
        exported.sourceType = .function .unit .word ∧ exported.source = source ∧
        completion.session.ExportsReady ∧
        ∃ state : RetainedState support completion.session [exported], state.heap = after

private theorem forward_initial {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed} {support : PublicSupports receiver}
    (extra : ObservedMake fixture observed)
    (first : ObservedPublicRun fixture observed.makeRow)
    (authority : first.bootstrap.ExportAuthorityAt)
    {invocation : Staging.Recursive.Scope} {source : Dynamic.Value} {after : Dynamic.Heap}
    (trace : SourceCall support support.makeHeader.header invocation ⟨[]⟩ [.word seed] (.value source) after) :
    ForwardFunctionAt support first source after := by
  obtain ⟨artifact, session, checkpoint, root, world, store, native, encodedValues,
      opened, prepared, sessionAt, checkpointAt, started⟩ :=
    fixture.actual_start first.opened first.started
  have ready : first.bootstrap.ReadyAt 100000 first.session := .single first.ready
  obtain ⟨_bootstrap, initialized, _value, _initialStore, _atBootstrap, initial,
      initializedAt, _done, booted⟩ := ready.indexed opened first.fresh
  have same : initialized = session := initializedAt.unique sessionAt
  subst initialized
  have startupRegistry : encodedValues.registry = fixture.recipe.compiled.compatible.checked.staticRegistry := by
    apply started.simple_registry (booted.registry_at initial)
    intro value member
    have same : value = .word seed := List.mem_singleton.mp member
    exact same ▸ SourceCoreIndexedSession.SimplePublic.word seed
  obtain ⟨selectedHeader, selected⟩ := started.selection prepared support.complete
  have selectedEq : selectedHeader = support.makeHeader.header := by
    apply selected_make_root (fixture := fixture) (observed := observed)
      support.makeHeader support.readHeader (root := root) (header := selectedHeader)
    · exact support.header_list ▸ selected
    · exact of_decide_eq_true (List.find?_some (p := fun candidate : SourceCoreIndexedSession.Root fixture.recipe.compiled =>
        decide (candidate.key = observed.makeRow.row.key)) started.selected)
  subst selectedHeader
  have inputs : RecursiveNamedPublicNestedInputs.Inputs support.rows session support.makeHeader.header.function.context
      (support.makeHeader.header.bindings.map (fun binding => binding.1.scheme.body)) [.word seed] [.word seed] := by
    rw [support.makeHeader.make_input_types extra]
    exact .cons (.leaf (.data ⟨.word seed, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word seed⟩
      ⟨.word seed, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word seed⟩)) .nil
  have metadata : SourceCoreRawMetadata.Extends encodedValues.registry receiver.completion.result.context.registry := by
    rw [startupRegistry]
    exact receiver.completion.result.extension
  obtain ⟨rawD, function, sourceSize, sourceAt, trace⟩ := trace
  obtain ⟨caller, capture, payload, finalStore, finalMap, finalWorld, required,
      _nativeEnough, _fullResult, publicEnough⟩ :=
    CallableIndexedOwnedPreparedStagedInitializedFunctionPreservation.public_resume_has_sufficient_fuel
      (inputs := [support.makeInput, support.readInput]) (rows := support.rows) (distinct := support.distinct)
      (stagePrepared := actualStagePrepared fixture)
      (completion := CallableIndexedOwnedPublicFaultReceivers.Receiver.of_completion receiver.completion)
      (receiver := CallableIndexedOwnedPublicFaultReceiverTables.issued_of_runSource receiver.executed)
      (profile := observed.profile) (bodyRegistry := receiver.completion.result.context.registry)
      (semanticFaults := CallableIndexedOwnedPublicDecodedCallFaults.faults receiver.completion.result.diagnostics)
      (observations := support.observations) (extension := receiver.completion.result.extension)
      (semantic := by intro reason token represented; exact represented)
      (family := support.family) (namedTerminals := fun header member =>
        CallableIndexedOwnedPreparedStagedNamedBodies.of_terminal (support.terminals header member)) (namedSupport := support.supports)
      (wellFormed := fixture.source_wellFormed) (prepared := prepared) (selected := selected)
      (opened := opened) (fresh := first.fresh) (ready := ready) (authority := authority)
      (atSession := sessionAt) (atCheckpoint := checkpointAt) (started := started)
      (inputReceipts := inputs) (metadata := metadata) (sourceAt := sourceAt)
      support.makeHeader.make_result_type trace
  refine ⟨required, ?_⟩
  intro executionFuel outputFuel outcome enough positive resumed
  obtain ⟨publicCompletion, actual, _generation, handle, reached, outcomeEq, handleValue, _handleType,
      _succeeded, indexedAt, _related, history, returnedRegistry, returnedReady⟩ :=
    publicEnough executionFuel outputFuel outcome enough positive resumed
  rw [startupRegistry] at returnedRegistry
  let exported : Entry := ⟨support.makeHeader.header.function.resultType, source, handle,
    payload, support.makeHeader.header.output, outputFuel⟩
  exact ⟨publicCompletion, exported, outcomeEq, handleValue, support.makeHeader.make_result_type, rfl,
    indexedAt.2.2.2.exportsReady_iff.mpr returnedReady,
    ⟨artifact, actual.session, finalMap, finalWorld, after, finalStore, reached, indexedAt.2.2.2,
      started.recipe_eq, returnedRegistry, history⟩, rfl⟩

/-- The actual compiler and public events establish both factory traces. The
first and later named factories now each supply a forward export guarantee. -/
theorem sequence_forward_meaning (fixture : CompiledFixture) (observed : ObservedProgram fixture)
    (extra : ObservedMake fixture observed)
    (makeStages : ObservedStages fixture observed.makeRow)
    (readStages : ObservedStages fixture observed.readRow)
    (observedSequence : Tests.SourceCoreDirectFunctionForward.ObservedForwardSequence fixture observed)
    (receiver : ObservedReceiver fixture observed) :
    Tests.SourceCoreDirectOutput.SequenceMeaning makeStages observedSequence.sequence receiver ∧
    (∃ (support : PublicSupports receiver) (first named : Entry),
      Tests.SourceCoreDirectFunctionForward.ForwardFunctionAt support
        observedSequence.sequence.named.completion.session [first, named] observedSequence.sequence.named.handle) ∧
    ∃ (support : PublicSupports receiver) (entry : Entry)
      (state : RetainedState support observedSequence.sequence.first.completion.session [entry]),
      ForwardFunctionAt support observedSequence.sequence.first entry.source state.heap := by
  obtain ⟨meaning, later⟩ := Tests.SourceCoreDirectFunctionForward.sequence_forward_meaning
    fixture observed extra makeStages readStages observedSequence receiver
  refine ⟨meaning, later, ?_⟩
  obtain ⟨support, first, named, second, _firstType, _namedType, _secondType,
    _firstHandle, _namedHandle, _secondHandle, _distinct, _namedSource,
    firstState, _namedState, _secondState, _firstInvoked, _secondInvoked, _finalState,
    _heapEq, firstTrace, _rest⟩ := meaning
  exact ⟨support, first, firstState,
    forward_initial extra observedSequence.sequence.first observedSequence.authority firstTrace⟩

def run : IO Unit := do
  let fixture ← compiledFixture
  let observed ← observeProgram fixture
  let extra ← observeMake fixture observed
  let makeStages ← observeStages fixture observed.makeRow
  let readStages ← observeStages fixture observed.readRow
  let sequence ← Tests.SourceCoreDirectFunctionForward.observeForwardSequence fixture observed
  let receiver ← observeReceiver fixture observed
  have _meaning := sequence_forward_meaning fixture observed extra makeStages readStages sequence receiver
  IO.println "Initial and direct Source factories: sufficient public function export fuel and reusable captured histories, with 10/20/10 reuse"

end Tests.SourceCoreInitialFunctionForward
end

section
-- leanmerge: from Solcore.Test.SourceCoreSelectedLexicalSourceFirst
/-! Independent ordinary traces drive the closed public compiler theorem for
the original lexical program. Initialization is observed before execution. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreSelectedLexicalSourceFirst
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open Tests.SourceCoreInitialLexicalFailure
open Tests.SourceCoreSelectedLexicalOrdinaryTraces
open Tests.SourceCoreSelectedLexicalSourceStart
open SelectedCompilationCertifiedPublicSession (Profiled Initial)
open RecursiveNamedPublicPhysicalSessionState (PlainValue PlainFault SourceCall)

variable {fixture : CompiledFixture} {observed : ObservedProgram fixture}

structure ScalarConclusion (issued : Profiled fixture.recipe)
    (started : Started fixture observed.identityRow.row.key [.word seed]) where
  initial : Initial issued.toIssued started.call
  actual : ActualHeader fixture observed.identityRow.row
  headerEq : actual.header = initial.header
  invocation : Staging.Recursive.Scope
  plain : PlainValue initial.header initial.header invocation ⟨[]⟩ [.word seed] (.word seed)
    (appendWord ⟨[]⟩ (some (.word seed)))
  forward :
    (SourceCall initial.header initial.header invocation ⟨[]⟩ [.word seed] (.value (.word seed))
      (appendWord ⟨[]⟩ (some (.word seed))) ∧
      SelectedCompilationPublicSessionScalarForward.ForwardAt (entries := []) issued.catalog.rows
        initial.header issued.initial issued.support.profile fixture.recipe (.word seed) started.call
        (appendWord ⟨[]⟩ (some (.word seed)))) ∨
    SelectedCompilationStageClosedInitialForward.StageStopped issued started.call initial invocation [.word seed]

structure FaultConclusion (issued : Profiled fixture.recipe)
    (started : Started fixture observed.failedRow.row.key []) where
  initial : Initial issued.toIssued started.call
  actual : ActualHeader fixture observed.failedRow.row
  headerEq : actual.header = initial.header
  invocation : Staging.Recursive.Scope
  plain : PlainFault initial.header initial.header invocation ⟨[]⟩ []
    (.uninitializedLocation (nextLocation ⟨[]⟩)) (appendWord ⟨[]⟩ none)
  forward :
    (SourceCall initial.header initial.header invocation ⟨[]⟩ []
      (.fault (.semantic (.uninitializedLocation (nextLocation ⟨[]⟩)))) (appendWord ⟨[]⟩ none) ∧
      SelectedCompilationPublicSessionFailureForward.FailureForwardAt (entries := []) issued.catalog.rows
        initial.header issued.initial issued.support.profile fixture.recipe
        (.semantic (.uninitializedLocation (nextLocation ⟨[]⟩))) started.call (appendWord ⟨[]⟩ none)) ∨
    SelectedCompilationStageClosedInitialForward.StageStopped issued started.call initial invocation []

theorem scalar_from_source
    (profile : CompilerProgramStaticProfile.StaticProfile fixture.recipe.compiled)
    (stages : ObservedStages fixture observed.identityRow)
    (started : Started fixture observed.identityRow.row.key [.word seed]) :
    ∃ issued : Profiled fixture.recipe, Nonempty (ScalarConclusion issued started) := by
  obtain ⟨issued, initial, actual, actualEq⟩ := initial profile observed.identityRow started
  let invocation := RecursiveStageRegistry.scope stages.sidecar [] initial.header.function
  obtain ⟨rawD, function, sourceAt⟩ :=
    (CallableIndexedOwnedPreparedFiniteNamedInventories.source_receipts issued.catalog.rows).receipts
      initial.header initial.start.selected.member
  have plain : PlainValue initial.header initial.header invocation ⟨[]⟩ [.word seed] (.word seed)
      (appendWord ⟨[]⟩ (some (.word seed))) := by
    have trace := Tests.SourceCoreSelectedLexicalOrdinaryTraces.ActualHeader.identity_plain actual (actualEq.symm ▸ sourceAt) initial.header invocation ⟨[]⟩ seed
    simpa only [actualEq] using trace
  have simple : ∀ value ∈ ([.word seed] : List SourceCorePublicValues.Value),
      SourceCoreIndexedSession.SimplePublic value := by
    intro value member
    cases List.mem_singleton.mp member
    exact .word seed
  have inputTypes : RecursiveNamedPublicDataArgumentReceipts.PublicDataTypes
      initial.header.function.context [.word seed] initial.header.types := by
    rw [← actualEq, identity_types actual]
    exact .cons ⟨.word seed, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word seed⟩ .nil
  have meanings : RecursiveNamedPublicDataInputs.Meanings [.word seed] [.word seed] := .cons ⟨.word seed, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word seed⟩ .nil
  have raw : initial.header.function.resultType = .word := by rw [← actualEq]; exact identity_result actual
  have native : initial.header.output = .word := by rw [← actualEq]; exact identity_output actual
  exact ⟨issued, ⟨⟨initial, actual, actualEq, invocation, plain,
    SelectedCompilationStageClosedInitialForward.scalar issued started.call initial simple inputTypes meanings
      (.word seed) raw native plain⟩⟩⟩

theorem fault_from_source
    (profile : CompilerProgramStaticProfile.StaticProfile fixture.recipe.compiled)
    (stages : ObservedStages fixture observed.failedRow)
    (started : Started fixture observed.failedRow.row.key []) :
    ∃ issued : Profiled fixture.recipe, Nonempty (FaultConclusion issued started) := by
  obtain ⟨issued, initial, actual, actualEq⟩ := initial profile observed.failedRow started
  let invocation := RecursiveStageRegistry.scope stages.sidecar [] initial.header.function
  obtain ⟨rawD, function, sourceAt⟩ :=
    (CallableIndexedOwnedPreparedFiniteNamedInventories.source_receipts issued.catalog.rows).receipts
      initial.header initial.start.selected.member
  have plain : PlainFault initial.header initial.header invocation ⟨[]⟩ []
      (.uninitializedLocation (nextLocation ⟨[]⟩)) (appendWord ⟨[]⟩ none) := by
    have trace := Tests.SourceCoreSelectedLexicalOrdinaryTraces.ActualHeader.failed_plain actual (actualEq.symm ▸ sourceAt) initial.header invocation ⟨[]⟩
    simpa only [actualEq] using trace
  have simple : ∀ value ∈ ([] : List SourceCorePublicValues.Value),
      SourceCoreIndexedSession.SimplePublic value := by intro value member; cases member
  have inputTypes : RecursiveNamedPublicDataArgumentReceipts.PublicDataTypes
      initial.header.function.context [] initial.header.types := by
    rw [← actualEq, failed_types actual]
    exact .nil
  exact ⟨issued, ⟨⟨initial, actual, actualEq, invocation, plain,
    SelectedCompilationStageClosedInitialForward.fault issued started.call initial simple inputTypes .nil
      (.uninitializedLocation (nextLocation ⟨[]⟩)) plain⟩⟩⟩

end Tests.SourceCoreSelectedLexicalSourceFirst
end

section
-- leanmerge: from Solcore.Test.SourceCoreInitialLexicalFailureCommon
/-! Concrete receiving diagnostics and retained state for the actual public
sequence. These records are constructed by public execution proofs. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreInitialLexicalFailure
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedFiniteNamedInventories (headers)
open CallableIndexedOwnedPreparedBootstrapRootState (keys)
open RecursiveNamedPublicFunctionHistory (Entry)

abbrev PublicSupports {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (receiver : ObservedReceiver fixture observed) :=
  StaticSupportPackage fixture observed receiver.completion.result.context.registry receiver.completion

def PublicSupports.functions {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed} (support : PublicSupports receiver) :=
  CallableIndexedOwnedContextualCellOrigins.functions (headers support.rows)
    (keys fixture.recipe.compiled) receiver.completion.result.context.registry
    (CallableIndexedOwnedPublicDecodedCallFaults.faults receiver.completion.result.diagnostics) observed.profile

theorem PublicSupports.observations {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed} (support : PublicSupports receiver) :
    CompatibleEquality.FunctionObservations fixture.recipe.compiled.compatible.checked.catalog
      support.functions (CallableIndexedLambdaValues.Identity fixture.recipe.compiled.indexed) := by
  intro metadata mapping world sourceType source native type origin
  exact CallableIndexedOwnedGeneralLambdaValues.observations _ receiver.completion.result.context.registry
    (CallableIndexedOwnedPublicDecodedCallFaults.faults receiver.completion.result.diagnostics)
    observed.profile (registry := metadata)
    (CallableIndexedOwnedContextualCellOrigins.functions_include_general observed.profile origin)

structure RetainedState {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed} (support : PublicSupports receiver)
    {publicArtifact : SourceCoreExecution.Artifact} (publicSession : SourceCoreExecution.Session publicArtifact)
    (entries : List Entry) where
  artifact : SourceCoreIndexedSession.Artifact
  session : SourceCoreIndexedSession.Session artifact
  mapping : GeneralHeap.LocationMap
  world : Core.StoreTyping
  heap : Dynamic.Heap
  store : Core.Store
  caller : RecursiveNamedPublicFunctionHistory.Caller (headers support.rows)
    (keys fixture.recipe.compiled) mapping world heap store
  atSession : publicSession.IndexedAt session
  atRecipe : RecursiveNamedPublicStartMeaning.ArtifactRecipe artifact fixture.recipe
  registry : session.RegistryAt fixture.recipe.compiled.compatible.checked.staticRegistry
  history : RecursiveNamedPublicFunctionHistory.History (headers support.rows)
    (keys fixture.recipe.compiled) support.functions receiver.completion.result.context.registry
    support.failedHeader.header session mapping world heap store caller entries

def SourceCall {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed} (support : PublicSupports receiver)
    (header : CallableIndexedOwnedFunctionValues.Header fixture.recipe.compiled
      (Program.ofChecked fixture.recipe.compiled.sourceProgram))
    (invocation : Staging.Recursive.Scope) (before : Dynamic.Heap) (arguments : List Dynamic.Value)
    (outcome : Staging.Recursive.Outcome) (after : Dynamic.Heap) : Prop :=
  ∃ rawD function size,
    CallableIndexedOwnedFunctionValues.NamedSourceAt header rawD function ∧
    Staging.Recursive.Size.Applies (Program.ofChecked fixture.recipe.compiled.sourceProgram)
      (RecursiveNamedPreparedStageScopes.registry (actualStagePrepared fixture)) size invocation
      support.failedHeader.header.function.context before (.global function) arguments outcome after

end Tests.SourceCoreInitialLexicalFailure
end

section
-- leanmerge: from Solcore.Test.SourceCoreInitialLexicalFailureSeed
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreInitialLexicalFailure
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedFiniteNamedInventories (headers)

theorem first_meaning {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed}
    (support : PublicSupports receiver)
    (stages : ObservedStages fixture observed.failedRow)
    (first : ObservedPublicRun fixture observed) :
    ∃ state : RetainedState support first.returned [],
      ∃ failure : Staging.Recursive.Failure,
        SourceCall support support.failedHeader.header
          (RecursiveStageRegistry.scope stages.sidecar [] support.failedHeader.header.function)
          ⟨[]⟩ [] (.fault failure) state.heap := by
  obtain ⟨artifact, session, checkpoint, root, world, store, native, encodedValues,
      opened, prepared, sessionAt, checkpointAt, started⟩ := first.start_receipt
  have startupRegistry := first.metadata_at_start opened sessionAt started
  obtain ⟨selectedHeader, selected⟩ := started.selection prepared support.complete
  have selectedEq : selectedHeader = support.failedHeader.header := by
    apply selected_failed_root support.failedHeader support.identityHeader (root := root)
      (support.header_list ▸ selected)
    exact of_decide_eq_true (List.find?_some
      (p := fun root : SourceCoreIndexedSession.Root fixture.recipe.compiled => decide (root.key = observed.failedRow.row.key)) started.selected)
  subst selectedHeader
  have inputs : RecursiveNamedPublicNestedInputs.Inputs support.rows session support.failedHeader.header.function.context
      (support.failedHeader.header.bindings.map (fun binding => binding.1.scheme.body)) [] [] := by
    rw [support.failedHeader.failed_inputs]
    exact .nil
  have metadata : SourceCoreRawMetadata.Extends encodedValues.registry receiver.completion.result.context.registry := by
    rw [startupRegistry]
    exact receiver.completion.result.extension
  have sourceAt : CallableIndexedOwnedFunctionValues.NamedSourceAt support.failedHeader.header support.failedInput.prepared.available
      (CallableNamedReversal.global (CallableNamedMetadata.global support.failedPacket.header.named.specialized support.failedInput.prepared.available)) := by
    rw [support.failedEq]
    exact support.failedPacket.sourceAt
  obtain ⟨caller, returnedSession, value, finalStore, capture, sourceSize, failure, after,
      finalMap, finalWorld, failed, returnedAt, trace, _fullResult, returnedCaller, _related, retained⟩ :=
    CallableIndexedOwnedPreparedStagedInitializedHistoryFailures.public_run_failed_seeds
      (inputs := [support.failedInput, support.identityInput]) (rows := support.rows) (distinct := support.distinct)
      (stagePrepared := actualStagePrepared fixture)
      (completion := CallableIndexedOwnedPublicFaultReceivers.Receiver.of_completion receiver.completion)
      (receiver := CallableIndexedOwnedPublicFaultReceiverTables.issued_of_runSource receiver.executed)
      (profile := observed.profile) (bodyRegistry := receiver.completion.result.context.registry)
      (semanticFaults := CallableIndexedOwnedPublicDecodedCallFaults.faults receiver.completion.result.diagnostics)
      (observations := support.observations) (extension := receiver.completion.result.extension)
      (semantic := by intro reason token represented; exact represented)
      (family := support.family) (namedTerminals := support.terminals) (namedSupport := support.supports)
      (wellFormed := fixture.source_wellFormed) (prepared := prepared) (selected := selected)
      (opened := opened) (fresh := first.fresh) (ready := .single first.ready)
      (sameRuntime := SourceCoreExecution.Session.SameRuntime.refl first.session) (atSession := sessionAt)
      (atCheckpoint := checkpointAt) (started := started) (inputReceipts := inputs)
      (metadata := metadata) (sourceAt := sourceAt)
      (invocation := RecursiveStageRegistry.scope stages.sidecar [] support.failedHeader.header.function)
      first.started first.executed support.failedDescriptor
  have returnedRegistry : returnedSession.RegistryAt encodedValues.registry := by
    have values := failed.2.2.2.2.1.trans started.values
    cases checkpoint
    exact congrArg SourceCoreCompatibleValues.Context.registry values
  rw [startupRegistry] at returnedRegistry
  let state : RetainedState support first.returned [] := {
    artifact := artifact, session := returnedSession, mapping := finalMap, world := finalWorld
    heap := after, store := finalStore, caller := returnedCaller
    atSession := returnedAt, atRecipe := started.recipe_eq, registry := returnedRegistry, history := retained }
  exact ⟨state, failure, support.failedInput.prepared.available, _, sourceSize, sourceAt, trace⟩

end Tests.SourceCoreInitialLexicalFailure
end

section
-- leanmerge: from Solcore.Test.SourceCoreInitialLexicalFailureStep
/-! The actual session returned by the first failed call runs identity(37).
The genuine public result identifies the Source result and retains the same
history at the new session, Source heap and native store. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreInitialLexicalFailure
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedFiniteNamedInventories (headers)
open CallableIndexedOwnedPreparedBootstrapRootState (keys)
open RecursiveNamedPublicFunctionHistory (Entry)

theorem RetainedState.identity {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed} {support : PublicSupports receiver}
    {first : ObservedPublicRun fixture observed}
    (state : RetainedState support first.returned [])
    (call : ObservedContinuation first)
    (invocation : Staging.Recursive.Scope) :
    ∃ after : RetainedState support call.completion.session [],
      SourceCall support support.identityHeader.header invocation state.heap [.word seed]
        (.value (.word seed)) after.heap := by
  obtain ⟨request⟩ := RecursiveNamedPublicHistoryFrontdoor.recover_start
    fixture.recipePrepared [support.failedInput, support.identityInput] support.rows support.complete
    state.atRecipe state.history.current.1 state.atSession call.started
  have selectedHeader : request.header = support.identityHeader.header :=
    selected_identity_at support.failedHeader support.identityHeader support.header_list request
  have inputs : RecursiveNamedPublicFunctionHistoryInputs.Inputs [] request.header.function.context
      (request.header.bindings.map (fun binding => binding.1.scheme.body))
      [.word seed] [.word seed] := by
    rw [selectedHeader, support.identityHeader.identity_inputs]
    exact .cons (.data ⟨.word seed, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word seed⟩
      ⟨.word seed, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word seed⟩) .nil
  have registry := request.started.simple_registry state.registry
    (by intro value member; have same := List.mem_singleton.mp member; exact same ▸ SourceCoreIndexedSession.SimplePublic.word seed)
  have metadata : SourceCoreRawMetadata.Extends request.encodedValues.registry receiver.completion.result.context.registry := by
    rw [registry]
    exact receiver.completion.result.extension
  have descriptor : SourceCoreCallableContracts.Descriptor fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable.table
      (.named request.header.named.signature.key) := by
    rw [selectedHeader]
    exact support.identityDescriptor
  obtain ⟨actual, generation, value, finalStore, capture, sourceSize, outcome, after,
      finalMap, finalWorld, succeeded, valueEq, _typeEq, _budgetEq, returnedAt, trace, result,
      reached, _related, retained⟩ :=
    CallableIndexedOwnedPreparedStagedHistoryPublicContinuations.public_run_succeeded_retains
      (inputs := [support.failedInput, support.identityInput]) (rows := support.rows)
      (stagePrepared := actualStagePrepared fixture)
      (completion := CallableIndexedOwnedPublicFaultReceivers.Receiver.of_completion receiver.completion)
      (receiver := CallableIndexedOwnedPublicFaultReceiverTables.issued_of_runSource receiver.executed)
      (profile := observed.profile) (observations := support.observations)
      (extension := receiver.completion.result.extension)
      (semantic := by intro reason token represented; exact represented)
      (family := support.family) (namedTerminals := support.terminals) (namedSupport := support.supports)
      (wellFormed := fixture.source_wellFormed) (prepared := fixture.recipePrepared)
      (selected := request.selected) (caller := state.caller) (history := state.history)
      (atCheckpoint := request.atCheckpoint) (started := request.started)
      (inputReceipts := inputs) (metadata := metadata) (sourceAt := request.sourceAt)
      (invocation := invocation) call.started call.executed descriptor
  have requested := request.started.original.result_type_at
    (show state.artifact.RecipeAt fixture.recipe from by
      have convert : ∀ (artifact : SourceCoreIndexedSession.Artifact) (recipe : SourceCoreIndexedSession.Recipe),
          RecursiveNamedPublicStartMeaning.ArtifactRecipe artifact recipe → artifact.RecipeAt recipe :=
        fun artifact _ atRecipe => by cases artifact; exact atRecipe
      exact convert _ _ state.atRecipe)
    request.started.selected
  have resultType := (RecursiveNamedPublicRootSourceSignature.inputs_and_result request.selected).2
  rw [resultType, selectedHeader, support.identityHeader.identity_result_type] at requested
  have outcomeValue := RecursiveNamedPublicWordResultMeaning.result_word succeeded requested
    (valueEq.symm.trans call.returned)
    (by rw [selectedHeader]; exact support.identityHeader.identity_output) result
  have returnedRegistry := request.started.returned_registry succeeded
  rw [registry] at returnedRegistry
  let next : RetainedState support call.completion.session [] :=
    ⟨state.artifact, actual.session, finalMap, finalWorld, after, finalStore, reached,
      returnedAt, state.atRecipe, returnedRegistry, retained⟩
  refine ⟨next, request.rawD, request.function, sourceSize, ?_, ?_⟩
  · rw [← selectedHeader]; exact request.sourceAt
  · simpa only [outcomeValue] using trace

end Tests.SourceCoreInitialLexicalFailure
end

section
-- leanmerge: from Solcore.Test.SourceCoreInitialLexicalFailurePublicExecution
/-! A first public failure returns the heap containing its newly allocated
absent local. That exact session and proved History then run identity(37),
which retains the absent cell while allocating its own initialized parameter. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreInitialLexicalFailure
open Solcore Frontend SourceInference SourceSemantics CoreLowering

structure ObservedSequence (fixture : CompiledFixture) (observed : ObservedProgram fixture) where
  first : ObservedPublicRun fixture observed
  next : ObservedContinuation first

def observeSequence (fixture : CompiledFixture) (observed : ObservedProgram fixture) :
    IO (ObservedSequence fixture observed) := do
  let first ← observePublicRun fixture observed
  let next ← observeContinuation first
  return ⟨first, next⟩

def SequenceMeaning {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (failedStages : ObservedStages fixture observed.failedRow)
    (identityStages : ObservedStages fixture observed.identityRow)
    (sequence : ObservedSequence fixture observed) (receiver : ObservedReceiver fixture observed) : Prop :=
  ∃ support : PublicSupports receiver,
    let failedScope := RecursiveStageRegistry.scope failedStages.sidecar [] support.failedHeader.header.function
    let identityScope := RecursiveStageRegistry.scope identityStages.sidecar [] support.identityHeader.header.function
    ∃ initial : RetainedState support sequence.first.returned [],
    ∃ final : RetainedState support sequence.next.completion.session [],
    ∃ location parameterLocation,
      Dynamic.Heap.Allocates ⟨[]⟩ .word none location initial.heap ∧
      Dynamic.Heap.Reads initial.heap location {type := .word, value := none} ∧
      Dynamic.Heap.Allocates initial.heap .word (some (.word seed)) parameterLocation final.heap ∧
      Dynamic.Heap.Reads final.heap location {type := .word, value := none} ∧
      SourceCall support support.failedHeader.header failedScope ⟨[]⟩ []
        (.fault (.semantic (.uninitializedLocation location))) initial.heap ∧
      SourceCall support support.identityHeader.header identityScope initial.heap [.word seed]
        (.value (.word seed)) final.heap

/-- Every semantic premise is produced from this accepted program and its
actual public events, including the first failed call's retained heap. -/
theorem sequence_meaning (fixture : CompiledFixture) (observed : ObservedProgram fixture)
    (failedStages : ObservedStages fixture observed.failedRow)
    (identityStages : ObservedStages fixture observed.identityRow)
    (sequence : ObservedSequence fixture observed) (receiver : ObservedReceiver fixture observed) :
    SequenceMeaning failedStages identityStages sequence receiver := by
  obtain ⟨support⟩ := static_supports
    (completion := CallableIndexedOwnedPublicFaultReceivers.Receiver.of_completion receiver.completion) fixture observed failedStages identityStages
    receiver.completion.result.context.registry
    (CallableIndexedOwnedPublicFaultReceiverTables.issued_of_runSource receiver.executed)
  let failedScope := RecursiveStageRegistry.scope failedStages.sidecar [] support.failedHeader.header.function
  let identityScope := RecursiveStageRegistry.scope identityStages.sidecar [] support.identityHeader.header.function
  obtain ⟨initial, failure, failedCall⟩ := first_meaning support failedStages sequence.first
  obtain ⟨rawD, global, size, sourceAt, applied⟩ := failedCall
  obtain ⟨location, failureEq, allocated, absent⟩ := support.failedHeader.failed_heap sourceAt applied
  obtain ⟨final, identityCall⟩ := initial.identity sequence.next identityScope
  obtain ⟨identityD, identityGlobal, identitySize, identityAt, identityApplied⟩ := identityCall
  obtain ⟨parameterLocation, parameterAllocated⟩ := support.identityHeader.identity_heap identityAt identityApplied
  refine ⟨support, initial, final, location, parameterLocation, allocated, absent,
    parameterAllocated, parameterAllocated.preserves_read absent, ?_, ?_⟩
  · exact ⟨rawD, global, size, sourceAt, failureEq ▸ applied⟩
  · exact ⟨identityD, identityGlobal, identitySize, identityAt, identityApplied⟩

def run : IO Unit := do
  let fixture ← compiledFixture
  let observed ← observeProgram fixture
  let failedStages ← observeStages fixture observed.failedRow
  let identityStages ← observeStages fixture observed.identityRow
  let sequence ← observeSequence fixture observed
  let receiver ← observeReceiver fixture observed
  have _meaning := sequence_meaning fixture observed failedStages identityStages sequence receiver
  IO.println "Actual initial uninitialized failure: absent local retained; same returned session runs identity(37), Source traces and histories proved"

end Tests.SourceCoreInitialLexicalFailure
end

section
-- leanmerge: from Solcore.Test.SourceCoreInitialLexicalFailureForward
/-! The independently established failed Source call produces a public failure
at every sufficient execution budget, including output-validation fuel zero.
The actual initial failure and identity continuation retain their exact heaps. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreInitialLexicalFailure
open Solcore Frontend SourceInference SourceSemantics CoreLowering

/-- The original checkpoint admits every sufficiently large execution budget.
Its actual failure token retains the Source relation without an injectivity
claim about the diagnostic table. -/
def ForwardFailureAt {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed} (support : PublicSupports receiver)
    (first : ObservedPublicRun fixture observed) (failure : Staging.Recursive.Failure)
    (after : Dynamic.Heap) : Prop :=
  ∃ token required,
    CallableIndexedOwnedPublicDecodedStagedCallFaults.faults receiver.completion.result.diagnostics failure token ∧
    ∀ executionFuel outputFuel (outcome : SourceCoreExecution.Outcome first.artifact),
      required ≤ executionFuel → first.checkpoint.ResumeAt executionFuel outputFuel outcome →
      ∃ returned : SourceCoreExecution.Session first.artifact,
        outcome = .failed token returned ∧
        ∃ state : RetainedState support returned [], state.heap = after

private theorem forward_failure {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed} {support : PublicSupports receiver}
    (first : ObservedPublicRun fixture observed)
    {invocation : Staging.Recursive.Scope} {failure : Staging.Recursive.Failure} {after : Dynamic.Heap}
    (trace : SourceCall support support.failedHeader.header invocation ⟨[]⟩ [] (.fault failure) after) :
    ForwardFailureAt support first failure after := by
  obtain ⟨artifact, session, checkpoint, root, world, store, native, encodedValues,
      opened, prepared, sessionAt, checkpointAt, started⟩ := first.start_receipt
  have startupRegistry := first.metadata_at_start opened sessionAt started
  obtain ⟨selectedHeader, selected⟩ := started.selection prepared support.complete
  have selectedEq : selectedHeader = support.failedHeader.header := by
    apply selected_failed_root support.failedHeader support.identityHeader (root := root) (support.header_list ▸ selected)
    exact of_decide_eq_true (List.find?_some
      (p := fun root : SourceCoreIndexedSession.Root fixture.recipe.compiled => decide (root.key = observed.failedRow.row.key)) started.selected)
  subst selectedHeader
  have inputs : RecursiveNamedPublicNestedInputs.Inputs support.rows session support.failedHeader.header.function.context
      (support.failedHeader.header.bindings.map (fun binding => binding.1.scheme.body)) [] [] := by
    rw [support.failedHeader.failed_inputs]
    exact .nil
  have metadata : SourceCoreRawMetadata.Extends encodedValues.registry receiver.completion.result.context.registry := by
    rw [startupRegistry]
    exact receiver.completion.result.extension
  obtain ⟨rawD, function, sourceSize, sourceAt, trace⟩ := trace
  obtain ⟨caller, capture, token, finalStore, finalMap, finalWorld, required, related,
      _nativeEnough, _fullResult, publicEnough⟩ :=
    CallableIndexedOwnedPreparedStagedInitializedFailurePreservation.public_resume_has_sufficient_fuel
      (inputs := [support.failedInput, support.identityInput]) (rows := support.rows) (distinct := support.distinct)
      (stagePrepared := actualStagePrepared fixture)
      (completion := CallableIndexedOwnedPublicFaultReceivers.Receiver.of_completion receiver.completion)
      (receiver := CallableIndexedOwnedPublicFaultReceiverTables.issued_of_runSource receiver.executed)
      (profile := observed.profile) (bodyRegistry := receiver.completion.result.context.registry)
      (semanticFaults := CallableIndexedOwnedPublicDecodedCallFaults.faults receiver.completion.result.diagnostics)
      (observations := support.observations) (extension := receiver.completion.result.extension)
      (semantic := by intro reason token represented; exact represented)
      (family := support.family) (namedTerminals := support.terminals) (namedSupport := support.supports)
      (wellFormed := fixture.source_wellFormed) (prepared := prepared) (selected := selected)
      (opened := opened) (fresh := first.fresh) (ready := .single first.ready)
      (sameRuntime := SourceCoreExecution.Session.SameRuntime.refl first.session) (atSession := sessionAt)
      (atCheckpoint := checkpointAt) (started := started) (inputReceipts := inputs)
      (metadata := metadata) (sourceAt := sourceAt) trace
  refine ⟨token, required, related, ?_⟩
  intro executionFuel outputFuel outcome enough resumed
  obtain ⟨returned, actual, reached, outcomeEq, _failed, returnedAt, _related, history, returnedRegistry⟩ :=
    publicEnough executionFuel outputFuel outcome enough resumed
  rw [startupRegistry] at returnedRegistry
  exact ⟨returned, outcomeEq,
    ⟨artifact, actual, finalMap, finalWorld, after, finalStore, reached, returnedAt,
      started.recipe_eq, returnedRegistry, history⟩, rfl⟩

/-- The closed accepted program establishes both actual public executions and
a forward guarantee for the first failure on its original checkpoint. The same
absent local survives the later identity call. -/
theorem sequence_forward_meaning (fixture : CompiledFixture) (observed : ObservedProgram fixture)
    (failedStages : ObservedStages fixture observed.failedRow)
    (identityStages : ObservedStages fixture observed.identityRow)
    (sequence : ObservedSequence fixture observed) (receiver : ObservedReceiver fixture observed) :
    ∃ support : PublicSupports receiver,
      let failedScope := RecursiveStageRegistry.scope failedStages.sidecar [] support.failedHeader.header.function
      let identityScope := RecursiveStageRegistry.scope identityStages.sidecar [] support.identityHeader.header.function
      ∃ initial : RetainedState support sequence.first.returned [],
      ∃ final : RetainedState support sequence.next.completion.session [],
      ∃ location parameterLocation,
        Dynamic.Heap.Allocates ⟨[]⟩ .word none location initial.heap ∧
        Dynamic.Heap.Reads initial.heap location {type := .word, value := none} ∧
        Dynamic.Heap.Allocates initial.heap .word (some (.word seed)) parameterLocation final.heap ∧
        Dynamic.Heap.Reads final.heap location {type := .word, value := none} ∧
        SourceCall support support.failedHeader.header failedScope ⟨[]⟩ []
          (.fault (.semantic (.uninitializedLocation location))) initial.heap ∧
        SourceCall support support.identityHeader.header identityScope initial.heap [.word seed]
          (.value (.word seed)) final.heap ∧
        ForwardFailureAt support sequence.first (.semantic (.uninitializedLocation location)) initial.heap := by
  obtain ⟨support, initial, final, location, parameterLocation, allocated, absent, parameterAllocated,
      retainedAbsent, failureCall, identityCall⟩ :=
    sequence_meaning fixture observed failedStages identityStages sequence receiver
  exact ⟨support, initial, final, location, parameterLocation, allocated, absent, parameterAllocated,
    retainedAbsent, failureCall, identityCall, forward_failure sequence.first failureCall⟩

def runForward : IO Unit := do
  let fixture ← compiledFixture
  let observed ← observeProgram fixture
  let failedStages ← observeStages fixture observed.failedRow
  let identityStages ← observeStages fixture observed.identityRow
  let sequence ← observeSequence fixture observed
  let receiver ← observeReceiver fixture observed
  have _meaning := sequence_forward_meaning fixture observed failedStages identityStages sequence receiver
  let zeroBoundary ← sequence.first.checkpoint.resumeWithReceipt runOptions.executionFuel 0
  match zeroBoundary.val with
  | .failed reason _ =>
      if reason != sequence.first.reason then
        throw (IO.userError "zero-output-budget failure changed its token")
  | _ => throw (IO.userError "zero-output-budget failed call changed its outcome")
  IO.println "Initial Source failure: sufficient public fuel, arbitrary output budget, retained absent cell and identity37 continuation proved"

end Tests.SourceCoreInitialLexicalFailure
end

section
-- leanmerge: from Solcore.Test.SourceCoreSelectedLexicalSourceFirstRuntime
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreSelectedLexicalSourceFirst
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open Tests.SourceCoreInitialLexicalFailure
open Tests.SourceCoreSelectedLexicalSourceStart

private def require (condition : Bool) (message : String) : IO Unit :=
  if condition then pure () else throw (IO.userError message)

def run : IO Unit := do
  let fixture ← compiledFixture
  let observed ← observeProgram fixture
  let profile ← Tests.SourceCoreSelectedLexicalFailure.observeProfile fixture
  let failureStages ← observeStages fixture observed.failedRow
  let scalarStages ← observeStages fixture observed.identityRow
  let failed ← observeStarted fixture observed.failedRow.row.key []
  let scalar ← observeStarted fixture observed.identityRow.row.key [.word seed]
  have _first := fault_from_source profile failureStages failed
  have _scalar := scalar_from_source profile scalarStages scalar
  let .outOfFuel suspended ← failed.call.checkpoint.resume 0 0
    | throw (IO.userError "source-first failure did not suspend at zero fuel")
  let .failed reason after ← suspended.resume 100000 0
    | throw (IO.userError "source-first uninitialized read did not fail")
  let .ok (some diagnostic) := after.diagnostic observed.failedRow.row.key reason
    | throw (IO.userError "source-first lexical diagnostic missing")
  require (match diagnostic.error with | .uninitializedLocal _ => true | _ => false)
    "source-first failure reason changed"
  let .outOfFuel suspended ← scalar.call.checkpoint.resume 0 0
    | throw (IO.userError "source-first scalar did not suspend at zero fuel")
  let .succeeded completed ← suspended.resume 100000 1000
    | throw (IO.userError "source-first identity did not complete")
  require (completed.value == .word seed) "source-first identity did not return37"
  let .ok checkpoint := after.start observed.identityRow.row.key [.word seed] runOptions.inputValidationFuel
    | throw (IO.userError "source-first returned session could not start identity")
  let .succeeded continued ← checkpoint.resume 100000 1000
    | throw (IO.userError "source-first identity after failure did not complete")
  require (continued.value == .word seed) "source-first continuation changed the value"
  require ([failed.session.heapSize, after.heapSize, scalar.session.heapSize,
    completed.session.heapSize, continued.session.heapSize] == [3, 6, 3, 6, 9])
    "source-first public stores changed"
  require (fixture.recipe.compiled.indexed.base.functions.length == 2)
    "source-first original cache changed"
  IO.println "LEXICAL_SOURCE_FIRST_FORWARD_PASS: original checker1000/compiler100; startup-only receipts; independently constructed ordinary identity37 and absent-cell fault; closed forward alternatives; zero-fuel resume; exact public heaps3/6/3/6/9 and returned-session identity37"

end Tests.SourceCoreSelectedLexicalSourceFirst
end
