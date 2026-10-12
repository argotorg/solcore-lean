import Solcore.Test.SourceCoreDirectFunctionForward
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedInitializedFunctionPreservation

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
