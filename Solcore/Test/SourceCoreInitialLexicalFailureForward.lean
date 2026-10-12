import Solcore.Test.SourceCoreInitialLexicalFailurePublicExecution
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedInitializedFailurePreservation

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
