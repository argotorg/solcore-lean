import Solcore.Test.SourceCoreDirectOutputPublicExecution
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicDirectCallableFunctionPreservation

/-! Genuine issuer receipts close function-output preservation on the actual
direct make(20) checkpoint. The same runtime scenario reuses captures 10/20/10. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreDirectFunctionForward
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open Tests.SourceCoreCapturedReuse Tests.SourceCoreDirectOutput
open RecursiveNamedPublicFunctionHistory (Entry)

private def observeOwnedPublicRun (fixture : CompiledFixture) {signature : ProgramFunctionSignature} (observed : ObservedRow fixture signature) :
    IO { first : ObservedPublicRun fixture observed // first.bootstrap.ExportAuthorityAt } := do
  let opened ← fixture.facadeCompiled.openWithReceipt
  let fresh ← opened.val.bootstrapWithExportReceipt
  match ready : fresh.val.resume 100000 with
  | .error error => throw (IO.userError (reprStr error))
  | .outOfFuel _ => throw (IO.userError "factory bootstrap exhausted")
  | .ready session =>
    match started : session.start observed.row.key [.word seed] runOptions.inputValidationFuel with
    | .error error => throw (IO.userError (reprStr error))
    | .ok checkpoint =>
      let executed ← session.runWithReceipt observed.row.key [.word seed] runOptions
      match result : executed.val with
      | .error error => throw (IO.userError (reprStr error))
      | .ok (.failed _ _) => throw (IO.userError "factory public run failed")
      | .ok (.exportError error _) => throw (IO.userError (reprStr error))
      | .ok (.outOfFuel _) => throw (IO.userError "factory public run exhausted")
      | .ok (.succeeded completion) =>
        match returned : completion.value with
        | .function handle =>
          return ⟨⟨opened.val, opened.property, fresh.val, fresh.property.1, session, ready,
            checkpoint, started, completion, result ▸ executed.property, handle, returned⟩, fresh.property.2⟩
        | _ => throw (IO.userError "factory output was not a function handle")

structure ObservedForwardSequence (fixture : CompiledFixture) (observed : ObservedProgram fixture) where
  sequence : Tests.SourceCoreDirectOutput.ObservedSequence fixture observed
  authority : sequence.first.bootstrap.ExportAuthorityAt

private def confirm (proposition : Prop) [Decidable proposition] (label : String) : IO (PLift proposition) :=
  if accepted : proposition then pure ⟨accepted⟩ else throw (IO.userError label)

def observeForwardSequence (fixture : CompiledFixture) (observed : ObservedProgram fixture) :
    IO (ObservedForwardSequence fixture observed) := do
  let first ← observeOwnedPublicRun fixture observed.makeRow
  let named ← Tests.SourceCoreDirectIssued.observeNamed first.val.completion.session observed.makeRow.row.key
  let second ← observeFunctionInvocation named.completion.session named.handle
  let ⟨distinct⟩ ← confirm (first.val.handle ≠ second.handle) "direct factory reused the original captured handle"
  let invokeFirst ← Tests.SourceCoreCapturedDirect.observeInvocation second.completion.session first.val.handle
  let ⟨firstValue⟩ ← confirm (invokeFirst.completion.value = .word seed) "original capture did not return 10"
  let invokeSecond ← Tests.SourceCoreCapturedDirect.observeInvocation invokeFirst.completion.session second.handle
  let ⟨secondValue⟩ ← confirm (invokeSecond.completion.value = .word secondSeed) "direct factory capture did not return 20"
  let invokeFirstAgain ← Tests.SourceCoreCapturedDirect.observeInvocation invokeSecond.completion.session first.val.handle
  let ⟨firstValueAgain⟩ ← confirm (invokeFirstAgain.completion.value = .word seed) "original capture changed after reuse"
  pure ⟨⟨first.val, named, second, distinct, invokeFirst, firstValue, invokeSecond, secondValue,
    invokeFirstAgain, firstValueAgain⟩, first.property⟩

/-- All future resumes use the actual original checkpoint. The new function
joins the retained collection at the exact independently established heap. -/
def ForwardFunctionAt {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed} (support : PublicSupports receiver)
    {publicArtifact : SourceCoreExecution.Artifact} (publicSession : SourceCoreExecution.Session publicArtifact)
    (entries : List Entry) (handle : SourceCorePublicValues.Handle) : Prop :=
  ∃ checkpoint : SourceCoreExecution.Checkpoint publicArtifact,
    publicSession.startHandlePacked handle (.word secondSeed) runOptions.inputValidationFuel = .ok checkpoint ∧
    ∃ source after required,
      ∀ executionFuel outputFuel (outcome : SourceCoreExecution.Outcome publicArtifact),
        required ≤ executionFuel → 1 ≤ outputFuel →
        checkpoint.ResumeAt executionFuel outputFuel outcome →
        ∃ (completion : SourceCoreExecution.Completion publicArtifact) (exported : Entry),
          outcome = .succeeded completion ∧ completion.value = .function exported.handle ∧
          exported.sourceType = .function .unit .word ∧ exported.source = source ∧
          completion.session.ExportsReady ∧
          ∃ returned : RetainedState support completion.session (entries ++ [exported]), returned.heap = after

private theorem forward_function {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed} {support : PublicSupports receiver}
    {publicArtifact : SourceCoreExecution.Artifact} {publicSession : SourceCoreExecution.Session publicArtifact}
    {entries : List Entry} (state : RetainedState support publicSession entries)
    (entry : Entry) (member : entry ∈ entries)
    (entryType : entry.sourceType = .function .word (.function .unit .word))
    {handle : SourceCorePublicValues.Handle} (entryHandle : entry.handle = handle)
    (call : ObservedFunctionInvocation publicSession handle)
    (exportsReady : publicSession.ExportsReady) (invocation : Staging.Recursive.Scope) :
    ForwardFunctionAt support publicSession entries handle := by
  have input : RecursiveNamedPublicFunctionHistoryInputs.Input entries
      support.makeHeader.header.function.context .word (.word secondSeed) (.word secondSeed) :=
    .data ⟨.word secondSeed, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word secondSeed⟩
      ⟨.word secondSeed, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word secondSeed⟩
  let selection : RecursiveNamedPublicOutputSelections.Selection (.function .unit .word) call.completion.value :=
    call.returned.symm ▸ .function
  obtain ⟨_checkpoint, _actual, _generation, _value, _finalStore, _actualParameter, _actualResult,
      _nativeParameter, _nativeResult, _callable, _packed, _encodedValues, sources, sourceSize, source,
      _payload, after, _finalMap, _finalWorld, _reached, _added, _started, _parameterView, _resultView,
      _succeeded, _actualAt, packing, trace, _result, _nativeValue, _selected, _handles, _related,
      _retained, _encodedRegistry, _returnedRegistry⟩ :=
    RecursiveNamedPublicDirectCallableOutputHistory.public_invoke_succeeded_collects_function_tree
      (receiver := CallableIndexedOwnedPublicFaultReceiverTables.issued_of_runSource receiver.executed)
      (stagePrepared := actualStagePrepared fixture) (profile := observed.profile)
      (observations := support.observations) (extension := receiver.completion.result.extension)
      (semantic := by intro reason token represented; exact represented)
      (family := support.family) (namedTerminals := fun header member =>
        CallableIndexedOwnedPreparedStagedNamedBodies.of_terminal (support.terminals header member)) (namedSupport := support.supports)
      (wellFormed := fixture.source_wellFormed) (history := state.history)
      (entry := entry) (member := member) (entryType := entryType)
      (input := input) (atRecipe := state.atRecipe)
      state.registry receiver.completion.result.extension (.simple (.word secondSeed))
      state.atSession (by simpa only [entryHandle] using call.executed) selection invocation
  obtain ⟨publicCheckpoint, accepted, _resumed⟩ := call.executed
  obtain ⟨checkpoint, atCheckpoint, original⟩ :=
    RecursiveNamedPublicDirectHandleMeaning.recover_handle_start state.atSession accepted
  have imported := (state.history.current.2.2.2.2 entry member).1
  rw [entryType, entryHandle] at imported
  obtain ⟨actualParameter, actualResult, nativeParameter, nativeResult, callable, packed, encodedValues,
      started, _parameterView, _resultView⟩ :=
    RecursiveNamedPublicDirectPackedInputMeaning.actual_start_compatible state.atRecipe
      state.history.current.1 imported original
  have registryEq := started.function_tree_registry (.simple (.word secondSeed)) state.registry
  have metadata : SourceCoreRawMetadata.Extends encodedValues.registry receiver.completion.result.context.registry := by
    rw [registryEq]
    exact receiver.completion.result.extension
  rw [← entryHandle] at started
  obtain ⟨required, payload, finalStore, finalMap, finalWorld, _nativeEnough, _fullResult, publicEnough⟩ :=
    RecursiveNamedPublicDirectCallableFunctionPreservation.public_resume_has_sufficient_fuel
      (receiver := CallableIndexedOwnedPublicFaultReceiverTables.issued_of_runSource receiver.executed)
      (stagePrepared := actualStagePrepared fixture) (profile := observed.profile)
      (observations := support.observations) (extension := receiver.completion.result.extension)
      (semantic := by intro reason token represented; exact represented)
      (family := support.family) (namedTerminals := fun header member =>
        CallableIndexedOwnedPreparedStagedNamedBodies.of_terminal (support.terminals header member)) (namedSupport := support.supports)
      (wellFormed := fixture.source_wellFormed) (history := state.history)
      (entry := entry) (member := member) (entryType := entryType) (input := input)
      (state.atSession.exportsReady_iff.mp exportsReady) started metadata packing trace atCheckpoint
  refine ⟨publicCheckpoint, accepted, source, after, required, ?_⟩
  intro executionFuel outputFuel outcome enough positive resumed
  obtain ⟨publicCompletion, actual, _generation, handle, reached, succeeded, handleValue, _sourceType, _exported,
      indexedAt, _related, history, returnedRegistry, returnedReady⟩ :=
    publicEnough executionFuel outputFuel outcome enough positive resumed
  rw [registryEq] at returnedRegistry
  let exported : Entry := ⟨.function .unit .word, source, handle, payload, nativeResult, outputFuel⟩
  exact ⟨publicCompletion, exported, succeeded, handleValue, rfl, rfl,
    indexedAt.2.2.2.exportsReady_iff.mpr returnedReady,
    ⟨state.artifact, actual.session, finalMap, finalWorld, after, finalStore, reached,
      indexedAt.2.2.2, state.atRecipe, returnedRegistry, history⟩, rfl⟩

/-- The rich initial receipt is obtained from the actual bootstrap operation;
all later export readiness follows the real first run and named issuance. -/
theorem sequence_forward_meaning (fixture : CompiledFixture) (observed : ObservedProgram fixture)
    (extra : ObservedMake fixture observed)
    (makeStages : ObservedStages fixture observed.makeRow)
    (readStages : ObservedStages fixture observed.readRow)
    (observedSequence : ObservedForwardSequence fixture observed) (receiver : ObservedReceiver fixture observed) :
    Tests.SourceCoreDirectOutput.SequenceMeaning makeStages observedSequence.sequence receiver ∧
    ∃ (support : PublicSupports receiver) (first named : Entry),
      ForwardFunctionAt support observedSequence.sequence.named.completion.session [first, named]
        observedSequence.sequence.named.handle := by
  have meaning := Tests.SourceCoreDirectOutput.sequence_meaning fixture observed extra makeStages readStages
    observedSequence.sequence receiver
  refine ⟨meaning, ?_⟩
  obtain ⟨support, first, named, second, _firstType, namedType, _secondType,
    _firstHandle, namedHandle, _secondHandle, _distinct, _namedSource,
    _firstState, namedState, _secondState, _firstInvoked, _secondInvoked, _finalState, _posts⟩ := meaning
  have initialReady := (SourceCoreExecution.Bootstrap.ReadyAt.single observedSequence.sequence.first.ready).exportsReady
    observedSequence.authority
  have firstReady := observedSequence.sequence.first.executed.exportsReady initialReady
  have namedReady := observedSequence.sequence.named.issued.exportsReady firstReady
  exact ⟨support, first, named,
    forward_function namedState named (by simp) namedType namedHandle observedSequence.sequence.second namedReady
      (RecursiveStageRegistry.scope makeStages.sidecar [] support.makeHeader.header.function)⟩

def run : IO Unit := do
  let fixture ← compiledFixture
  let observed ← observeProgram fixture
  let extra ← observeMake fixture observed
  let makeStages ← observeStages fixture observed.makeRow
  let readStages ← observeStages fixture observed.readRow
  let sequence ← observeForwardSequence fixture observed
  let receiver ← observeReceiver fixture observed
  have _meaning := sequence_forward_meaning fixture observed extra makeStages readStages sequence receiver
  IO.println "Actual direct factory: Source implies function export with output fuel 1 and reusable History; captures 10/20/10 retained"

end Tests.SourceCoreDirectFunctionForward
