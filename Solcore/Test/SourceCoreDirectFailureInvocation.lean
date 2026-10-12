import Solcore.Test.SourceCoreDirectFailureIssuance
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicActualRegistryFailures
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicActualRegistryFailurePreservation
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreDirectFailure
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open Tests.SourceCoreInitialLexicalFailure
open RecursiveNamedPublicFunctionHistory (Entry)

def failureOptions : SourceCoreExecution.RunOptions := { runOptions with outputValidationFuel := 0 }

structure ObservedFailure {artifact : SourceCoreExecution.Artifact}
    (session : SourceCoreExecution.Session artifact) (handle : SourceCorePublicValues.Handle) where
  reason : Core.Word
  returned : SourceCoreExecution.Session artifact
  executed : session.InvokeAt handle .unit failureOptions (.ok (.failed reason returned))

def observeFailure {artifact : SourceCoreExecution.Artifact}
    (session : SourceCoreExecution.Session artifact) (handle : SourceCorePublicValues.Handle) :
    IO (ObservedFailure session handle) := do
  let executed ← session.invokePackedWithReceipt handle .unit failureOptions
  match result : executed.val with
  | .ok (.failed reason returned) => pure ⟨reason, returned, result ▸ executed.property⟩
  | .error error => throw (IO.userError (reprStr error))
  | _ => throw (IO.userError "direct named call did not fail at output fuel zero")

def ForwardFailureAt {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed} (support : PublicSupports receiver)
    {artifact : SourceCoreExecution.Artifact} (checkpoint : SourceCoreExecution.Checkpoint artifact)
    (entries : List Entry) (failure : Staging.Recursive.Failure) (after : Dynamic.Heap) : Prop :=
  ∃ receiving : CallableIndexedOwnedPublicFaultReceivers.Receiver fixture.recipe.compiled.indexed,
    CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt fixture.recipe.compiled.indexed receiving.entry
      receiving.result.context.registry receiving.result.extension receiving.result.diagnostics ∧
    ∃ token required,
      CallableIndexedOwnedPublicDecodedStagedCallFaults.faults receiving.result.diagnostics failure token ∧
      ∀ executionFuel outputFuel (outcome : SourceCoreExecution.Outcome artifact),
        required ≤ executionFuel → checkpoint.ResumeAt executionFuel outputFuel outcome →
        ∃ returned : SourceCoreExecution.Session artifact,
          outcome = .failed token returned ∧ returned.ExportsReady ∧
          ∃ state : RetainedState support returned entries, state.heap = after

private theorem unit_input {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed} (support : PublicSupports receiver) (entries : List Entry) :
    RecursiveNamedPublicFunctionHistoryInputs.Input entries support.failedHeader.header.function.context
      .unit .unit .unit :=
  .data ⟨.unit, by simp [SourceCoreIndexedSession.DataInput.publicValue], .unit⟩
    ⟨.unit, by simp [SourceCoreIndexedSession.DataInput.publicValue], .unit⟩

theorem invoke {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed} {support : PublicSupports receiver}
    {publicArtifact : SourceCoreExecution.Artifact} {publicSession : SourceCoreExecution.Session publicArtifact}
    {entries : List Entry} (state : RetainedState support publicSession entries)
    (entry : Entry) (member : entry ∈ entries) (entryType : entry.sourceType = .function .unit .word)
    {handle : SourceCorePublicValues.Handle} (entryHandle : entry.handle = handle)
    {global : Dynamic.GlobalFunction} (entrySource : entry.source = .global global)
    (sourceAt : CallableIndexedOwnedFunctionValues.NamedSourceAt support.failedHeader.header
      support.failedInput.prepared.available global)
    (call : ObservedFailure publicSession handle) (ready : publicSession.ExportsReady)
    (invocation : Staging.Recursive.Scope) :
    ∃ (next : RetainedState support call.returned entries) (failure : Staging.Recursive.Failure),
      SourceCall support support.failedHeader.header invocation state.heap [] (.fault failure) next.heap ∧
      ∃ checkpoint : SourceCoreExecution.Checkpoint publicArtifact,
        publicSession.startHandlePacked handle .unit failureOptions.inputValidationFuel = .ok checkpoint ∧
        ForwardFailureAt support checkpoint entries failure next.heap := by
  have invoked : publicSession.InvokeAt entry.handle .unit failureOptions (.ok (.failed call.reason call.returned)) := by
    rw [entryHandle]
    exact call.executed
  obtain ⟨publicCheckpoint, accepted, resumed⟩ := invoked
  obtain ⟨checkpoint, atCheckpoint, original⟩ :=
    RecursiveNamedPublicDirectHandleMeaning.recover_handle_start state.atSession accepted
  have imported := (state.history.current.2.2.2.2 entry member).1
  rw [entryType] at imported
  obtain ⟨parameter, result, nativeParameter, nativeResult, callable, packed, values,
      started, _parameterView, _resultView⟩ :=
    RecursiveNamedPublicDirectPackedInputMeaning.actual_start_compatible state.atRecipe state.history.current.1 imported original
  have startupRegistry := started.function_tree_registry (.simple .unit) state.registry
  have registry : state.session.RegistryAt receiver.completion.result.context.registry := receiver.registry.symm ▸ state.registry
  obtain ⟨receiving, contextAt, issued, _extended, _diagnostics, actual, value, finalStore,
      sources, sourceSize, failure, after, finalMap, finalWorld, reached, failed, returnedAt,
      packing, arity, trace, _result, _related, retained, returnedRegistry⟩ :=
    RecursiveNamedPublicActualRegistryFailures.public_resume_failed_at_arity
      (completion := receiver.completion) receiver.issued (actualStagePrepared fixture) observed.profile
      support.observations (by intro reason token represented; exact represented)
      support.family support.terminals support.supports fixture.source_wellFormed state.history entry member
      entryType (unit_input support entries) registry started atCheckpoint resumed invocation
  have actualRegistry : receiving.result.context.registry = receiver.completion.result.context.registry :=
    (congrArg (·.registry) contextAt).trans (startupRegistry.trans receiver.registry.symm)
  rw [actualRegistry] at retained
  rw [startupRegistry] at returnedRegistry
  let next : RetainedState support call.returned entries :=
    ⟨state.artifact, actual, finalMap, finalWorld, after, finalStore, reached,
      returnedAt, state.atRecipe, returnedRegistry, retained⟩
  have noParameters : support.failedHeader.header.function.parameters = [] := by
    rw [support.failedHeader.header.parameters, ← support.failedHeader.header.inputs,
      support.failedHeader.source, observed.failedShape.inputs]
  have sourceCount : sources.length = 0 := by
    rw [entrySource] at arity
    have count := arity.global_count fixture.source_wellFormed sourceAt.frame.instantiated
    rw [← sourceAt.frame.parameters, noParameters] at count
    exact count.symm
  have noSources := List.eq_nil_of_length_eq_zero sourceCount
  subst sources
  obtain ⟨receivingForward, contextForward, issuedForward, _extendedForward, _diagnosticsForward,
      required, token, forwardStore, forwardMap, forwardWorld, faultRelated, _enough, _fullResult, publicEnough⟩ :=
    RecursiveNamedPublicActualRegistryFailurePreservation.public_resume_has_sufficient_fuel
      (completion := receiver.completion) receiver.issued (actualStagePrepared fixture) observed.profile
      support.observations (by intro reason token represented; exact represented)
      support.family support.terminals support.supports fixture.source_wellFormed state.history entry member
      entryType (unit_input support entries) registry (state.atSession.exportsReady_iff.mp ready)
      started packing arity trace atCheckpoint
  refine ⟨next, failure, ⟨support.failedInput.prepared.available, global, sourceSize, sourceAt, ?_⟩,
    publicCheckpoint, ?_, receivingForward, issuedForward, token, required, faultRelated, ?_⟩
  · simpa only [entrySource] using trace
  · simpa only [entryHandle] using accepted
  · intro executionFuel outputFuel outcome bound resumed
    obtain ⟨returned, actual, reached, outcomeEq, _failed, atReturned, _related, history, registry, exportsReady⟩ :=
      publicEnough executionFuel outputFuel outcome bound resumed
    have actualRegistry : receivingForward.result.context.registry = receiver.completion.result.context.registry :=
      (congrArg (·.registry) contextForward).trans (startupRegistry.trans receiver.registry.symm)
    rw [actualRegistry] at history
    rw [startupRegistry] at registry
    exact ⟨returned, outcomeEq, atReturned.exportsReady_iff.mpr exportsReady,
      ⟨state.artifact, actual, forwardMap, forwardWorld, after, forwardStore, reached,
        atReturned, state.atRecipe, registry, history⟩, rfl⟩

end Tests.SourceCoreDirectFailure
