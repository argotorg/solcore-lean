import Solcore.Test.SourceCoreNestedFormationPublicExecution
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicActualRegistryOutputCollectionPreservation

/-! Independent Source success at an outer closure produces a reusable inner
function and preserves the exact reached heap for every sufficient public resume. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreNestedFormation
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open RecursiveNamedPublicFunctionHistory (Entry)

def ForwardFormationAt {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed} (support : PublicSupports receiver)
    {publicArtifact : SourceCoreExecution.Artifact} (publicSession : SourceCoreExecution.Session publicArtifact)
    (entries : List Entry) (handle : SourceCorePublicValues.Handle)
    (source : Dynamic.Value) (after : Dynamic.Heap) : Prop :=
  ∃ checkpoint : SourceCoreExecution.Checkpoint publicArtifact,
    publicSession.startHandlePacked handle .unit runOptions.inputValidationFuel = .ok checkpoint ∧
    ∃ requiredExecution requiredOutput,
      ∀ executionFuel outputFuel (outcome : SourceCoreExecution.Outcome publicArtifact),
        requiredExecution ≤ executionFuel → requiredOutput ≤ outputFuel →
        checkpoint.ResumeAt executionFuel outputFuel outcome →
        ∃ completion : SourceCoreExecution.Completion publicArtifact,
          outcome = .succeeded completion ∧ completion.session.ExportsReady ∧
          ∃ inner : Entry, inner.sourceType = closureType ∧ inner.source = source ∧
            completion.value = .function inner.handle ∧ inner.handle.sourceType = closureType ∧
            ∃ returned : RetainedState support completion.session (entries ++ [inner]), returned.heap = after

theorem forward_formation {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed} {support : PublicSupports receiver}
    {publicArtifact : SourceCoreExecution.Artifact} {publicSession : SourceCoreExecution.Session publicArtifact}
    {entries : List Entry} (state : RetainedState support publicSession entries)
    (entry : Entry) (member : entry ∈ entries) (entryType : entry.sourceType = outerType)
    {handle : SourceCorePublicValues.Handle} (entryHandle : entry.handle = handle)
    (handleType : handle.sourceType = outerType)
    (call : ObservedFormation publicSession handle) (exportsReady : publicSession.ExportsReady)
    {invocation : Staging.Recursive.Scope} {after : Dynamic.Heap} {arguments : List Dynamic.Value}
    {source : Dynamic.Value} (packing : Dynamic.ValuesPack arguments .unit)
    (trace : SourceInvocation support invocation state.heap entry.source arguments (.value source) after) :
    ForwardFormationAt support publicSession entries handle source after := by
  have unitInput : RecursiveNamedPublicFunctionHistoryInputs.Input entries
      support.makeHeader.header.function.context .unit .unit .unit :=
    .data ⟨.unit, by simp [SourceCoreIndexedSession.DataInput.publicValue], .unit⟩
      ⟨.unit, by simp [SourceCoreIndexedSession.DataInput.publicValue], .unit⟩
  obtain ⟨publicCheckpoint, accepted, _resumed⟩ := call.executed
  obtain ⟨checkpoint, atCheckpoint, original⟩ :=
    RecursiveNamedPublicDirectHandleMeaning.recover_handle_start state.atSession accepted
  have imported := (state.history.current.2.2.2.2 entry member).1
  rw [entryType, entryHandle] at imported
  obtain ⟨actualParameter, actualResult, nativeParameter, nativeResult, callable, packed, encodedValues,
      started, _parameterView, _resultView⟩ :=
    RecursiveNamedPublicDirectPackedInputMeaning.actual_start_compatible state.atRecipe
      state.history.current.1 imported original
  have requested := started.requested_exact handleType
  have checkpointReady := original.initial_registry.exportsReady (state.atSession.exportsReady_iff.mp exportsReady)
  rw [← entryHandle] at started
  obtain ⟨program, present⟩ := RecursiveNamedPublicHistoryRegistryExtension.diagnostics_present state.history
  have semantic : ∀ reason token,
      CallableIndexedOwnedPublicDecodedCallFaults.faults receiver.completion.result.diagnostics reason token →
      CallableIndexedOwnedPublicDecodedStagedCallFaults.faults state.receiving.result.diagnostics (.semantic reason) token := by
    intro reason token represented
    exact CompatibleRegistryDiagnosticExtension.semantic_preserved fixture.recipe.compiled
      receiver.issued state.issued present state.extension represented
  obtain ⟨size, trace⟩ := trace
  obtain ⟨receiving, contextAt, issued, extended, _diagnostics, requiredExecution, requiredOutput,
      payload, finalStore, finalMap, finalWorld, nativeEnough, _fullResult, publicEnough⟩ :=
    RecursiveNamedPublicActualRegistryOutputCollectionPreservation.public_resume_has_sufficient_fuel
      (completion := state.receiving) state.issued (actualStagePrepared fixture) observed.profile
      support.observations semantic support.family support.bodies support.supports
      fixture.source_wellFormed state.history entry member entryType unitInput state.atRecipe state.registry
      (state.atSession.exportsReady_iff.mp exportsReady) started packing trace atCheckpoint
  refine ⟨publicCheckpoint, accepted, requiredExecution, max requiredOutput 1, ?_⟩
  intro executionFuel outputFuel outcome executionBound outputBound resumed
  obtain ⟨completion, actual, _generation, succeeded, exported, actualAt,
      registry, ready, collect⟩ :=
    publicEnough executionFuel outputFuel outcome executionBound (Nat.le_trans (Nat.le_max_left _ _) outputBound) resumed
  obtain ⟨exportedCompletion, handle, sameOutcome, functionValue, handleType, _ready⟩ :=
    SourceCoreExecution.Checkpoint.ResumeAt.runtime_function_succeeded atCheckpoint resumed checkpointReady
      (nativeEnough executionFuel executionBound) requested rfl (by omega)
  have sameCompletion : exportedCompletion = completion := SourceCoreExecution.Outcome.succeeded.inj (sameOutcome.symm.trans succeeded)
  subst exportedCompletion
  obtain ⟨reached, added, selected, _handles, _related, retained⟩ :=
    collect (functionValue.symm ▸ RecursiveNamedPublicNestedOutputSelections.Selection.function)
  let inner : Entry := ⟨closureType, source, handle, payload, nativeResult, outputFuel⟩
  have addedEq : added = [inner] := selected_function functionValue selected
  let returned : RetainedState support completion.session (entries ++ [inner]) := {
    artifact := state.artifact
    session := actual.session
    mapping := finalMap
    world := finalWorld
    heap := after
    store := finalStore
    caller := reached
    atSession := actualAt.2.2.2
    atRecipe := state.atRecipe
    receiving := receiving
    issued := issued
    extension := state.extension.trans extended
    registry := (congrArg (·.registry) contextAt).symm ▸ registry
    history := addedEq ▸ retained }
  exact ⟨completion, succeeded, actualAt.2.2.2.exportsReady_iff.mpr ready,
    inner, rfl, rfl, functionValue, handleType, returned, rfl⟩

def FormationForwardMeaning {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {makeStages : ObservedStages fixture observed.makeRow}
    {sequence : ObservedSequence fixture observed} {receiver : ObservedReceiver fixture observed}
    (meaning : SequenceWitness makeStages sequence receiver) : Prop :=
  ForwardFormationAt meaning.support sequence.first.completion.session [meaning.first]
    sequence.first.handle meaning.firstInner.source meaning.firstFormationState.heap ∧
  ForwardFormationAt meaning.support sequence.second.completion.session [meaning.first, meaning.firstInner, meaning.second]
    sequence.second.handle meaning.secondInner.source meaning.secondFormationState.heap

theorem SequenceWitness.formations_forward {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {makeStages : ObservedStages fixture observed.makeRow}
    {sequence : ObservedSequence fixture observed} {receiver : ObservedReceiver fixture observed}
    (meaning : SequenceWitness makeStages sequence receiver) : FormationForwardMeaning meaning := by
  have ready := (SourceCoreExecution.Bootstrap.ReadyAt.single sequence.first.ready).exportsReady sequence.first.authority
  have firstReady := sequence.first.executed.exportsReady ready
  have firstFormationReady := sequence.firstFormation.executed.exportsReady firstReady
  have secondReady := sequence.second.executed.exportsReady firstFormationReady
  exact ⟨forward_formation meaning.initial meaning.first (by simp)
      meaning.firstType meaning.firstHandle meaning.firstHandleType sequence.firstFormation firstReady
      meaning.firstFormationPacking meaning.firstFormationTrace,
    forward_formation meaning.secondState meaning.second (by simp)
      meaning.secondType meaning.secondHandle meaning.secondHandleType sequence.secondFormation secondReady
      meaning.secondFormationPacking meaning.secondFormationTrace⟩

end Tests.SourceCoreNestedFormation
