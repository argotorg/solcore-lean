import Solcore.Test.SourceCoreRecursiveIndexFailureStep
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicActualRegistryNamedOutputPreservation

/-! Independent Source failure fixes a sufficient execution budget at the
original public checkpoint. Every output budget, including zero, retains the
same reached Source heap, current diagnostic registry and earlier handles. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreRecursiveIndex
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open RecursiveNamedPublicFunctionHistory (Entry)

variable {fixture : CompiledFixture} {observed : ObservedProgram fixture}
  {receiver : ObservedReceiver fixture observed} {support : PublicSupports receiver}
  {artifact : SourceCoreExecution.Artifact}
  {session : SourceCoreExecution.Session artifact} {entries : List Entry}

def ForwardFailureAt (support : PublicSupports receiver)
    {firstHandle secondHandle : SourceCorePublicValues.Handle} {key : Core.Word}
    (call : ObservedFailure session observed.selectRow.row.key [table firstHandle secondHandle, .word key])
    (failure : Staging.Recursive.Failure) (after : Dynamic.Heap) (entries : List Entry) : Prop :=
  ∃ token required,
    ∀ executionFuel outputFuel (outcome : SourceCoreExecution.Outcome artifact),
      required ≤ executionFuel → call.checkpoint.ResumeAt executionFuel outputFuel outcome →
      ∃ returned : SourceCoreExecution.Session artifact,
        outcome = .failed token returned ∧ returned.ExportsReady ∧
        ∃ state : RetainedState support returned entries, state.heap = after ∧
          CallableIndexedOwnedPublicDecodedStagedCallFaults.faults state.receiving.result.diagnostics failure token

theorem forward_failure
    (state : RetainedState support session entries)
    (first second : Entry) (firstMember : first ∈ entries) (secondMember : second ∈ entries)
    (firstType : first.sourceType = closureType) (secondType : second.sourceType = closureType)
    {firstHandle secondHandle : SourceCorePublicValues.Handle}
    (firstHandleEq : first.handle = firstHandle) (secondHandleEq : second.handle = secondHandle)
    {key : Core.Word}
    (call : ObservedFailure session observed.selectRow.row.key [table firstHandle secondHandle, .word key])
    (ready : session.ExportsReady)
    {invocation : Staging.Recursive.Scope} {failure : Staging.Recursive.Failure} {after : Dynamic.Heap}
    (trace : SourceCall support support.selectHeader.header invocation state.heap
      [sourceTable first second, .word key] (.fault failure) after) :
    ForwardFailureAt support call failure after entries := by
  obtain ⟨request⟩ := RecursiveNamedPublicHistoryFrontdoor.recover_start
    fixture.recipePrepared [support.makeInput, support.echoInput, support.chooseInput, support.selectInput]
    support.rows support.complete state.atRecipe state.history.current.1 state.atSession call.started
  have selected := selected_select_at support.makeHeader support.echoHeader support.chooseHeader
    support.selectHeader support.header_list request
  have inputs : RecursiveNamedPublicFunctionHistoryInputs.Inputs entries request.header.function.context
      (request.header.bindings.map (fun binding => binding.1.scheme.body))
      [table firstHandle secondHandle, .word key] [sourceTable first second, .word key] := by
    rw [selected, support.selectHeader.select_input_types_source]
    exact select_inputs first second firstMember secondMember firstType secondType firstHandleEq secondHandleEq key
  obtain ⟨program, present⟩ := RecursiveNamedPublicHistoryRegistryExtension.diagnostics_present state.history
  have semantic : ∀ reason token,
      CallableIndexedOwnedPublicDecodedCallFaults.faults receiver.completion.result.diagnostics reason token →
      CallableIndexedOwnedPublicDecodedStagedCallFaults.faults state.receiving.result.diagnostics (.semantic reason) token := by
    intro reason token represented
    exact CompatibleRegistryDiagnosticExtension.semantic_preserved fixture.recipe.compiled
      receiver.issued state.issued present state.extension represented
  obtain ⟨rawD, function, sourceSize, sourceAt, sourceTrace⟩ := trace
  have sourceAt' : CallableIndexedOwnedFunctionValues.NamedSourceAt request.header rawD function := by
    rw [selected]
    exact sourceAt
  obtain ⟨receiving, contextAt, issued, extended, _diagnostics, _capture, token, finalStore, finalMap,
      finalWorld, required, matched, _nativeEnough, _fullResult, publicEnough⟩ :=
    RecursiveNamedPublicActualRegistryNamedOutputPreservation.public_resume_fault_has_sufficient_fuel
      (inputs := [support.makeInput, support.echoInput, support.chooseInput, support.selectInput]) (rows := support.rows)
      (stagePrepared := actualStagePrepared fixture) (completion := state.receiving)
      (receiver := state.issued) (profile := observed.profile) (observations := support.observations)
      (semantic := semantic) (family := support.family) (namedTerminals := fun header member =>
        CallableIndexedOwnedPreparedStagedNamedBodies.of_terminal (support.terminals header member))
      (namedSupport := support.supports) (wellFormed := fixture.source_wellFormed)
      (prepared := fixture.recipePrepared) (selected := request.selected)
      (caller := state.caller) (history := state.history) (atCheckpoint := request.atCheckpoint)
      (started := request.started) (inputReceipts := inputs) (atRegistry := state.registry)
      (exportsReady := state.atSession.exportsReady_iff.mp ready) (sourceAt := sourceAt') sourceTrace
  refine ⟨token, required, ?_⟩
  intro executionFuel outputFuel outcome enough resumed
  obtain ⟨returned, actual, reached, failedOutcome, _failed, returnedAt, _related, history, registry, returnedReady⟩ :=
    publicEnough executionFuel outputFuel outcome enough resumed
  let next : RetainedState support returned entries := {
    artifact := state.artifact
    session := actual
    mapping := finalMap
    world := finalWorld
    heap := after
    store := finalStore
    caller := reached
    atSession := returnedAt
    atRecipe := state.atRecipe
    receiving := receiving
    issued := issued
    extension := state.extension.trans extended
    registry := (congrArg (·.registry) contextAt).symm ▸ registry
    history := history }
  exact ⟨returned, failedOutcome, returnedAt.exportsReady_iff.mpr returnedReady, next, rfl, matched⟩

end Tests.SourceCoreRecursiveIndex
