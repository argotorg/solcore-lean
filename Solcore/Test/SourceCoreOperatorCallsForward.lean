import Solcore.Test.SourceCoreOperatorCallsStep
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicActualRegistryNamedOutputPreservation

/-! Following named execution derives sufficient public fuel from the independent
Source trace at the exact retained heap. The output and next history follow for
every sufficient resume of the original checkpoint. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreOperatorCalls
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedFiniteNamedInventories (headers)
open RecursiveNamedPublicFunctionHistory (Entry)

def ForwardAt {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed} (support : PublicSupports receiver)
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    (entries : List Entry) {handle : SourceCorePublicValues.Handle} {flag : Bool} {value result : Core.Word}
    (call : ObservedCall session observed.selectRow.row.key (selectArguments handle flag value) result)
    (after : Dynamic.Heap) : Prop :=
  ∃ requiredExecution requiredOutput,
    ∀ executionFuel outputFuel (outcome : SourceCoreExecution.Outcome artifact),
      requiredExecution ≤ executionFuel → requiredOutput ≤ outputFuel →
      call.checkpoint.ResumeAt executionFuel outputFuel outcome →
      ∃ completion : SourceCoreExecution.Completion artifact,
        outcome = .succeeded completion ∧ completion.value = .word result ∧
        completion.session.ExportsReady ∧
        ∃ returned : RetainedState support completion.session entries, returned.heap = after

theorem forward_select {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed} {support : PublicSupports receiver}
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    {entries : List Entry} (state : RetainedState support session entries)
    (entry : Entry) (member : entry ∈ entries) (entryType : entry.sourceType = functionType)
    {handle : SourceCorePublicValues.Handle} (entryHandle : entry.handle = handle)
    {flag : Bool} {value returned : Core.Word}
    (call : ObservedCall session observed.selectRow.row.key (selectArguments handle flag value) returned)
    (ready : session.ExportsReady) {invocation : Staging.Recursive.Scope} {after : Dynamic.Heap}
    (trace : SourceCall support support.selectHeader.header invocation state.heap
      [entry.source, .bool flag, .word value] (.value (.word returned)) after) :
    ForwardAt support entries call after := by
  obtain ⟨request⟩ := RecursiveNamedPublicHistoryFrontdoor.recover_start
    fixture.recipePrepared [support.identityInput, support.selectInput] support.rows support.complete
    state.atRecipe state.history.current.1 state.atSession call.started
  have selectedHeader : request.header = support.selectHeader.header :=
    selected_select_at support.identityHeader support.selectHeader support.header_list request
  have inputs : RecursiveNamedPublicFunctionHistoryInputs.Inputs entries request.header.function.context
      (request.header.bindings.map (fun binding => binding.1.scheme.body))
      (selectArguments handle flag value) [entry.source, .bool flag, .word value] := by
    rw [selectedHeader, support.selectHeader.select_input_types]
    change RecursiveNamedPublicFunctionHistoryInputs.Inputs entries support.selectHeader.header.function.context
      [functionType, .bool, .word] [.function handle, .bool flag, .word value]
      [entry.source, .bool flag, .word value]
    refine .cons ?_ (.cons (.data ?_ ?_) (.cons (.data ?_ ?_) .nil))
    · rw [← entryType, ← entryHandle]; exact .retained entry member
    · exact ⟨.bool flag, by simp [SourceCoreIndexedSession.DataInput.publicValue], .bool flag⟩
    · exact ⟨.bool flag, by simp [SourceCoreIndexedSession.DataInput.publicValue], .bool flag⟩
    · exact ⟨.word value, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word value⟩
    · exact ⟨.word value, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word value⟩
  obtain ⟨program, present⟩ := RecursiveNamedPublicHistoryRegistryExtension.diagnostics_present state.history
  have semantic : ∀ reason token,
      CallableIndexedOwnedPublicDecodedCallFaults.faults receiver.completion.result.diagnostics reason token →
      CallableIndexedOwnedPublicDecodedStagedCallFaults.faults state.receiving.result.diagnostics (.semantic reason) token := by
    intro reason token represented
    exact CompatibleRegistryDiagnosticExtension.semantic_preserved fixture.recipe.compiled
      receiver.issued state.issued present state.extension represented
  obtain ⟨rawD, function, sourceSize, sourceAt, applied⟩ := trace
  have sourceAt' : CallableIndexedOwnedFunctionValues.NamedSourceAt request.header rawD function := by
    rw [selectedHeader]; exact sourceAt
  obtain ⟨receiving, contextAt, issued, extended, _diagnostics, _capture,
      payload, finalStore, finalMap, finalWorld, requiredExecution, requiredOutput,
      _nativeEnough, fullResult, publicEnough⟩ :=
    RecursiveNamedPublicActualRegistryNamedOutputPreservation.public_resume_has_sufficient_fuel
      (inputs := [support.identityInput, support.selectInput]) (rows := support.rows)
      (stagePrepared := actualStagePrepared fixture) (completion := state.receiving)
      (receiver := state.issued) (profile := observed.profile) (observations := support.observations)
      (semantic := semantic) (family := support.family)
      (namedTerminals := support.terminals) (namedSupport := support.supports)
      (wellFormed := fixture.source_wellFormed) (prepared := fixture.recipePrepared)
      (selected := request.selected) (caller := state.caller) (history := state.history)
      (atCheckpoint := request.atCheckpoint) (started := request.started)
      (inputReceipts := inputs) (atRegistry := state.registry)
      (exportsReady := state.atSession.exportsReady_iff.mp ready) (sourceAt := sourceAt') applied
  have atRecipe : state.artifact.RecipeAt fixture.recipe := by
    have convert : ∀ (artifact : SourceCoreIndexedSession.Artifact) (recipe : SourceCoreIndexedSession.Recipe),
        RecursiveNamedPublicStartMeaning.ArtifactRecipe artifact recipe → artifact.RecipeAt recipe :=
      fun artifact _ atRecipe => by cases artifact; exact atRecipe
    exact convert _ _ state.atRecipe
  have requested := request.started.original.result_type_at atRecipe request.started.selected
  have resultType := (RecursiveNamedPublicRootSourceSignature.inputs_and_result request.selected).2
  rw [resultType, selectedHeader, support.selectHeader.result_type] at requested
  have nativeWord : payload = .word returned := by
    have represented := fullResult.2.1
    rw [selectedHeader, support.selectHeader.output] at represented
    cases represented with
    | value related =>
      obtain ⟨word, same, native⟩ := CompatibleExpressionPrimitives.word_fields related
      exact native.trans (congrArg Core.Value.word (Dynamic.Value.word.inj same).symm)
  refine ⟨requiredExecution, requiredOutput, ?_⟩
  intro executionFuel outputFuel outcome executionBound outputBound resumed
  obtain ⟨completion, actual, _generation, reached, succeeded, exported, actualAt,
      _related, history, registry, returnedReady⟩ :=
    publicEnough executionFuel outputFuel outcome executionBound outputBound resumed
  let returned : RetainedState support completion.session entries := {
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
    history := history }
  exact ⟨completion, succeeded, actualAt.1.trans ((nativeWord ▸ exported).word_value requested),
    actualAt.2.2.2.exportsReady_iff.mpr returnedReady, returned, rfl⟩

end Tests.SourceCoreOperatorCalls
