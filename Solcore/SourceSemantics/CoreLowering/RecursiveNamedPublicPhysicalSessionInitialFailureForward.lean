import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicPhysicalSessionInitial
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicPhysicalSessionFailureForward

/-! An initial Source fault supplies sufficient execution fuel and retains the
exact failed session, decoded reason and physical state with no handles. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicPhysicalSessionInitialFailureForward
open Core Frontend SourceInference
open CallableIndexedOwnedPreparedFiniteNamedInventories (Input Inventory headers)
open CallableIndexedOwnedFunctionValues (Header)
open CallableIndexedOwnedPreparedBootstrapRootState (keys)
open RecursiveNamedPublicPhysicalSessionState (StartedCall State SourceCall)
open RecursiveNamedPublicPhysicalSessionInitial (Started)
open CallableIndexedOwnedPreparedPhysicalProgramSupport (Support stagePrepared)

variable {recipe : SourceCoreIndexedSession.Recipe}
  {inputs : List (Input recipe.compiled)} (rows : Inventory inputs)
  (prepared : SourceCoreIndexedSession.Recipe.prepare recipe.compiled = .ok recipe)
  (anchor header : Header recipe.compiled (Program.ofChecked recipe.compiled.sourceProgram))
  {initial : CallableIndexedOwnedPublicFaultReceivers.Receiver recipe.compiled.indexed}
  (support : Support recipe.compiled (headers rows) (keys recipe.compiled) initial)
  {publicArtifact : SourceCoreExecution.Artifact}
  {session : SourceCoreExecution.Session publicArtifact}
  {key : SourceCoreIndexedSession.Key} {publicArguments : List SourceCorePublicValues.Value}
  {options : SourceCoreExecution.RunOptions}

theorem first_failure
    (distinct : (inputs.map (fun input => input.prepared.index)).Nodup)
    (call : StartedCall session key publicArguments options)
    (start : Started rows prepared header call)
    (simple : ∀ value ∈ publicArguments, SourceCoreIndexedSession.SimplePublic value)
    (inputTypes : RecursiveNamedPublicDataArgumentReceipts.PublicDataTypes
      header.function.context publicArguments header.types)
    {arguments : List Dynamic.Value}
    (inputMeanings : RecursiveNamedPublicDataInputs.Meanings publicArguments arguments)
    {invocation : Staging.Recursive.Scope} {after : Dynamic.Heap} {failure : Staging.Recursive.Failure}
    (trace : SourceCall anchor header invocation ⟨[]⟩ arguments (.fault failure) after) :
    RecursiveNamedPublicPhysicalSessionFailureForward.FailureForwardAt (entries := [])
      rows anchor initial support.profile recipe failure call after := by
  have startupRegistry := start.registry rows prepared header simple
  have metadata : SourceCoreRawMetadata.Extends start.encodedValues.registry initial.result.context.registry := by
    rw [startupRegistry, support.registry]
    exact .refl _
  obtain ⟨caller, stable, globalReference, heaps, heapTyped, represented, argumentsTyped⟩ :=
    CallableIndexedOwnedPreparedStagedInitializedPhysicalClosureArguments.initial_data_arguments
      (inputs := inputs) (rows := rows) (distinct := distinct) (completion := initial)
      (profile := support.profile) (bodyRegistry := initial.result.context.registry)
      (semanticFaults := CallableIndexedOwnedPublicDecodedCallFaults.faults initial.result.diagnostics)
      (wellFormed := support.wellFormed) (prepared := prepared) (selected := start.selected)
      (opened := start.opened) (fresh := start.fresh) (ready := start.ready)
      (sameRuntime := SourceCoreExecution.Session.SameRuntime.refl session) (atSession := start.atSession)
      (started := start.started) (inputTypes := inputTypes) (inputMeanings := inputMeanings) (metadata := metadata)
  obtain ⟨rawD, function, sourceSize, sourceAt, applied⟩ := trace
  obtain ⟨capture, value, finalStore, finalMap, finalWorld, requiredExecution, enough, result⟩ :=
    CallableIndexedOwnedPreparedStagedPhysicalBodyPublicInvocationBounds.preserves_root
      (stagePrepared := stagePrepared recipe.compiled) (completion := initial)
      (functions := CallableIndexedOwnedPreparedPhysicalProgramSupport.functions support)
      (owner := CallableIndexedOwnedPreparedBootstrapRootState.owner recipe.compiled)
      (packet := support.bodies header start.selected.member)
      (preservesBodies := fun budget {child} selected =>
        CallableIndexedOwnedPreparedPhysicalProgramSupport.preserves_bodies support support.issued (.refl _)
          header start.selected.member selected budget)
      (keyPhysical := CallableIndexedOwnedPreparedPhysicalBootstrap.key_physical _ _)
      (physical := caller.physical) (wellFormed := support.wellFormed)
      (selected := start.selected) (caller := caller.base.val)
      (globalReference := globalReference) (stable := stable) (heapTyped := heapTyped)
      (represented := represented) (argumentsTyped := argumentsTyped) (heaps := heaps)
      (sourceAt := sourceAt) (supports := (RecursiveNamedPublicReturnedValues.header_context_supports
        header anchor support.wellFormed).2) applied
  obtain ⟨token, rfl, faultRelated⟩ : ∃ token,
      value = .inLeft header.output (.word token) ∧
      CallableIndexedOwnedPublicDecodedStagedCallFaults.faults initial.result.diagnostics failure token := by
    have related := result.2.1
    cases related with
    | fault related => exact ⟨_, rfl, related⟩
  have completes : ∀ executionFuel, requiredExecution ≤ executionFuel →
      start.checkpoint.NativeDone executionFuel (.inLeft header.output (.word token)) finalStore :=
    fun fuel bound => start.started.initial.native_done_iff.mpr (enough fuel bound)
  have contextSupports := (RecursiveNamedPublicReturnedValues.header_context_supports
    header anchor support.wellFormed).1
  have callerHeap := heapTyped.transportContext contextSupports
  have callerArguments := argumentsTyped.transportContext contextSupports
  obtain ⟨packed, packing⟩ := Dynamic.ValuesPack.exists_pack arguments
  have preserved := Staging.Recursive.FaultPreservation.applies support.wellFormed
    (RecursiveNamedPublicHistorySourceInputs.header_runtime support.wellFormed anchor) callerHeap
    (RecursiveNamedPublicHistorySourceInputs.source_typed support.wellFormed sourceAt anchor ⟨[]⟩)
    packing (packing.hasType callerArguments) applied
  have checkpointReady := start.started.original.initial_registry.exportsReady (start.atSession.exportsReady_iff.mp (start.ready.exportsReady start.authority))
  refine ⟨requiredExecution, token, ?_⟩
  intro executionFuel outputFuel outcome executionBound resumed
  have completed := completes executionFuel executionBound
  obtain ⟨returned, outcomeEq⟩ := resumed.native_failed start.atCheckpoint completed rfl
  have failedResume : call.checkpoint.ResumeAt executionFuel outputFuel (.failed token returned) := outcomeEq ▸ resumed
  obtain ⟨actual, _generation, actualValue, actualStore, actualCompleted, failed, returnedAt⟩ :=
    failedResume.indexed_failed start.atCheckpoint
  have same := completed.symm.trans actualCompleted
  cases same
  obtain ⟨reached, related, post⟩ := result.2.2.2.2.2.2.2
  have retained := RecursiveNamedPublicFunctionHistory.History.first_failed rfl start.started start.selected
    failed result reached ⟨related, post⟩ preserved.1
  have physicalRetained := RecursiveNamedPublicPhysicalHistory.physical_of_result caller.physical result
  have returnedRegistry : actual.RegistryAt initial.result.context.registry := by
    have actualRegistry := congrArg SourceCoreCompatibleValues.Context.registry
      (failed.2.2.2.2.1.trans start.started.values)
    exact actualRegistry.trans (startupRegistry.trans support.registry.symm)
  let next : State rows anchor initial support.profile recipe returned [] := {
    artifact := start.artifact
    session := actual
    mapping := finalMap
    world := finalWorld
    heap := after
    store := finalStore
    caller := reached
    atSession := returnedAt
    atRecipe := start.started.recipe_eq
    receiving := initial
    issued := support.issued
    extension := .refl _
    registry := returnedRegistry
    history := ⟨retained, physicalRetained⟩ }
  exact ⟨returned, outcomeEq, returnedAt.exportsReady_iff.mpr (failed.exportsReady checkpointReady),
    next, rfl, faultRelated⟩

end Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicPhysicalSessionInitialFailureForward
