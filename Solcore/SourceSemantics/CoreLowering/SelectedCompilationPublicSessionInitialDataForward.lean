import Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicSessionInitialForward
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicInitialReceiver
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicInitialArguments
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicReturnedValues
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicClosureHistory
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicSessionInitial
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicActualRegistryNamedOutputPreservation

/-! Independent initial Source success determines execution and export budgets.
Every sufficiently fueled public resume retains its actual new handle, the same
Source heap and all initialized physical cells. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicSessionInitialDataForward
open Core Frontend SourceInference
open CallableIndexedOwnedPreparedFiniteNamedInventories (Input Inventory headers)
open CallableIndexedOwnedFunctionValues (Header)
open CallableIndexedOwnedPreparedBootstrapRootState (keys)
open SelectedCompilationPublicSessionState (StartedCall State SourceCall)
open SelectedCompilationPublicSessionInitial (Started)
open SelectedCompilationPhysicalProgramSupport (Support stagePrepared)

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

abbrev ForwardAt := @SelectedCompilationPublicSessionInitialForward.ForwardAt

theorem first_function
    (distinct : (inputs.map (fun input => input.prepared.index)).Nodup)
    (call : StartedCall session key publicArguments options)
    (start : Started rows prepared header call)
    (inputTypes : RecursiveNamedPublicDataArgumentReceipts.PublicDataTypes
      header.function.context publicArguments header.types)
    {arguments : List Dynamic.Value}
    (inputMeanings : RecursiveNamedPublicDataInputs.Meanings publicArguments arguments)
    {parameter resultType : TypeSystem.Ty}
    (functionResult : SourceCoreRawMetadata.runtimeType header.function.resultType = .function parameter resultType)
    {invocation : Staging.Recursive.Scope} {after : Dynamic.Heap} {source : Dynamic.Value}
    (trace : SourceCall anchor header invocation ⟨[]⟩ arguments (.value source) after) :
    ForwardAt rows anchor header support call source after := by
  obtain ⟨receiving, contextAt, receiverIssued, receiverExtension⟩ :=
    SelectedCompilationPublicInitialReceiver.of_started support start
  have receiverRegistry := congrArg SourceCoreCompatibleValues.Context.registry contextAt
  have metadata : SourceCoreRawMetadata.Extends start.encodedValues.registry receiving.result.context.registry := by
    rw [receiverRegistry]
    exact .refl _
  obtain ⟨caller, stable, globalReference, heaps, heapTyped, represented, argumentsTyped⟩ :=
    SelectedCompilationPublicInitialArguments.initial_data_arguments
      (inputs := inputs) (rows := rows) (distinct := distinct) (completion := receiving)
      (profile := support.profile) (bodyRegistry := initial.result.context.registry)
      (semanticFaults := CallableIndexedOwnedPublicDecodedCallFaults.faults initial.result.diagnostics)
      (bodyTyping := support.bodyTyping) (prepared := prepared) (selected := start.selected)
      (opened := start.opened) (fresh := start.fresh) (ready := start.ready)
      (sameRuntime := SourceCoreExecution.Session.SameRuntime.refl session) (atSession := start.atSession)
      (started := start.started) (inputTypes := inputTypes) (inputMeanings := inputMeanings) (metadata := metadata)
  obtain ⟨rawD, function, sourceSize, sourceAt, applied⟩ := trace
  obtain ⟨capture, value, finalStore, finalMap, finalWorld, requiredExecution, enough, result⟩ :=
    SelectedCompilationPublicBodyInvocationBounds.preserves_root
      (stagePrepared := stagePrepared recipe.compiled) (completion := receiving)
      (functions := SelectedCompilationPhysicalProgramSupport.functions support)
      (owner := CallableIndexedOwnedPreparedBootstrapRootState.owner recipe.compiled)
      (packet := support.bodies header start.selected.member)
      (preservesBodies := fun budget {child} selected =>
        SelectedCompilationPhysicalProgramSupport.preserves_bodies support receiverIssued receiverExtension
          header start.selected.member selected budget)
      (keyPhysical := CallableIndexedOwnedPreparedPhysicalBootstrap.key_physical _ _)
      (physical := caller.physical) (bodyTyping := support.bodyTyping)
      (selected := start.selected) (caller := caller.base.val)
      (globalReference := globalReference) (stable := stable) (heapTyped := heapTyped)
      (represented := represented) (argumentsTyped := argumentsTyped) (heaps := heaps)
      (sourceAt := sourceAt) (supports := (SelectedCompilationPublicReturnedValues.header_context_supports
        header anchor support.bodyTyping).2) applied
  obtain ⟨payload, rfl⟩ : ∃ payload, value = .inRight .word payload := by
    have representedResult := result.2.1
    cases representedResult with
    | value represented => exact ⟨_, rfl⟩
  have completes : ∀ executionFuel, requiredExecution ≤ executionFuel →
      start.checkpoint.NativeDone executionFuel (.inRight .word payload) finalStore :=
    fun fuel bound => start.started.initial.native_done_iff.mpr (enough fuel bound)
  have representedResult : CompatiblePayload.ValueRep recipe.compiled.compatible.checked
      receiving.result.context.registry (SelectedCompilationPhysicalProgramSupport.functions support)
      finalMap finalWorld header.function.resultType source payload header.output := by
    have representedResult := result.2.1
    cases representedResult with
    | value related => exact related
  have shape : SourceCorePublicOutputShapes.Output recipe.compiled.compatible.checked start.encodedValues.registry
      (finalStore.map Core.Value.type) recipe.program.layouts.definitions header.function.resultType payload := by
    have shaped := CompatiblePublicOutputShapes.ValueRep.output representedResult
    rw [receiverRegistry] at shaped
    rw [result.2.2.1.runtime_hasTypes.world_eq] at shaped
    exact shaped
  have checkpointRegistry : start.checkpoint.RegistryAt start.encodedValues.registry := by
    have values := start.started.values
    generalize checkpointEq : start.checkpoint = checkpoint at values ⊢
    cases checkpoint
    change _ = start.encodedValues at values
    exact congrArg SourceCoreCompatibleValues.Context.registry values
  have atRecipe : start.artifact.RecipeAt recipe := by
    have convert : ∀ (artifact : SourceCoreIndexedSession.Artifact),
        RecursiveNamedPublicStartMeaning.ArtifactRecipe artifact recipe → artifact.RecipeAt recipe :=
      fun artifact atRecipe => by cases artifact; exact atRecipe
    exact convert _ start.started.recipe_eq
  have requested := start.started.original.result_type_at atRecipe start.started.selected
  have resultType := (RecursiveNamedPublicRootSourceSignature.inputs_and_result start.selected).2
  rw [resultType] at requested
  have checkpointReady := start.started.original.initial_registry.exportsReady
    (start.atSession.exportsReady_iff.mp (start.ready.exportsReady start.authority))
  obtain ⟨requiredOutput, exports⟩ := call.checkpoint.output_succeeded_uniform
    start.atCheckpoint atRecipe checkpointRegistry checkpointReady requested shape
  refine ⟨requiredExecution, max requiredOutput 1, ?_⟩
  intro executionFuel outputFuel outcome executionBound outputBound resumed
  obtain ⟨completion, actual, generation, succeeded, exported, actualAt, returnedReady⟩ :=
    exports executionFuel (completes executionFuel executionBound) outputFuel (Nat.le_trans (Nat.le_max_left _ _) outputBound) outcome resumed
  have requestedRaw := requested
  obtain ⟨exportedCompletion, handle, sameOutcome, functionValue, handleType, _ready⟩ :=
    SourceCoreExecution.Checkpoint.ResumeAt.runtime_function_succeeded start.atCheckpoint resumed checkpointReady
      (completes executionFuel executionBound) requested functionResult (by omega)
  have sameCompletion : exportedCompletion = completion :=
    SourceCoreExecution.Outcome.succeeded.inj (sameOutcome.symm.trans succeeded)
  subst exportedCompletion
  let entry : RecursiveNamedPublicFunctionHistory.Entry :=
    ⟨header.function.resultType, source, handle, payload, header.output, outputFuel⟩
  obtain ⟨reached, related, post⟩ := result.2.2.2.2.2.2.2
  have retained := RecursiveNamedPublicFunctionHistory.History.first rfl start.started start.selected exported result
    reached ⟨related, post⟩
    (.remember requestedRaw rfl rfl (actualAt.1.symm.trans functionValue))
  have physicalRetained := RecursiveNamedPublicPhysicalHistory.physical_of_result caller.physical result
  have returnedRegistry := start.started.returned_registry exported
  rw [← receiverRegistry] at returnedRegistry
  let returned : State rows anchor initial support.profile recipe completion.session [entry] := {
    artifact := start.artifact
    session := actual.session
    mapping := finalMap
    world := finalWorld
    heap := after
    store := finalStore
    caller := reached
    atSession := actualAt.2.2.2
    atRecipe := start.started.recipe_eq
    receiving := receiving
    issued := receiverIssued
    extension := receiverExtension
    registry := returnedRegistry
    history := ⟨retained, physicalRetained⟩ }
  exact ⟨completion, succeeded, actualAt.2.2.2.exportsReady_iff.mpr returnedReady,
    entry, rfl, rfl, functionValue, handleType, returned, rfl⟩


end Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicSessionInitialDataForward
