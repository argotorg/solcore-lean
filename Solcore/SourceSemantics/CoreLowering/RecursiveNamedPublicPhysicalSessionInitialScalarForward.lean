import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicPhysicalSessionInitial
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicPhysicalSessionScalarForward

/-! An initial scalar call retains the real bootstrapped state with an empty
handle history. Independent Source success supplies both required budgets. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicPhysicalSessionInitialScalarForward
open Core Frontend SourceInference
open CallableIndexedOwnedPreparedFiniteNamedInventories (Input Inventory headers)
open CallableIndexedOwnedFunctionValues (Header)
open RecursiveNamedPublicScalarResults (ScalarOutput)
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

theorem first_scalar
    (distinct : (inputs.map (fun input => input.prepared.index)).Nodup)
    (scalar : ScalarOutput) (call : StartedCall session key publicArguments options)
    (start : Started rows prepared header call)
    (simple : ∀ value ∈ publicArguments, SourceCoreIndexedSession.SimplePublic value)
    (inputTypes : RecursiveNamedPublicDataArgumentReceipts.PublicDataTypes
      header.function.context publicArguments header.types)
    {arguments : List Dynamic.Value}
    (inputMeanings : RecursiveNamedPublicDataInputs.Meanings publicArguments arguments)
    (rawType : header.function.resultType = scalar.sourceType)
    (nativeType : header.output = scalar.nativeType)
    {invocation : Staging.Recursive.Scope} {after : Dynamic.Heap}
    (trace : SourceCall anchor header invocation ⟨[]⟩ arguments (.value scalar.source) after) :
    RecursiveNamedPublicPhysicalSessionScalarForward.ForwardAt (entries := [])
      rows anchor initial support.profile recipe scalar call after := by
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
  obtain ⟨payload, rfl⟩ : ∃ payload, value = .inRight .word payload := by
    have representedResult := result.2.1
    cases representedResult with
    | value represented => exact ⟨_, rfl⟩
  have completes : ∀ executionFuel, requiredExecution ≤ executionFuel →
      start.checkpoint.NativeDone executionFuel (.inRight .word payload) finalStore :=
    fun fuel bound => start.started.initial.native_done_iff.mpr (enough fuel bound)
  have representedResult : CompatiblePayload.ValueRep recipe.compiled.compatible.checked
      initial.result.context.registry (CallableIndexedOwnedPreparedPhysicalProgramSupport.functions support)
      finalMap finalWorld header.function.resultType scalar.source payload header.output := by
    have representedResult := result.2.1
    cases representedResult with
    | value related => exact related
  have nativeScalar : payload = scalar.native := by
    rw [nativeType] at representedResult
    exact scalar.native_value representedResult
  have shape : SourceCorePublicOutputShapes.Output recipe.compiled.compatible.checked start.encodedValues.registry
      (finalStore.map Core.Value.type) recipe.program.layouts.definitions header.function.resultType payload := by
    have shaped := CompatiblePublicOutputShapes.ValueRep.output representedResult
    rw [support.registry, ← startupRegistry] at shaped
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
  refine ⟨requiredExecution, requiredOutput, ?_⟩
  intro executionFuel outputFuel outcome executionBound outputBound resumed
  obtain ⟨completion, actual, generation, succeeded, exported, actualAt, returnedReady⟩ :=
    exports executionFuel (completes executionFuel executionBound) outputFuel outputBound outcome resumed
  obtain ⟨reached, related, post⟩ := result.2.2.2.2.2.2.2
  have retained := RecursiveNamedPublicFunctionHistory.History.first rfl start.started start.selected exported result
    reached ⟨related, post⟩
    .skip
  have physicalRetained := RecursiveNamedPublicPhysicalHistory.physical_of_result caller.physical result
  have returnedRegistry := start.started.returned_registry exported
  rw [startupRegistry, ← support.registry] at returnedRegistry
  let returned : State rows anchor initial support.profile recipe completion.session [] := {
    artifact := start.artifact
    session := actual.session
    mapping := finalMap
    world := finalWorld
    heap := after
    store := finalStore
    caller := reached
    atSession := actualAt.2.2.2
    atRecipe := start.started.recipe_eq
    receiving := initial
    issued := support.issued
    extension := .refl _
    registry := returnedRegistry
    history := ⟨retained, physicalRetained⟩ }
  rw [rawType] at requested
  exact ⟨completion, succeeded, actualAt.1.trans (scalar.succeeded_value (nativeScalar ▸ exported) requested),
    actualAt.2.2.2.exportsReady_iff.mpr returnedReady, returned, rfl⟩


end Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicPhysicalSessionInitialScalarForward
