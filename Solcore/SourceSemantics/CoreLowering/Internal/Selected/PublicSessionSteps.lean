import Solcore.SourceSemantics.CoreLowering.PublicSessions
import Solcore.SourceSemantics.CoreLowering.Internal.Selected.NamedAdmission
import Solcore.SourceSemantics.CoreLowering.Internal.Selected.PublicDirectSessions
import Solcore.SourceSemantics.CoreLowering.PublicSupport
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.PublicArgumentReceipts
import Solcore.SourceSemantics.CoreLowering.Internal.Selected.PublicDirectBounds
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.PhysicalPublic
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.PublicInputRegistries
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.PublicDirectHistories
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.PublicActualRegistry
import Solcore.SourceSemantics.Staging.Preservation

/-!
# Selected compilations: public session steps

One step of a public session for each outcome: scalar, function, failure and export, in forward and step form, at the first call and at registry-extending calls.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicInitialReceiver
/-! The initial public encoder can extend the static metadata registry. Its
actual returned context supplies the first diagnostic receiver, including for
mapping, constructor and proxy arguments. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicInitialReceiver
open Core Frontend SourceInference
open CallableIndexedOwnedPreparedFiniteNamedInventories (Input Inventory headers)
open CallableIndexedOwnedFunctionValues (Header)
open CallableIndexedOwnedPreparedBootstrapRootState (keys)
open SelectedCompilationPublicSessionState (StartedCall)
open SelectedCompilationPublicSessionInitial (Started)
open SelectedCompilationPhysicalProgramSupport (Support)

variable {recipe : SourceCoreIndexedSession.Recipe}
  {inputs : List (Input recipe.compiled)} {rows : Inventory inputs}
  {prepared : SourceCoreIndexedSession.Recipe.prepare recipe.compiled = .ok recipe}
  {header : Header recipe.compiled (Program.ofChecked recipe.compiled.sourceProgram)}
  {initial : CallableIndexedOwnedPublicFaultReceivers.Receiver recipe.compiled.indexed}
  {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
  {key : SourceCoreIndexedSession.Key} {arguments : List SourceCorePublicValues.Value}
  {options : SourceCoreExecution.RunOptions} {call : StartedCall session key arguments options}

theorem of_started (support : Support recipe.compiled (headers rows) (keys recipe.compiled) initial)
    (start : Started rows prepared header call) :
    ∃ receiving : CallableIndexedOwnedPublicFaultReceivers.Receiver recipe.compiled.indexed,
      receiving.result.context = start.encodedValues ∧
      CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt recipe.compiled.indexed receiving.entry
        receiving.result.context.registry receiving.result.extension receiving.result.diagnostics ∧
      SourceCoreRawMetadata.Extends initial.result.context.registry receiving.result.context.registry := by
  obtain ⟨receiving, _entry, contextAt, issued⟩ :=
    CallableIndexedOwnedPublicFaultReceivers.Receiver.at_context recipe.compiled initial.entry
      start.encodedValues start.started.owner
  refine ⟨receiving, contextAt, issued, ?_⟩
  rw [support.registry]
  exact receiving.result.extension

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicInitialReceiver
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicSessionScalarForward
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicSessionScalarForward
open Core Frontend SourceInference
open CallableIndexedOwnedPreparedFiniteNamedInventories (Input Inventory headers)
open CallableIndexedOwnedPreparedBootstrapRootState (keys)
open CallableIndexedOwnedFunctionValues (Header)
open SelectedCompilationPublicSessionState
open RecursiveNamedPublicScalarResults (ScalarOutput)
open SelectedCompilationPhysicalProgramSupport (stagePrepared)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {inputs : List (Input compiled)} {rows : Inventory inputs}
  {anchor : Header compiled (Program.ofChecked compiled.sourceProgram)}
  {initial : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
  {profile : compiled.compatible.checked.catalog.callableContracts = true}
  {recipe : SourceCoreIndexedSession.Recipe}

def ForwardAt (rows : Inventory inputs) (anchor : Header compiled (Program.ofChecked compiled.sourceProgram))
    (initial : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed)
    (profile : compiled.compatible.checked.catalog.callableContracts = true) (recipe : SourceCoreIndexedSession.Recipe)
    {options : SourceCoreExecution.RunOptions}
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    {entries : List RecursiveNamedPublicFunctionHistory.Entry}
    {key : SourceCoreIndexedSession.Key} {arguments : List SourceCorePublicValues.Value}
    (scalar : ScalarOutput) (call : StartedCall session key arguments options)
    (after : Dynamic.Heap) : Prop :=
  ∃ requiredExecution requiredOutput,
    ∀ executionFuel outputFuel (outcome : SourceCoreExecution.Outcome artifact),
      requiredExecution ≤ executionFuel → requiredOutput ≤ outputFuel →
      call.checkpoint.ResumeAt executionFuel outputFuel outcome →
      ∃ completion : SourceCoreExecution.Completion artifact,
        outcome = .succeeded completion ∧ completion.value = scalar.publicValue ∧
        completion.session.ExportsReady ∧
        ∃ returned : State rows anchor initial profile recipe completion.session entries, returned.heap = after

theorem forward_call (support : SelectedCompilationPhysicalProgramSupport.Support compiled (headers rows) (keys compiled) initial)
    (prepared : SourceCoreIndexedSession.Recipe.prepare compiled = .ok recipe)
    {options : SourceCoreExecution.RunOptions}
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    {entries : List RecursiveNamedPublicFunctionHistory.Entry}
    (state : State rows anchor initial profile recipe session entries)
    {key : SourceCoreIndexedSession.Key} {publicArguments : List SourceCorePublicValues.Value}
    (scalar : ScalarOutput) (call : StartedCall session key publicArguments options)
    (request : RecursiveNamedPublicHistoryFrontdoor.Started (headers rows) prepared
      call.checkpoint state.session key publicArguments options.inputValidationFuel state.world state.store)
    {arguments : List Dynamic.Value}
    (inputs : RecursiveNamedPublicFunctionHistoryInputs.Inputs entries request.header.function.context
      (request.header.bindings.map (fun binding => binding.1.scheme.body)) publicArguments arguments)
    (registry : request.encodedValues.registry = state.receiving.result.context.registry)
    (rawType : request.header.function.resultType = scalar.sourceType)
    (nativeType : request.header.output = scalar.nativeType)
    (ready : session.ExportsReady)
    {invocation : Staging.Recursive.Scope} {after : Dynamic.Heap}
    (trace : SourceCall anchor request.header invocation state.heap arguments (.value scalar.source) after) :
    ForwardAt (entries := entries) rows anchor initial profile recipe scalar call after := by
  have sameCompiled := SourceCoreIndexedSession.Recipe.prepare_compiled prepared
  cases sameCompiled
  have metadata : SourceCoreRawMetadata.Extends request.encodedValues.registry state.receiving.result.context.registry := by
    rw [registry]; exact .refl _
  obtain ⟨stable, heaps, heapTyped, represented, argumentsTyped⟩ :=
    SelectedCompilationPublicClosureHistory.History.current_arguments
      (profile := profile)
      (bodyTyping := support.bodyTyping) (prepared := prepared)
      (selected := request.selected) (history := state.history)
      (started := request.started) (inputReceipts := inputs) (metadata := metadata)
  have globalReference := CallableIndexedOwnedPreparedBootstrapGlobalReferences.global_reference
    rows request.header request.selected.member
  have supports := (SelectedCompilationPublicReturnedValues.header_context_supports
    request.header anchor support.bodyTyping).2
  obtain ⟨rawD, function, sourceSize, sourceAt, applied⟩ := trace
  obtain ⟨capture, value, finalStore, finalMap, finalWorld, requiredExecution, enough, result⟩ :=
    SelectedCompilationPublicBodyInvocationBounds.preserves_root
      (stagePrepared := stagePrepared recipe.compiled) (completion := state.receiving)
      (functions := functions rows initial profile)
      (owner := CallableIndexedOwnedPreparedBootstrapRootState.owner recipe.compiled)
      (packet := support.bodies request.header request.selected.member) (preservesBodies := fun budget {child} selected =>
        SelectedCompilationPhysicalProgramSupport.preserves_bodies support state.issued
          state.extension request.header request.selected.member selected budget)
      (keyPhysical := CallableIndexedOwnedPreparedPhysicalBootstrap.key_physical _ _)
      (physical := state.history.physical)
      (bodyTyping := support.bodyTyping)
      (selected := request.selected) (caller := state.caller)
      (globalReference := globalReference) (stable := stable) (heapTyped := heapTyped)
      (represented := represented) (argumentsTyped := argumentsTyped) (heaps := heaps)
      (sourceAt := sourceAt) (supports := supports) applied
  obtain ⟨payload, rfl⟩ : ∃ payload, value = .inRight .word payload := by
    have representedResult := result.2.1
    cases representedResult with
    | value represented => exact ⟨_, rfl⟩
  have completes : ∀ executionFuel, requiredExecution ≤ executionFuel →
      request.checkpoint.NativeDone executionFuel (.inRight .word payload) finalStore :=
    fun fuel bound => request.started.initial.native_done_iff.mpr (enough fuel bound)
  have representedResult : CompatiblePayload.ValueRep recipe.compiled.compatible.checked
      state.receiving.result.context.registry (functions rows initial profile)
      finalMap finalWorld request.header.function.resultType scalar.source payload request.header.output := by
    have representedResult := result.2.1
    cases representedResult with
    | value related => exact related
  have nativeScalar : payload = scalar.native := by
    rw [nativeType] at representedResult
    exact scalar.native_value representedResult
  have shape : SourceCorePublicOutputShapes.Output recipe.compiled.compatible.checked request.encodedValues.registry
      (finalStore.map Core.Value.type) recipe.program.layouts.definitions request.header.function.resultType payload := by
    have shaped := CompatiblePublicOutputShapes.ValueRep.output representedResult
    rw [← registry] at shaped
    rw [result.2.2.1.runtime_hasTypes.world_eq] at shaped
    exact shaped
  have checkpointRegistry : request.checkpoint.RegistryAt request.encodedValues.registry := by
    have atValues := request.started.values
    generalize checkpointEq : request.checkpoint = checkpoint at atValues ⊢
    cases checkpoint
    change _ = request.encodedValues at atValues
    exact congrArg SourceCoreCompatibleValues.Context.registry atValues
  have atRecipe : state.artifact.RecipeAt recipe := by
    have convert : ∀ (artifact : SourceCoreIndexedSession.Artifact) (recipe : SourceCoreIndexedSession.Recipe),
        RecursiveNamedPublicStartMeaning.ArtifactRecipe artifact recipe → artifact.RecipeAt recipe :=
      fun artifact _ atRecipe => by cases artifact; exact atRecipe
    exact convert _ _ state.atRecipe
  have requested := request.started.original.result_type_at atRecipe request.started.selected
  have resultType := (RecursiveNamedPublicRootSourceSignature.inputs_and_result request.selected).2
  rw [resultType] at requested
  have checkpointReady := request.started.original.initial_registry.exportsReady (state.atSession.exportsReady_iff.mp ready)
  obtain ⟨requiredOutput, exports⟩ := call.checkpoint.output_succeeded_uniform
    request.atCheckpoint atRecipe checkpointRegistry checkpointReady requested shape
  refine ⟨requiredExecution, requiredOutput, ?_⟩
  intro executionFuel outputFuel outcome executionBound outputBound resumed
  obtain ⟨completion, actual, generation, succeeded, exported, actualAt, returnedReady⟩ :=
    exports executionFuel (completes executionFuel executionBound) outputFuel outputBound outcome resumed
  obtain ⟨reached, _related, retained⟩ := state.history.semantic.after_success
    (SourceCoreIndexedSession.Recipe.prepare_compiled prepared) request.started request.selected exported result
  have physicalRetained := state.history.after_result result retained
  have returnedRegistry := request.started.returned_registry exported
  rw [registry] at returnedRegistry
  let returned : State rows anchor initial profile recipe completion.session entries := {
    artifact := state.artifact
    session := actual.session
    mapping := finalMap
    world := finalWorld
    heap := after
    store := finalStore
    caller := reached
    atSession := actualAt.2.2.2
    atRecipe := state.atRecipe
    receiving := state.receiving
    issued := state.issued
    extension := state.extension
    registry := returnedRegistry
    history := physicalRetained }
  rw [rawType] at requested
  exact ⟨completion, succeeded, actualAt.1.trans (scalar.succeeded_value (nativeScalar ▸ exported) requested),
    actualAt.2.2.2.exportsReady_iff.mpr returnedReady, returned, rfl⟩

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicSessionScalarForward
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicSessionRegistryScalarForward
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicSessionScalarForward
open Core Frontend SourceInference
open CallableIndexedOwnedPreparedFiniteNamedInventories (Input Inventory headers)
open CallableIndexedOwnedPreparedBootstrapRootState (keys)
open CallableIndexedOwnedFunctionValues (Header)
open SelectedCompilationPublicSessionState
open RecursiveNamedPublicScalarResults (ScalarOutput)
open SelectedCompilationPhysicalProgramSupport (stagePrepared)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {inputs : List (Input compiled)} {rows : Inventory inputs}
  {anchor : Header compiled (Program.ofChecked compiled.sourceProgram)}
  {initial : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
  {profile : compiled.compatible.checked.catalog.callableContracts = true}
  {recipe : SourceCoreIndexedSession.Recipe}
theorem forward_call_at_input_registry (support : SelectedCompilationPhysicalProgramSupport.Support compiled (headers rows) (keys compiled) initial)
    (prepared : SourceCoreIndexedSession.Recipe.prepare compiled = .ok recipe)
    {options : SourceCoreExecution.RunOptions}
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    {entries : List RecursiveNamedPublicFunctionHistory.Entry}
    (state : State rows anchor initial profile recipe session entries)
    {key : SourceCoreIndexedSession.Key} {publicArguments : List SourceCorePublicValues.Value}
    (scalar : ScalarOutput) (call : StartedCall session key publicArguments options)
    (request : RecursiveNamedPublicHistoryFrontdoor.Started (headers rows) prepared
      call.checkpoint state.session key publicArguments options.inputValidationFuel state.world state.store)
    {arguments : List Dynamic.Value}
    (inputs : RecursiveNamedPublicFunctionHistoryInputs.Inputs entries request.header.function.context
      (request.header.bindings.map (fun binding => binding.1.scheme.body)) publicArguments arguments)
    (rawType : request.header.function.resultType = scalar.sourceType)
    (nativeType : request.header.output = scalar.nativeType)
    (ready : session.ExportsReady)
    {invocation : Staging.Recursive.Scope} {after : Dynamic.Heap}
    (trace : SourceCall anchor request.header invocation state.heap arguments (.value scalar.source) after) :
    ForwardAt (entries := entries) rows anchor initial profile recipe scalar call after := by
  have sameCompiled := SourceCoreIndexedSession.Recipe.prepare_compiled prepared
  cases sameCompiled
  obtain ⟨receiving, contextAt, issued, extension, history⟩ := state.at_named_request prepared request
  have registry : request.encodedValues.registry = receiving.result.context.registry :=
    (congrArg SourceCoreCompatibleValues.Context.registry contextAt).symm
  have metadata : SourceCoreRawMetadata.Extends request.encodedValues.registry receiving.result.context.registry := by
    rw [registry]; exact .refl _
  obtain ⟨stable, heaps, heapTyped, represented, argumentsTyped⟩ :=
    SelectedCompilationPublicClosureHistory.History.current_arguments
      (profile := profile)
      (bodyTyping := support.bodyTyping) (prepared := prepared)
      (selected := request.selected) (history := history)
      (started := request.started) (inputReceipts := inputs) (metadata := metadata)
  have globalReference := CallableIndexedOwnedPreparedBootstrapGlobalReferences.global_reference
    rows request.header request.selected.member
  have supports := (SelectedCompilationPublicReturnedValues.header_context_supports
    request.header anchor support.bodyTyping).2
  obtain ⟨rawD, function, sourceSize, sourceAt, applied⟩ := trace
  obtain ⟨capture, value, finalStore, finalMap, finalWorld, requiredExecution, enough, result⟩ :=
    SelectedCompilationPublicBodyInvocationBounds.preserves_root
      (stagePrepared := stagePrepared recipe.compiled) (completion := receiving)
      (functions := functions rows initial profile)
      (owner := CallableIndexedOwnedPreparedBootstrapRootState.owner recipe.compiled)
      (packet := support.bodies request.header request.selected.member) (preservesBodies := fun budget {child} selected =>
        SelectedCompilationPhysicalProgramSupport.preserves_bodies support issued
          extension request.header request.selected.member selected budget)
      (keyPhysical := CallableIndexedOwnedPreparedPhysicalBootstrap.key_physical _ _)
      (physical := history.physical)
      (bodyTyping := support.bodyTyping)
      (selected := request.selected) (caller := state.caller)
      (globalReference := globalReference) (stable := stable) (heapTyped := heapTyped)
      (represented := represented) (argumentsTyped := argumentsTyped) (heaps := heaps)
      (sourceAt := sourceAt) (supports := supports) applied
  obtain ⟨payload, rfl⟩ : ∃ payload, value = .inRight .word payload := by
    have representedResult := result.2.1
    cases representedResult with
    | value represented => exact ⟨_, rfl⟩
  have completes : ∀ executionFuel, requiredExecution ≤ executionFuel →
      request.checkpoint.NativeDone executionFuel (.inRight .word payload) finalStore :=
    fun fuel bound => request.started.initial.native_done_iff.mpr (enough fuel bound)
  have representedResult : CompatiblePayload.ValueRep recipe.compiled.compatible.checked
      receiving.result.context.registry (functions rows initial profile)
      finalMap finalWorld request.header.function.resultType scalar.source payload request.header.output := by
    have representedResult := result.2.1
    cases representedResult with
    | value related => exact related
  have nativeScalar : payload = scalar.native := by
    rw [nativeType] at representedResult
    exact scalar.native_value representedResult
  have shape : SourceCorePublicOutputShapes.Output recipe.compiled.compatible.checked request.encodedValues.registry
      (finalStore.map Core.Value.type) recipe.program.layouts.definitions request.header.function.resultType payload := by
    have shaped := CompatiblePublicOutputShapes.ValueRep.output representedResult
    rw [← registry] at shaped
    rw [result.2.2.1.runtime_hasTypes.world_eq] at shaped
    exact shaped
  have checkpointRegistry : request.checkpoint.RegistryAt request.encodedValues.registry := by
    have atValues := request.started.values
    generalize checkpointEq : request.checkpoint = checkpoint at atValues ⊢
    cases checkpoint
    change _ = request.encodedValues at atValues
    exact congrArg SourceCoreCompatibleValues.Context.registry atValues
  have atRecipe : state.artifact.RecipeAt recipe := by
    have convert : ∀ (artifact : SourceCoreIndexedSession.Artifact) (recipe : SourceCoreIndexedSession.Recipe),
        RecursiveNamedPublicStartMeaning.ArtifactRecipe artifact recipe → artifact.RecipeAt recipe :=
      fun artifact _ atRecipe => by cases artifact; exact atRecipe
    exact convert _ _ state.atRecipe
  have requested := request.started.original.result_type_at atRecipe request.started.selected
  have resultType := (RecursiveNamedPublicRootSourceSignature.inputs_and_result request.selected).2
  rw [resultType] at requested
  have checkpointReady := request.started.original.initial_registry.exportsReady (state.atSession.exportsReady_iff.mp ready)
  obtain ⟨requiredOutput, exports⟩ := call.checkpoint.output_succeeded_uniform
    request.atCheckpoint atRecipe checkpointRegistry checkpointReady requested shape
  refine ⟨requiredExecution, requiredOutput, ?_⟩
  intro executionFuel outputFuel outcome executionBound outputBound resumed
  obtain ⟨completion, actual, generation, succeeded, exported, actualAt, returnedReady⟩ :=
    exports executionFuel (completes executionFuel executionBound) outputFuel outputBound outcome resumed
  obtain ⟨reached, _related, retained⟩ := history.semantic.after_success
    (SourceCoreIndexedSession.Recipe.prepare_compiled prepared) request.started request.selected exported result
  have physicalRetained := history.after_result result retained
  have returnedRegistry := request.started.returned_registry exported
  rw [registry] at returnedRegistry
  let returned : State rows anchor initial profile recipe completion.session entries := {
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
    extension := extension
    registry := returnedRegistry
    history := physicalRetained }
  rw [rawType] at requested
  exact ⟨completion, succeeded, actualAt.1.trans (scalar.succeeded_value (nativeScalar ▸ exported) requested),
    actualAt.2.2.2.exportsReady_iff.mpr returnedReady, returned, rfl⟩


end Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicSessionScalarForward
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicSessionInitialDataForward
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
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicSessionInitialDataScalarForward
/-! An initial scalar call retains the real bootstrapped state with an empty
handle history. Independent Source success supplies both required budgets. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicSessionInitialDataScalarForward
open Core Frontend SourceInference
open CallableIndexedOwnedPreparedFiniteNamedInventories (Input Inventory headers)
open CallableIndexedOwnedFunctionValues (Header)
open RecursiveNamedPublicScalarResults (ScalarOutput)
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

theorem first_scalar
    (distinct : (inputs.map (fun input => input.prepared.index)).Nodup)
    (scalar : ScalarOutput) (call : StartedCall session key publicArguments options)
    (start : Started rows prepared header call)
    (inputTypes : RecursiveNamedPublicDataArgumentReceipts.PublicDataTypes
      header.function.context publicArguments header.types)
    {arguments : List Dynamic.Value}
    (inputMeanings : RecursiveNamedPublicDataInputs.Meanings publicArguments arguments)
    (rawType : header.function.resultType = scalar.sourceType)
    (nativeType : header.output = scalar.nativeType)
    {invocation : Staging.Recursive.Scope} {after : Dynamic.Heap}
    (trace : SourceCall anchor header invocation ⟨[]⟩ arguments (.value scalar.source) after) :
    SelectedCompilationPublicSessionScalarForward.ForwardAt (entries := [])
      rows anchor initial support.profile recipe scalar call after := by
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
  rw [← receiverRegistry] at returnedRegistry
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
    receiving := receiving
    issued := receiverIssued
    extension := receiverExtension
    registry := returnedRegistry
    history := ⟨retained, physicalRetained⟩ }
  rw [rawType] at requested
  exact ⟨completion, succeeded, actualAt.1.trans (scalar.succeeded_value (nativeScalar ▸ exported) requested),
    actualAt.2.2.2.exportsReady_iff.mpr returnedReady, returned, rfl⟩


end Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicSessionInitialDataScalarForward
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicSessionFailureForward
/-! An independent Source fault determines every sufficiently fueled public
failure. The actual failed session retains the reached heap, complete physical
cache and prior exported handles. Output validation fuel is unrestricted. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicSessionFailureForward
open Core Frontend SourceInference
open CallableIndexedOwnedPreparedFiniteNamedInventories (Input Inventory headers)
open CallableIndexedOwnedPreparedBootstrapRootState (keys)
open CallableIndexedOwnedFunctionValues (Header)
open SelectedCompilationPublicSessionState
open SelectedCompilationPhysicalProgramSupport (stagePrepared)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {inputs : List (Input compiled)} {rows : Inventory inputs}
  {anchor : Header compiled (Program.ofChecked compiled.sourceProgram)}
  {initial : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
  {profile : compiled.compatible.checked.catalog.callableContracts = true}
  {recipe : SourceCoreIndexedSession.Recipe}

def FailureForwardAt (rows : Inventory inputs) (anchor : Header compiled (Program.ofChecked compiled.sourceProgram))
    (initial : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed)
    (profile : compiled.compatible.checked.catalog.callableContracts = true) (recipe : SourceCoreIndexedSession.Recipe)
    {options : SourceCoreExecution.RunOptions}
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    {entries : List RecursiveNamedPublicFunctionHistory.Entry}
    {key : SourceCoreIndexedSession.Key} {arguments : List SourceCorePublicValues.Value}
    (failure : Staging.Recursive.Failure) (call : StartedCall session key arguments options)
    (after : Dynamic.Heap) : Prop :=
  ∃ requiredExecution token,
    ∀ executionFuel outputFuel (outcome : SourceCoreExecution.Outcome artifact),
      requiredExecution ≤ executionFuel → call.checkpoint.ResumeAt executionFuel outputFuel outcome →
      ∃ returned : SourceCoreExecution.Session artifact,
        outcome = .failed token returned ∧ returned.ExportsReady ∧
        ∃ next : State rows anchor initial profile recipe returned entries,
          next.heap = after ∧
          CallableIndexedOwnedPublicDecodedStagedCallFaults.faults next.receiving.result.diagnostics failure token

theorem forward_call (support : SelectedCompilationPhysicalProgramSupport.Support compiled (headers rows) (keys compiled) initial)
    (selectedBodies : Staging.Recursive.SelectedPreservation.SelectedBodies
      (Program.ofChecked compiled.sourceProgram)
      (SelectedCompilationPhysicalProgramSupport.stages compiled))
    (prepared : SourceCoreIndexedSession.Recipe.prepare compiled = .ok recipe)
    {options : SourceCoreExecution.RunOptions}
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    {entries : List RecursiveNamedPublicFunctionHistory.Entry}
    (state : State rows anchor initial profile recipe session entries)
    {key : SourceCoreIndexedSession.Key} {publicArguments : List SourceCorePublicValues.Value}
    (call : StartedCall session key publicArguments options)
    (request : RecursiveNamedPublicHistoryFrontdoor.Started (headers rows) prepared
      call.checkpoint state.session key publicArguments options.inputValidationFuel state.world state.store)
    {arguments : List Dynamic.Value}
    (inputs : RecursiveNamedPublicFunctionHistoryInputs.Inputs entries request.header.function.context
      (request.header.bindings.map (fun binding => binding.1.scheme.body)) publicArguments arguments)
    (registry : request.encodedValues.registry = state.receiving.result.context.registry)
    (ready : session.ExportsReady)
    {invocation : Staging.Recursive.Scope} {after : Dynamic.Heap} {failure : Staging.Recursive.Failure}
    (trace : SourceCall anchor request.header invocation state.heap arguments (.fault failure) after) :
    FailureForwardAt (entries := entries) rows anchor initial profile recipe failure call after := by
  have sameCompiled := SourceCoreIndexedSession.Recipe.prepare_compiled prepared
  cases sameCompiled
  have metadata : SourceCoreRawMetadata.Extends request.encodedValues.registry state.receiving.result.context.registry := by
    rw [registry]; exact .refl _
  obtain ⟨stable, heaps, heapTyped, represented, argumentsTyped⟩ :=
    SelectedCompilationPublicClosureHistory.History.current_arguments
      (profile := profile)
      (bodyTyping := support.bodyTyping) (prepared := prepared)
      (selected := request.selected) (history := state.history)
      (started := request.started) (inputReceipts := inputs) (metadata := metadata)
  have globalReference := CallableIndexedOwnedPreparedBootstrapGlobalReferences.global_reference
    rows request.header request.selected.member
  have supports := (SelectedCompilationPublicReturnedValues.header_context_supports
    request.header anchor support.bodyTyping).2
  obtain ⟨rawD, function, sourceSize, sourceAt, applied⟩ := trace
  obtain ⟨capture, value, finalStore, finalMap, finalWorld, requiredExecution, enough, result⟩ :=
    SelectedCompilationPublicBodyInvocationBounds.preserves_root
      (stagePrepared := stagePrepared recipe.compiled) (completion := state.receiving)
      (functions := functions rows initial profile)
      (owner := CallableIndexedOwnedPreparedBootstrapRootState.owner recipe.compiled)
      (packet := support.bodies request.header request.selected.member) (preservesBodies := fun budget {child} selected =>
        SelectedCompilationPhysicalProgramSupport.preserves_bodies support state.issued
          state.extension request.header request.selected.member selected budget)
      (keyPhysical := CallableIndexedOwnedPreparedPhysicalBootstrap.key_physical _ _)
      (physical := state.history.physical)
      (bodyTyping := support.bodyTyping)
      (selected := request.selected) (caller := state.caller)
      (globalReference := globalReference) (stable := stable) (heapTyped := heapTyped)
      (represented := represented) (argumentsTyped := argumentsTyped) (heaps := heaps)
      (sourceAt := sourceAt) (supports := supports) applied
  obtain ⟨token, rfl, faultRelated⟩ : ∃ token,
      value = .inLeft request.header.output (.word token) ∧
      CallableIndexedOwnedPublicDecodedStagedCallFaults.faults state.receiving.result.diagnostics failure token := by
    have related := result.2.1
    cases related with
    | fault related => exact ⟨_, rfl, related⟩
  have completes : ∀ executionFuel, requiredExecution ≤ executionFuel →
      request.checkpoint.NativeDone executionFuel (.inLeft request.header.output (.word token)) finalStore :=
    fun fuel bound => request.started.initial.native_done_iff.mpr (enough fuel bound)
  have contextSupports := (SelectedCompilationPublicReturnedValues.header_context_supports
    request.header anchor support.bodyTyping).1
  have callerHeap := heapTyped.transportContext contextSupports
  have callerArguments := argumentsTyped.transportContext contextSupports
  obtain ⟨packed, packing⟩ := Dynamic.ValuesPack.exists_pack arguments
  have preserved := Staging.Recursive.SelectedPreservation.applies_fault selectedBodies
    (SelectedCompilationPublicHistorySourceInputs.header_runtime support.bodyTyping anchor) callerHeap
    (SelectedCompilationPublicHistorySourceInputs.source_typed support.bodyTyping sourceAt anchor state.heap)
    packing (packing.hasType callerArguments) applied
  have checkpointReady := request.started.original.initial_registry.exportsReady (state.atSession.exportsReady_iff.mp ready)
  refine ⟨requiredExecution, token, ?_⟩
  intro executionFuel outputFuel outcome executionBound resumed
  have completed := completes executionFuel executionBound
  obtain ⟨returned, outcomeEq⟩ := resumed.native_failed request.atCheckpoint completed rfl
  have failedResume : call.checkpoint.ResumeAt executionFuel outputFuel (.failed token returned) := outcomeEq ▸ resumed
  obtain ⟨actual, _generation, actualValue, actualStore, actualCompleted, failed, returnedAt⟩ :=
    failedResume.indexed_failed request.atCheckpoint
  have same := completed.symm.trans actualCompleted
  cases same
  obtain ⟨reached, _related, retained⟩ := state.history.semantic.after_failure
    rfl request.started request.selected failed result preserved.1
  have physicalRetained := state.history.after_result result retained
  have returnedRegistry : actual.RegistryAt state.receiving.result.context.registry := by
    rw [← registry]
    exact congrArg SourceCoreCompatibleValues.Context.registry (failed.2.2.2.2.1.trans request.started.values)
  let next : State rows anchor initial profile recipe returned entries := {
    artifact := state.artifact
    session := actual
    mapping := finalMap
    world := finalWorld
    heap := after
    store := finalStore
    caller := reached
    atSession := returnedAt
    atRecipe := state.atRecipe
    receiving := state.receiving
    issued := state.issued
    extension := state.extension
    registry := returnedRegistry
    history := physicalRetained }
  exact ⟨returned, outcomeEq, returnedAt.exportsReady_iff.mpr (failed.exportsReady checkpointReady),
    next, rfl, faultRelated⟩

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicSessionFailureForward
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicSessionInitialDataFailureForward
/-! An initial Source fault supplies sufficient execution fuel and retains the
exact failed session, decoded reason and physical state with no handles. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicSessionInitialDataFailureForward
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
  (selectedBodies : Staging.Recursive.SelectedPreservation.SelectedBodies
    (Program.ofChecked recipe.compiled.sourceProgram)
    (SelectedCompilationPhysicalProgramSupport.stages recipe.compiled))
  {publicArtifact : SourceCoreExecution.Artifact}
  {session : SourceCoreExecution.Session publicArtifact}
  {key : SourceCoreIndexedSession.Key} {publicArguments : List SourceCorePublicValues.Value}
  {options : SourceCoreExecution.RunOptions}

include selectedBodies in
theorem first_failure
    (distinct : (inputs.map (fun input => input.prepared.index)).Nodup)
    (call : StartedCall session key publicArguments options)
    (start : Started rows prepared header call)
    (inputTypes : RecursiveNamedPublicDataArgumentReceipts.PublicDataTypes
      header.function.context publicArguments header.types)
    {arguments : List Dynamic.Value}
    (inputMeanings : RecursiveNamedPublicDataInputs.Meanings publicArguments arguments)
    {invocation : Staging.Recursive.Scope} {after : Dynamic.Heap} {failure : Staging.Recursive.Failure}
    (trace : SourceCall anchor header invocation ⟨[]⟩ arguments (.fault failure) after) :
    SelectedCompilationPublicSessionFailureForward.FailureForwardAt (entries := [])
      rows anchor initial support.profile recipe failure call after := by
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
  obtain ⟨token, rfl, faultRelated⟩ : ∃ token,
      value = .inLeft header.output (.word token) ∧
      CallableIndexedOwnedPublicDecodedStagedCallFaults.faults receiving.result.diagnostics failure token := by
    have related := result.2.1
    cases related with
    | fault related => exact ⟨_, rfl, related⟩
  have completes : ∀ executionFuel, requiredExecution ≤ executionFuel →
      start.checkpoint.NativeDone executionFuel (.inLeft header.output (.word token)) finalStore :=
    fun fuel bound => start.started.initial.native_done_iff.mpr (enough fuel bound)
  have contextSupports := (SelectedCompilationPublicReturnedValues.header_context_supports
    header anchor support.bodyTyping).1
  have callerHeap := heapTyped.transportContext contextSupports
  have callerArguments := argumentsTyped.transportContext contextSupports
  obtain ⟨packed, packing⟩ := Dynamic.ValuesPack.exists_pack arguments
  have preserved := Staging.Recursive.SelectedPreservation.applies_fault selectedBodies
    (SelectedCompilationPublicHistorySourceInputs.header_runtime support.bodyTyping anchor) callerHeap
    (SelectedCompilationPublicHistorySourceInputs.source_typed support.bodyTyping sourceAt anchor ⟨[]⟩)
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
  have returnedRegistry : actual.RegistryAt receiving.result.context.registry := by
    have actualRegistry := congrArg SourceCoreCompatibleValues.Context.registry
      (failed.2.2.2.2.1.trans start.started.values)
    exact actualRegistry.trans receiverRegistry.symm
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
    receiving := receiving
    issued := receiverIssued
    extension := receiverExtension
    registry := returnedRegistry
    history := ⟨retained, physicalRetained⟩ }
  exact ⟨returned, outcomeEq, returnedAt.exportsReady_iff.mpr (failed.exportsReady checkpointReady),
    next, rfl, faultRelated⟩

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicSessionInitialDataFailureForward
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicSessionFunctionForward
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicSessionFunctionForward
open Core Frontend SourceInference
open CallableIndexedOwnedPreparedFiniteNamedInventories (Input Inventory headers)
open CallableIndexedOwnedPreparedBootstrapRootState (keys)
open CallableIndexedOwnedFunctionValues (Header)
open SelectedCompilationPublicSessionState
open RecursiveNamedPublicScalarResults (ScalarOutput)
open SelectedCompilationPhysicalProgramSupport (stagePrepared)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {inputs : List (Input compiled)} {rows : Inventory inputs}
  {anchor : Header compiled (Program.ofChecked compiled.sourceProgram)}
  {initial : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
  {profile : compiled.compatible.checked.catalog.callableContracts = true}
  {recipe : SourceCoreIndexedSession.Recipe}

def FunctionForwardAt (rows : Inventory inputs) (anchor : Header compiled (Program.ofChecked compiled.sourceProgram))
    (initial : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed)
    (profile : compiled.compatible.checked.catalog.callableContracts = true) (recipe : SourceCoreIndexedSession.Recipe)
    {options : SourceCoreExecution.RunOptions}
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    {entries : List RecursiveNamedPublicFunctionHistory.Entry}
    {key : SourceCoreIndexedSession.Key} {arguments : List SourceCorePublicValues.Value}
    (call : StartedCall session key arguments options)
    (parameterType resultType : TypeSystem.Ty) (source : Dynamic.Value)
    (after : Dynamic.Heap) : Prop :=
  ∃ requiredExecution requiredOutput,
    ∀ executionFuel outputFuel (outcome : SourceCoreExecution.Outcome artifact),
      requiredExecution ≤ executionFuel → requiredOutput ≤ outputFuel →
      call.checkpoint.ResumeAt executionFuel outputFuel outcome →
      ∃ completion : SourceCoreExecution.Completion artifact,
        outcome = .succeeded completion ∧ completion.session.ExportsReady ∧
        ∃ entry : RecursiveNamedPublicFunctionHistory.Entry,
          entry.sourceType = (.function parameterType resultType) ∧ entry.source = source ∧
          completion.value = .function entry.handle ∧ entry.handle.sourceType = (.function parameterType resultType) ∧
          ∃ returned : State rows anchor initial profile recipe completion.session (entries ++ [entry]),
            returned.heap = after

theorem forward_function (support : SelectedCompilationPhysicalProgramSupport.Support compiled (headers rows) (keys compiled) initial)
    (prepared : SourceCoreIndexedSession.Recipe.prepare compiled = .ok recipe)
    {options : SourceCoreExecution.RunOptions}
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    {entries : List RecursiveNamedPublicFunctionHistory.Entry}
    (state : State rows anchor initial profile recipe session entries)
    {key : SourceCoreIndexedSession.Key} {publicArguments : List SourceCorePublicValues.Value}
    (call : StartedCall session key publicArguments options)
    (request : RecursiveNamedPublicHistoryFrontdoor.Started (headers rows) prepared
      call.checkpoint state.session key publicArguments options.inputValidationFuel state.world state.store)
    {arguments : List Dynamic.Value}
    (inputs : RecursiveNamedPublicFunctionHistoryInputs.Inputs entries request.header.function.context
      (request.header.bindings.map (fun binding => binding.1.scheme.body)) publicArguments arguments)
    (registry : request.encodedValues.registry = state.receiving.result.context.registry)
    {parameterType resultType : TypeSystem.Ty}
    (rawType : request.header.function.resultType = (.function parameterType resultType))
    (ready : session.ExportsReady)
    {invocation : Staging.Recursive.Scope} {after : Dynamic.Heap} {source : Dynamic.Value}
    (trace : SourceCall anchor request.header invocation state.heap arguments (.value source) after) :
    FunctionForwardAt (entries := entries) rows anchor initial profile recipe call parameterType resultType source after := by
  have sameCompiled := SourceCoreIndexedSession.Recipe.prepare_compiled prepared
  cases sameCompiled
  have metadata : SourceCoreRawMetadata.Extends request.encodedValues.registry state.receiving.result.context.registry := by
    rw [registry]; exact .refl _
  obtain ⟨stable, heaps, heapTyped, represented, argumentsTyped⟩ :=
    SelectedCompilationPublicClosureHistory.History.current_arguments
      (profile := profile)
      (bodyTyping := support.bodyTyping) (prepared := prepared)
      (selected := request.selected) (history := state.history)
      (started := request.started) (inputReceipts := inputs) (metadata := metadata)
  have globalReference := CallableIndexedOwnedPreparedBootstrapGlobalReferences.global_reference
    rows request.header request.selected.member
  have supports := (SelectedCompilationPublicReturnedValues.header_context_supports
    request.header anchor support.bodyTyping).2
  obtain ⟨rawD, function, sourceSize, sourceAt, applied⟩ := trace
  obtain ⟨capture, value, finalStore, finalMap, finalWorld, requiredExecution, enough, result⟩ :=
    SelectedCompilationPublicBodyInvocationBounds.preserves_root
      (stagePrepared := stagePrepared recipe.compiled) (completion := state.receiving)
      (functions := functions rows initial profile)
      (owner := CallableIndexedOwnedPreparedBootstrapRootState.owner recipe.compiled)
      (packet := support.bodies request.header request.selected.member) (preservesBodies := fun budget {child} selected =>
        SelectedCompilationPhysicalProgramSupport.preserves_bodies support state.issued
          state.extension request.header request.selected.member selected budget)
      (keyPhysical := CallableIndexedOwnedPreparedPhysicalBootstrap.key_physical _ _)
      (physical := state.history.physical)
      (bodyTyping := support.bodyTyping)
      (selected := request.selected) (caller := state.caller)
      (globalReference := globalReference) (stable := stable) (heapTyped := heapTyped)
      (represented := represented) (argumentsTyped := argumentsTyped) (heaps := heaps)
      (sourceAt := sourceAt) (supports := supports) applied
  obtain ⟨payload, rfl⟩ : ∃ payload, value = .inRight .word payload := by
    have representedResult := result.2.1
    cases representedResult with
    | value represented => exact ⟨_, rfl⟩
  have completes : ∀ executionFuel, requiredExecution ≤ executionFuel →
      request.checkpoint.NativeDone executionFuel (.inRight .word payload) finalStore :=
    fun fuel bound => request.started.initial.native_done_iff.mpr (enough fuel bound)
  have representedResult : CompatiblePayload.ValueRep recipe.compiled.compatible.checked
      state.receiving.result.context.registry (functions rows initial profile)
      finalMap finalWorld request.header.function.resultType source payload request.header.output := by
    have representedResult := result.2.1
    cases representedResult with
    | value related => exact related
  have shape : SourceCorePublicOutputShapes.Output recipe.compiled.compatible.checked request.encodedValues.registry
      (finalStore.map Core.Value.type) recipe.program.layouts.definitions request.header.function.resultType payload := by
    have shaped := CompatiblePublicOutputShapes.ValueRep.output representedResult
    rw [← registry] at shaped
    rw [result.2.2.1.runtime_hasTypes.world_eq] at shaped
    exact shaped
  have checkpointRegistry : request.checkpoint.RegistryAt request.encodedValues.registry := by
    have atValues := request.started.values
    generalize checkpointEq : request.checkpoint = checkpoint at atValues ⊢
    cases checkpoint
    change _ = request.encodedValues at atValues
    exact congrArg SourceCoreCompatibleValues.Context.registry atValues
  have atRecipe : state.artifact.RecipeAt recipe := by
    have convert : ∀ (artifact : SourceCoreIndexedSession.Artifact) (recipe : SourceCoreIndexedSession.Recipe),
        RecursiveNamedPublicStartMeaning.ArtifactRecipe artifact recipe → artifact.RecipeAt recipe :=
      fun artifact _ atRecipe => by cases artifact; exact atRecipe
    exact convert _ _ state.atRecipe
  have requested := request.started.original.result_type_at atRecipe request.started.selected
  have selectedResult := (RecursiveNamedPublicRootSourceSignature.inputs_and_result request.selected).2
  rw [selectedResult] at requested
  have checkpointReady := request.started.original.initial_registry.exportsReady (state.atSession.exportsReady_iff.mp ready)
  obtain ⟨requiredOutput, exports⟩ := call.checkpoint.output_succeeded_uniform
    request.atCheckpoint atRecipe checkpointRegistry checkpointReady requested shape
  refine ⟨requiredExecution, max requiredOutput 1, ?_⟩
  intro executionFuel outputFuel outcome executionBound outputBound resumed
  obtain ⟨completion, actual, generation, succeeded, exported, actualAt, returnedReady⟩ :=
    exports executionFuel (completes executionFuel executionBound) outputFuel (Nat.le_trans (Nat.le_max_left _ _) outputBound) outcome resumed
  have requestedRaw := requested
  rw [rawType] at requested
  obtain ⟨exportedCompletion, handle, sameOutcome, functionValue, handleType, _ready⟩ :=
    SourceCoreExecution.Checkpoint.ResumeAt.runtime_function_succeeded request.atCheckpoint resumed checkpointReady
      (completes executionFuel executionBound) requested rfl (by omega)
  have sameCompletion : exportedCompletion = completion :=
    SourceCoreExecution.Outcome.succeeded.inj (sameOutcome.symm.trans succeeded)
  subst exportedCompletion
  let entry : RecursiveNamedPublicFunctionHistory.Entry :=
    ⟨request.header.function.resultType, source, handle, payload, request.header.output, outputFuel⟩
  obtain ⟨reached, related, post⟩ := result.2.2.2.2.2.2.2
  have retained := RecursiveNamedPublicFunctionHistory.History.next state.history.semantic
    (SourceCoreIndexedSession.Recipe.prepare_compiled prepared) request.started request.selected exported result reached ⟨related, post⟩
    (.remember requestedRaw rfl rfl (actualAt.1.symm.trans functionValue))
  have physicalRetained := state.history.after_result result retained
  have returnedRegistry := request.started.returned_registry exported
  rw [registry] at returnedRegistry
  let returned : State rows anchor initial profile recipe completion.session (entries ++ [entry]) := {
    artifact := state.artifact
    session := actual.session
    mapping := finalMap
    world := finalWorld
    heap := after
    store := finalStore
    caller := reached
    atSession := actualAt.2.2.2
    atRecipe := state.atRecipe
    receiving := state.receiving
    issued := state.issued
    extension := state.extension
    registry := returnedRegistry
    history := physicalRetained }
  exact ⟨completion, succeeded, actualAt.2.2.2.exportsReady_iff.mpr returnedReady,
    entry, rawType, rfl, functionValue, handleType, returned, rfl⟩

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicSessionFunctionForward
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicSessionExportForward
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicSessionExportForward
open Core Frontend SourceInference
open CallableIndexedOwnedPreparedFiniteNamedInventories (Input Inventory headers)
open CallableIndexedOwnedPreparedBootstrapRootState (keys)
open CallableIndexedOwnedFunctionValues (Header)
open SelectedCompilationPublicSessionState
open RecursiveNamedPublicScalarResults (ScalarOutput)
open SelectedCompilationPhysicalProgramSupport (stagePrepared)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {inputs : List (Input compiled)} {rows : Inventory inputs}
  {anchor : Header compiled (Program.ofChecked compiled.sourceProgram)}
  {initial : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
  {profile : compiled.compatible.checked.catalog.callableContracts = true}
  {recipe : SourceCoreIndexedSession.Recipe}
/-- The exact Source result reimports at the output validation budget used by
this resume. The state may retain only the pre-existing entry list. -/
def ReturnedValue
    {artifact : SourceCoreExecution.Artifact}
    (completion : SourceCoreExecution.Completion artifact) {entries : List RecursiveNamedPublicFunctionHistory.Entry}
    (state : State rows anchor initial profile recipe completion.session entries)
    (sourceType : TypeSystem.Ty) (source : Dynamic.Value) (fuel : Nat) : Prop :=
  ∃ payload nativeType,
    state.session.EncodesAt fuel sourceType completion.value payload ∧
    CompatiblePayload.ValueRep compiled.compatible.checked state.receiving.result.context.registry
      (functions rows initial profile) state.mapping state.world sourceType source payload nativeType

def ForwardAt (rows : Inventory inputs)
    (anchor : Header compiled (Program.ofChecked compiled.sourceProgram))
    (initial : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed)
    (profile : compiled.compatible.checked.catalog.callableContracts = true)
    (recipe : SourceCoreIndexedSession.Recipe)
    {artifact : SourceCoreExecution.Artifact} (entries : List RecursiveNamedPublicFunctionHistory.Entry)
    (checkpoint : SourceCoreExecution.Checkpoint artifact) (sourceType : TypeSystem.Ty)
    (source : Dynamic.Value) (after : Dynamic.Heap) : Prop :=
  ∃ requiredExecution requiredOutput,
    ∀ executionFuel outputFuel (outcome : SourceCoreExecution.Outcome artifact),
      requiredExecution ≤ executionFuel → requiredOutput ≤ outputFuel →
      checkpoint.ResumeAt executionFuel outputFuel outcome →
      ∃ completion : SourceCoreExecution.Completion artifact,
        outcome = .succeeded completion ∧
        ∃ handle, completion.value = .function handle ∧ handle.sourceType = sourceType ∧
        completion.session.ExportsReady ∧
        ∃ returned : State rows anchor initial profile recipe completion.session entries,
          returned.heap = after ∧ ReturnedValue completion returned sourceType source outputFuel

theorem forward_function_at_input_registry (support : SelectedCompilationPhysicalProgramSupport.Support compiled (headers rows) (keys compiled) initial)
    (prepared : SourceCoreIndexedSession.Recipe.prepare compiled = .ok recipe)
    {options : SourceCoreExecution.RunOptions}
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    {entries : List RecursiveNamedPublicFunctionHistory.Entry}
    (state : State rows anchor initial profile recipe session entries)
    {key : SourceCoreIndexedSession.Key} {publicArguments : List SourceCorePublicValues.Value}
    (call : StartedCall session key publicArguments options)
    (request : RecursiveNamedPublicHistoryFrontdoor.Started (headers rows) prepared
      call.checkpoint state.session key publicArguments options.inputValidationFuel state.world state.store)
    {arguments : List Dynamic.Value}
    (inputs : RecursiveNamedPublicFunctionHistoryInputs.Inputs entries request.header.function.context
      (request.header.bindings.map (fun binding => binding.1.scheme.body)) publicArguments arguments)
    {parameterType resultType : TypeSystem.Ty}
    (rawType : request.header.function.resultType = (.function parameterType resultType))
    (ready : session.ExportsReady)
    {invocation : Staging.Recursive.Scope} {after : Dynamic.Heap} {source : Dynamic.Value}
    (trace : SourceCall anchor request.header invocation state.heap arguments (.value source) after) :
    ForwardAt rows anchor initial profile recipe entries call.checkpoint (.function parameterType resultType) source after := by
  have sameCompiled := SourceCoreIndexedSession.Recipe.prepare_compiled prepared
  cases sameCompiled
  obtain ⟨receiving, contextAt, issued, extension, history⟩ := state.at_named_request prepared request
  have registry : request.encodedValues.registry = receiving.result.context.registry :=
    (congrArg SourceCoreCompatibleValues.Context.registry contextAt).symm
  have metadata : SourceCoreRawMetadata.Extends request.encodedValues.registry receiving.result.context.registry := by
    rw [registry]; exact .refl _
  obtain ⟨stable, heaps, heapTyped, represented, argumentsTyped⟩ :=
    SelectedCompilationPublicClosureHistory.History.current_arguments
      (profile := profile)
      (bodyTyping := support.bodyTyping) (prepared := prepared)
      (selected := request.selected) (history := history)
      (started := request.started) (inputReceipts := inputs) (metadata := metadata)
  have globalReference := CallableIndexedOwnedPreparedBootstrapGlobalReferences.global_reference
    rows request.header request.selected.member
  have supports := (SelectedCompilationPublicReturnedValues.header_context_supports
    request.header anchor support.bodyTyping).2
  obtain ⟨rawD, function, sourceSize, sourceAt, applied⟩ := trace
  obtain ⟨capture, value, finalStore, finalMap, finalWorld, requiredExecution, enough, result⟩ :=
    SelectedCompilationPublicBodyInvocationBounds.preserves_root
      (stagePrepared := stagePrepared recipe.compiled) (completion := receiving)
      (functions := functions rows initial profile)
      (owner := CallableIndexedOwnedPreparedBootstrapRootState.owner recipe.compiled)
      (packet := support.bodies request.header request.selected.member) (preservesBodies := fun budget {child} selected =>
        SelectedCompilationPhysicalProgramSupport.preserves_bodies support issued
          extension request.header request.selected.member selected budget)
      (keyPhysical := CallableIndexedOwnedPreparedPhysicalBootstrap.key_physical _ _)
      (physical := history.physical)
      (bodyTyping := support.bodyTyping)
      (selected := request.selected) (caller := state.caller)
      (globalReference := globalReference) (stable := stable) (heapTyped := heapTyped)
      (represented := represented) (argumentsTyped := argumentsTyped) (heaps := heaps)
      (sourceAt := sourceAt) (supports := supports) applied
  obtain ⟨payload, rfl⟩ : ∃ payload, value = .inRight .word payload := by
    have representedResult := result.2.1
    cases representedResult with
    | value represented => exact ⟨_, rfl⟩
  have completes : ∀ executionFuel, requiredExecution ≤ executionFuel →
      request.checkpoint.NativeDone executionFuel (.inRight .word payload) finalStore :=
    fun fuel bound => request.started.initial.native_done_iff.mpr (enough fuel bound)
  have representedResult : CompatiblePayload.ValueRep recipe.compiled.compatible.checked
      receiving.result.context.registry (functions rows initial profile)
      finalMap finalWorld request.header.function.resultType source payload request.header.output := by
    have representedResult := result.2.1
    cases representedResult with
    | value related => exact related
  have shape : SourceCorePublicOutputShapes.Output recipe.compiled.compatible.checked request.encodedValues.registry
      (finalStore.map Core.Value.type) recipe.program.layouts.definitions request.header.function.resultType payload := by
    have shaped := CompatiblePublicOutputShapes.ValueRep.output representedResult
    rw [← registry] at shaped
    rw [result.2.2.1.runtime_hasTypes.world_eq] at shaped
    exact shaped
  have checkpointRegistry : request.checkpoint.RegistryAt request.encodedValues.registry := by
    have atValues := request.started.values
    generalize checkpointEq : request.checkpoint = checkpoint at atValues ⊢
    cases checkpoint
    change _ = request.encodedValues at atValues
    exact congrArg SourceCoreCompatibleValues.Context.registry atValues
  have atRecipe : state.artifact.RecipeAt recipe := by
    have convert : ∀ (artifact : SourceCoreIndexedSession.Artifact) (recipe : SourceCoreIndexedSession.Recipe),
        RecursiveNamedPublicStartMeaning.ArtifactRecipe artifact recipe → artifact.RecipeAt recipe :=
      fun artifact _ atRecipe => by cases artifact; exact atRecipe
    exact convert _ _ state.atRecipe
  have requested := request.started.original.result_type_at atRecipe request.started.selected
  have selectedResult := (RecursiveNamedPublicRootSourceSignature.inputs_and_result request.selected).2
  rw [selectedResult] at requested
  have checkpointReady := request.started.original.initial_registry.exportsReady (state.atSession.exportsReady_iff.mp ready)
  obtain ⟨requiredOutput, exports⟩ := call.checkpoint.output_succeeded_uniform
    request.atCheckpoint atRecipe checkpointRegistry checkpointReady requested shape
  refine ⟨requiredExecution, max requiredOutput 1, ?_⟩
  intro executionFuel outputFuel outcome executionBound outputBound resumed
  obtain ⟨completion, actual, generation, succeeded, exported, actualAt, returnedReady⟩ :=
    exports executionFuel (completes executionFuel executionBound) outputFuel (Nat.le_trans (Nat.le_max_left _ _) outputBound) outcome resumed
  have requestedRaw := requested
  rw [rawType] at requested
  obtain ⟨exportedCompletion, handle, sameOutcome, functionValue, handleType, _ready⟩ :=
    SourceCoreExecution.Checkpoint.ResumeAt.runtime_function_succeeded request.atCheckpoint resumed checkpointReady
      (completes executionFuel executionBound) requested rfl (by omega)
  have sameCompletion : exportedCompletion = completion :=
    SourceCoreExecution.Outcome.succeeded.inj (sameOutcome.symm.trans succeeded)
  subst exportedCompletion
  obtain ⟨reached, _related, retained⟩ := history.semantic.after_success
    (SourceCoreIndexedSession.Recipe.prepare_compiled prepared) request.started request.selected exported result
  have physicalRetained := history.after_result result retained
  have returnedRegistry := request.started.returned_registry exported
  rw [registry] at returnedRegistry
  let returned : State rows anchor initial profile recipe completion.session entries := {
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
    extension := extension
    registry := returnedRegistry
    history := physicalRetained }
  have represented : CompatiblePayload.ValueRep recipe.compiled.compatible.checked receiving.result.context.registry
      (functions rows initial profile) finalMap finalWorld (.function parameterType resultType) source
      payload request.header.output := by
    rw [← rawType]
    exact representedResult
  have encoded := (exported.reimports_payload requested rfl).2
  rw [← actualAt.1] at encoded
  exact ⟨completion, succeeded, handle, functionValue, rawType ▸ handleType,
    actualAt.2.2.2.exportsReady_iff.mpr returnedReady, returned, rfl,
    payload, _, encoded, represented⟩

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicSessionExportForward
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicSessionScalarStep
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicSessionScalarStep
open Core Frontend SourceInference
open CallableIndexedOwnedPreparedFiniteNamedInventories (Input Inventory headers)
open CallableIndexedOwnedPreparedBootstrapRootState (keys)
open CallableIndexedOwnedFunctionValues (Header)
open SelectedCompilationPublicSessionState
open RecursiveNamedPublicScalarResults (ScalarOutput)
open SelectedCompilationPhysicalProgramSupport (stagePrepared)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {inputs : List (Input compiled)} {rows : Inventory inputs}
  {anchor : Header compiled (Program.ofChecked compiled.sourceProgram)}
  {initial : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
  {profile : compiled.compatible.checked.catalog.callableContracts = true}
  {recipe : SourceCoreIndexedSession.Recipe}

theorem State.finished_call (support : SelectedCompilationPhysicalProgramSupport.Support compiled (headers rows) (keys compiled) initial)
    (prepared : SourceCoreIndexedSession.Recipe.prepare compiled = .ok recipe)
    {options : SourceCoreExecution.RunOptions}
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    {entries : List RecursiveNamedPublicFunctionHistory.Entry}
    (state : State rows anchor initial profile recipe session entries)
    {key : SourceCoreIndexedSession.Key} {publicArguments : List SourceCorePublicValues.Value}
    (scalar : ScalarOutput) (call : Call session key publicArguments options)
    (returned : call.completion.value = scalar.publicValue)
    (request : RecursiveNamedPublicHistoryFrontdoor.Started (headers rows) prepared
      call.checkpoint state.session key publicArguments options.inputValidationFuel state.world state.store)
    {arguments : List Dynamic.Value}
    (inputs : RecursiveNamedPublicFunctionHistoryInputs.Inputs entries request.header.function.context
      (request.header.bindings.map (fun binding => binding.1.scheme.body)) publicArguments arguments)
    (registry : request.encodedValues.registry = state.receiving.result.context.registry)
    (rawType : request.header.function.resultType = scalar.sourceType)
    (nativeType : request.header.output = scalar.nativeType)
    (descriptor : SourceCoreCallableContracts.Descriptor compiled.indexed.ancestry.graph.inputs.callable.table
      (.named request.header.named.signature.key))
    (invocation : Staging.Recursive.Scope) :
    ∃ after : State rows anchor initial profile recipe call.completion.session entries,
      SourceCall anchor request.header invocation state.heap arguments
        (.value scalar.source) after.heap := by
  have sameCompiled := SourceCoreIndexedSession.Recipe.prepare_compiled prepared
  cases sameCompiled
  have metadata : SourceCoreRawMetadata.Extends request.encodedValues.registry state.receiving.result.context.registry := by
    rw [registry]; exact .refl _
  obtain ⟨stable, heaps, heapTyped, represented, argumentsTyped⟩ :=
    SelectedCompilationPublicClosureHistory.History.current_arguments
      (profile := profile)
      (bodyTyping := support.bodyTyping) (prepared := prepared)
      (selected := request.selected) (history := state.history)
      (started := request.started) (inputReceipts := inputs) (metadata := metadata)
  have globalReference := CallableIndexedOwnedPreparedBootstrapGlobalReferences.global_reference
    rows request.header request.selected.member
  have supports := (SelectedCompilationPublicReturnedValues.header_context_supports
    request.header anchor support.bodyTyping).2
  obtain ⟨actual, generation, native, finalStore, capture, sourceSize, outcome, after,
      finalMap, finalWorld, succeeded, valueEq, _typeEq, _budgetEq, returnedAt, trace, result⟩ :=
    SelectedCompilationPublicBodyInvocationBounds.public_run_succeeded_reflects
      (stagePrepared := stagePrepared recipe.compiled) (completion := state.receiving)
      (functions := functions rows initial profile)
      (owner := CallableIndexedOwnedPreparedBootstrapRootState.owner recipe.compiled)
      (packet := support.bodies request.header request.selected.member) (reflectsBodies := fun budget {child} selected =>
        SelectedCompilationPhysicalProgramSupport.reflects_bodies support state.issued
          state.extension request.header request.selected.member selected budget)
      (keyPhysical := CallableIndexedOwnedPreparedPhysicalBootstrap.key_physical _ _)
      (physical := state.history.physical)
      (bodyTyping := support.bodyTyping)
      (selected := request.selected) (caller := state.caller)
      (globalReference := globalReference) (stable := stable) (heapTyped := heapTyped)
      (represented := represented) (argumentsTyped := argumentsTyped) (heaps := heaps)
      (sourceAt := request.sourceAt) (supports := supports)
      (sameCompiled := SourceCoreIndexedSession.Recipe.prepare_compiled prepared)
      (started := request.started) (invocation := invocation)
      call.started request.atCheckpoint call.executed descriptor
  obtain ⟨reached, _related, retained⟩ := state.history.semantic.after_success
    (SourceCoreIndexedSession.Recipe.prepare_compiled prepared) request.started request.selected succeeded result
  have physicalRetained := state.history.after_result result retained
  have atRecipe : state.artifact.RecipeAt recipe := by
    have convert : ∀ (artifact : SourceCoreIndexedSession.Artifact) (recipe : SourceCoreIndexedSession.Recipe),
        RecursiveNamedPublicStartMeaning.ArtifactRecipe artifact recipe → artifact.RecipeAt recipe :=
      fun artifact _ atRecipe => by cases artifact; exact atRecipe
    exact convert _ _ state.atRecipe
  have requested := request.started.original.result_type_at atRecipe request.started.selected
  have resultType := (RecursiveNamedPublicRootSourceSignature.inputs_and_result request.selected).2
  rw [resultType, rawType] at requested
  have represented := result.2.1
  rw [nativeType] at represented
  have outcomeValue := scalar.source_value succeeded requested (valueEq.symm.trans returned) represented
  have returnedRegistry := request.started.returned_registry succeeded
  rw [registry] at returnedRegistry
  let next : State rows anchor initial profile recipe call.completion.session entries := {
    artifact := state.artifact
    session := actual.session
    mapping := finalMap
    world := finalWorld
    heap := after
    store := finalStore
    caller := reached
    atSession := returnedAt
    atRecipe := state.atRecipe
    receiving := state.receiving
    issued := state.issued
    extension := state.extension
    registry := returnedRegistry
    history := physicalRetained }
  exact ⟨next, request.rawD, request.function, sourceSize, request.sourceAt, outcomeValue ▸ trace⟩

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicSessionScalarStep
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicSessionInitialDataScalarStep
/-! A genuine first scalar completion establishes an empty retained-handle
history and the exact Source outcome, heap and physical store. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicSessionInitialDataScalarStep
open Core Frontend SourceInference
open CallableIndexedOwnedPreparedFiniteNamedInventories (Input Inventory headers)
open CallableIndexedOwnedFunctionValues (Header)
open RecursiveNamedPublicScalarResults (ScalarOutput)
open CallableIndexedOwnedPreparedBootstrapRootState (keys)
open SelectedCompilationPublicSessionState (StartedCall Call State SourceCall)
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

theorem first_scalar
    (distinct : (inputs.map (fun input => input.prepared.index)).Nodup)
    (scalar : ScalarOutput) (call : Call session key publicArguments options)
    (returned : call.completion.value = scalar.publicValue)
    (start : Started rows prepared header call.toStartedCall)
    (inputTypes : RecursiveNamedPublicDataArgumentReceipts.PublicDataTypes
      header.function.context publicArguments header.types)
    {arguments : List Dynamic.Value}
    (inputMeanings : RecursiveNamedPublicDataInputs.Meanings publicArguments arguments)
    (rawType : header.function.resultType = scalar.sourceType)
    (nativeType : header.output = scalar.nativeType)
    (descriptor : SourceCoreCallableContracts.Descriptor recipe.compiled.indexed.ancestry.graph.inputs.callable.table
      (.named header.named.signature.key))
    (invocation : Staging.Recursive.Scope) :
    ∃ after : State rows anchor initial support.profile recipe call.completion.session [],
      SourceCall anchor header invocation ⟨[]⟩ arguments (.value scalar.source) after.heap := by
  obtain ⟨receiving, contextAt, receiverIssued, receiverExtension⟩ :=
    SelectedCompilationPublicInitialReceiver.of_started support start
  have receiverRegistry := congrArg SourceCoreCompatibleValues.Context.registry contextAt
  have metadata : SourceCoreRawMetadata.Extends start.encodedValues.registry receiving.result.context.registry := by
    rw [receiverRegistry]
    exact .refl _
  obtain ⟨rawD, function, sourceAt⟩ :=
    (CallableIndexedOwnedPreparedFiniteNamedInventories.source_receipts rows).receipts header start.selected.member
  obtain ⟨physicalCaller, stable, globalReference, heaps, heapTyped, represented, argumentsTyped⟩ :=
    SelectedCompilationPublicInitialArguments.initial_data_arguments
      (inputs := inputs) (rows := rows) (distinct := distinct)
      (profile := support.profile) (completion := receiving)
      (bodyRegistry := initial.result.context.registry)
      (semanticFaults := CallableIndexedOwnedPublicDecodedCallFaults.faults initial.result.diagnostics)
      (bodyTyping := support.bodyTyping) (prepared := prepared) (selected := start.selected)
      (opened := start.opened) (fresh := start.fresh) (ready := start.ready)
      (sameRuntime := SourceCoreExecution.Session.SameRuntime.refl session) (atSession := start.atSession)
      (started := start.started) (inputTypes := inputTypes) (inputMeanings := inputMeanings) (metadata := metadata)
  have supports := (SelectedCompilationPublicReturnedValues.header_context_supports header anchor support.bodyTyping).2
  obtain ⟨actual, generation, value, finalStore, capture, sourceSize, outcome, after,
      finalMap, finalWorld, succeeded, valueEq, _typeEq, _budgetEq, returnedAt, trace, result⟩ :=
    SelectedCompilationPublicBodyInvocationBounds.public_run_succeeded_reflects
      (stagePrepared := stagePrepared recipe.compiled) (completion := receiving)
      (functions := SelectedCompilationPhysicalProgramSupport.functions support)
      (packet := support.bodies header start.selected.member)
      (reflectsBodies := fun budget {child} selected =>
        SelectedCompilationPhysicalProgramSupport.reflects_bodies support receiverIssued receiverExtension
          header start.selected.member selected budget)
      (owner := CallableIndexedOwnedPreparedBootstrapRootState.owner recipe.compiled)
      (keyPhysical := CallableIndexedOwnedPreparedPhysicalBootstrap.key_physical _ _)
      (physical := physicalCaller.physical) (bodyTyping := support.bodyTyping)
      (selected := start.selected) (caller := physicalCaller.base.val)
      (globalReference := globalReference) (stable := stable) (heapTyped := heapTyped)
      (represented := represented) (argumentsTyped := argumentsTyped) (heaps := heaps)
      (sourceAt := sourceAt) (supports := supports)
      (sameCompiled := SourceCoreIndexedSession.Recipe.prepare_compiled prepared)
      (started := start.started) (invocation := invocation)
      call.started start.atCheckpoint call.executed descriptor
  obtain ⟨reached, related, post⟩ := result.2.2.2.2.2.2.2
  have retained := RecursiveNamedPublicFunctionHistory.History.first rfl start.started start.selected succeeded result
    reached ⟨related, post⟩ .skip
  have physicalRetained := RecursiveNamedPublicPhysicalHistory.physical_of_result physicalCaller.physical result
  have atRecipe : start.artifact.RecipeAt recipe := by
    have convert : ∀ (artifact : SourceCoreIndexedSession.Artifact),
        RecursiveNamedPublicStartMeaning.ArtifactRecipe artifact recipe → artifact.RecipeAt recipe :=
      fun artifact atRecipe => by cases artifact; exact atRecipe
    exact convert _ start.started.recipe_eq
  have requested := start.started.original.result_type_at atRecipe start.started.selected
  have resultType := (RecursiveNamedPublicRootSourceSignature.inputs_and_result start.selected).2
  rw [resultType, rawType] at requested
  have represented := result.2.1
  rw [nativeType] at represented
  have outcomeValue := scalar.source_value succeeded requested (valueEq.symm.trans returned) represented
  have returnedRegistry := start.started.returned_registry succeeded
  rw [← receiverRegistry] at returnedRegistry
  let next : State rows anchor initial support.profile recipe call.completion.session [] := {
    artifact := start.artifact, session := actual.session, mapping := finalMap, world := finalWorld,
    heap := after, store := finalStore, caller := reached, atSession := returnedAt,
    atRecipe := start.started.recipe_eq, receiving := receiving, issued := receiverIssued,
    extension := receiverExtension, registry := returnedRegistry, history := ⟨retained, physicalRetained⟩ }
  exact ⟨next, rawD, function, sourceSize, sourceAt, outcomeValue ▸ trace⟩

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicSessionInitialDataScalarStep
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicSessionFailureStep
/-! An actual failed public call retains its returned session, prior function
history and physical cache. The original staged failure and its decoded token
are derived from the real native failure; Source preservation keeps the heap
after every effect performed before failure. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicSessionFailureStep
open Core Frontend SourceInference
open CallableIndexedOwnedPreparedFiniteNamedInventories (Input Inventory headers)
open CallableIndexedOwnedPreparedBootstrapRootState (keys)
open CallableIndexedOwnedFunctionValues (Header)
open SelectedCompilationPublicSessionState
open SelectedCompilationPhysicalProgramSupport (stagePrepared)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {inputs : List (Input compiled)} {rows : Inventory inputs}
  {anchor : Header compiled (Program.ofChecked compiled.sourceProgram)}
  {initial : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
  {profile : compiled.compatible.checked.catalog.callableContracts = true}
  {recipe : SourceCoreIndexedSession.Recipe}

/-- Reflect a public failure through the same static program package and actual
argument receipts, without imposing a result type. -/
theorem State.failed_call (support : SelectedCompilationPhysicalProgramSupport.Support compiled (headers rows) (keys compiled) initial)
    (selectedBodies : Staging.Recursive.SelectedPreservation.SelectedBodies
      (Program.ofChecked compiled.sourceProgram)
      (SelectedCompilationPhysicalProgramSupport.stages compiled))
    (prepared : SourceCoreIndexedSession.Recipe.prepare compiled = .ok recipe)
    {options : SourceCoreExecution.RunOptions}
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    {entries : List RecursiveNamedPublicFunctionHistory.Entry}
    (state : State rows anchor initial profile recipe session entries)
    {key : SourceCoreIndexedSession.Key} {publicArguments : List SourceCorePublicValues.Value}
    (call : StartedCall session key publicArguments options)
    (returned : SourceCoreExecution.Session artifact) (reason : Word)
    (failedCall : session.RunAt key publicArguments options (.ok (.failed reason returned)))
    (request : RecursiveNamedPublicHistoryFrontdoor.Started (headers rows) prepared
      call.checkpoint state.session key publicArguments options.inputValidationFuel state.world state.store)
    {arguments : List Dynamic.Value}
    (inputs : RecursiveNamedPublicFunctionHistoryInputs.Inputs entries request.header.function.context
      (request.header.bindings.map (fun binding => binding.1.scheme.body)) publicArguments arguments)
    (registry : request.encodedValues.registry = state.receiving.result.context.registry)
    (descriptor : SourceCoreCallableContracts.Descriptor compiled.indexed.ancestry.graph.inputs.callable.table
      (.named request.header.named.signature.key))
    (invocation : Staging.Recursive.Scope) :
    ∃ failure, ∃ after : State rows anchor initial profile recipe returned entries,
      SourceCall anchor request.header invocation state.heap arguments
        (.fault failure) after.heap ∧
      CallableIndexedOwnedPublicDecodedStagedCallFaults.faults
        after.receiving.result.diagnostics failure reason := by
  have sameCompiled := SourceCoreIndexedSession.Recipe.prepare_compiled prepared
  cases sameCompiled
  have metadata : SourceCoreRawMetadata.Extends request.encodedValues.registry state.receiving.result.context.registry := by
    rw [registry]; exact .refl _
  obtain ⟨stable, heaps, heapTyped, represented, argumentsTyped⟩ :=
    SelectedCompilationPublicClosureHistory.History.current_arguments
      (profile := profile)
      (bodyTyping := support.bodyTyping) (prepared := prepared)
      (selected := request.selected) (history := state.history)
      (started := request.started) (inputReceipts := inputs) (metadata := metadata)
  have globalReference := CallableIndexedOwnedPreparedBootstrapGlobalReferences.global_reference
    rows request.header request.selected.member
  have supports := (SelectedCompilationPublicReturnedValues.header_context_supports
    request.header anchor support.bodyTyping).2
  obtain ⟨actual, native, finalStore, capture, sourceSize, outcome, after,
      finalMap, finalWorld, failed, returnedAt, trace, result⟩ :=
    SelectedCompilationPublicBodyInvocationBounds.public_run_failed_reflects
      (stagePrepared := stagePrepared recipe.compiled) (completion := state.receiving)
      (functions := functions rows initial profile)
      (owner := CallableIndexedOwnedPreparedBootstrapRootState.owner recipe.compiled)
      (packet := support.bodies request.header request.selected.member) (reflectsBodies := fun budget {child} selected =>
        SelectedCompilationPhysicalProgramSupport.reflects_bodies support state.issued
          state.extension request.header request.selected.member selected budget)
      (keyPhysical := CallableIndexedOwnedPreparedPhysicalBootstrap.key_physical _ _)
      (physical := state.history.physical)
      (bodyTyping := support.bodyTyping)
      (selected := request.selected) (caller := state.caller)
      (globalReference := globalReference) (stable := stable) (heapTyped := heapTyped)
      (represented := represented) (argumentsTyped := argumentsTyped) (heaps := heaps)
      (sourceAt := request.sourceAt) (supports := supports)
      (sameCompiled := SourceCoreIndexedSession.Recipe.prepare_compiled prepared)
      (started := request.started) (invocation := invocation)
      call.started request.atCheckpoint failedCall descriptor
  obtain ⟨failure, outcomeEq⟩ : ∃ failure, outcome = .fault failure := by
    have represented := result.2.1
    cases represented with
    | value _ => have impossible := failed.2.1; cases impossible
    | fault _ => exact ⟨_, rfl⟩
  subst outcome
  have fault : CallableIndexedOwnedPublicDecodedStagedCallFaults.faults
      state.receiving.result.diagnostics failure reason := by
    have represented := result.2.1
    cases represented with
    | fault matched =>
      have decoded := failed.2.1
      simp only [Core.LanguageResult.decode?] at decoded
      cases decoded
      exact matched
  have contexts := (SelectedCompilationPublicReturnedValues.header_context_supports
    request.header anchor support.bodyTyping).1
  have callerHeap := heapTyped.transportContext contexts
  have callerArguments := argumentsTyped.transportContext contexts
  obtain ⟨packed, packing⟩ := Dynamic.ValuesPack.exists_pack arguments
  have preserved := Staging.Recursive.SelectedPreservation.applies_fault selectedBodies
    (SelectedCompilationPublicHistorySourceInputs.header_runtime support.bodyTyping anchor) callerHeap
    (SelectedCompilationPublicHistorySourceInputs.source_typed support.bodyTyping request.sourceAt anchor state.heap)
    packing (packing.hasType callerArguments) trace
  obtain ⟨reached, _related, retained⟩ := state.history.semantic.after_failure
    (SourceCoreIndexedSession.Recipe.prepare_compiled prepared) request.started request.selected
    failed result preserved.1
  have physicalRetained := state.history.after_result result retained
  have returnedRegistry : actual.RegistryAt state.receiving.result.context.registry := by
    have actualValues := failed.2.2.2.2.1.trans request.started.values
    exact (congrArg SourceCoreCompatibleValues.Context.registry actualValues).trans registry
  let next : State rows anchor initial profile recipe returned entries := {
    artifact := state.artifact
    session := actual
    mapping := finalMap
    world := finalWorld
    heap := after
    store := finalStore
    caller := reached
    atSession := returnedAt
    atRecipe := state.atRecipe
    receiving := state.receiving
    issued := state.issued
    extension := state.extension
    registry := returnedRegistry
    history := physicalRetained }
  exact ⟨failure, next, ⟨request.rawD, request.function, sourceSize, request.sourceAt, trace⟩, fault⟩

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicSessionFailureStep
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicSessionInitialDataFailureStep
/-! A completed initial failure reflects the original staged Source fault and
retains its exact physical state without any prior or fabricated handle. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicSessionInitialDataFailureStep
open Core Frontend SourceInference
open CallableIndexedOwnedPreparedFiniteNamedInventories (Input Inventory headers)
open CallableIndexedOwnedFunctionValues (Header)
open CallableIndexedOwnedPreparedBootstrapRootState (keys)
open SelectedCompilationPublicSessionState (StartedCall Call State SourceCall)
open SelectedCompilationPublicSessionInitial (Started)
open SelectedCompilationPhysicalProgramSupport (Support stagePrepared)

variable {recipe : SourceCoreIndexedSession.Recipe}
  {inputs : List (Input recipe.compiled)} (rows : Inventory inputs)
  (prepared : SourceCoreIndexedSession.Recipe.prepare recipe.compiled = .ok recipe)
  (anchor header : Header recipe.compiled (Program.ofChecked recipe.compiled.sourceProgram))
  {initial : CallableIndexedOwnedPublicFaultReceivers.Receiver recipe.compiled.indexed}
  (support : Support recipe.compiled (headers rows) (keys recipe.compiled) initial)
  (selectedBodies : Staging.Recursive.SelectedPreservation.SelectedBodies
    (Program.ofChecked recipe.compiled.sourceProgram)
    (SelectedCompilationPhysicalProgramSupport.stages recipe.compiled))
  {publicArtifact : SourceCoreExecution.Artifact}
  {session : SourceCoreExecution.Session publicArtifact}
  {key : SourceCoreIndexedSession.Key} {publicArguments : List SourceCorePublicValues.Value}
  {options : SourceCoreExecution.RunOptions}

include selectedBodies in
theorem first_failure
    (distinct : (inputs.map (fun input => input.prepared.index)).Nodup)
    (call : StartedCall session key publicArguments options)
    (returned : SourceCoreExecution.Session publicArtifact) (reason : Word)
    (failedCall : session.RunAt key publicArguments options (.ok (.failed reason returned)))
    (start : Started rows prepared header call)
    (inputTypes : RecursiveNamedPublicDataArgumentReceipts.PublicDataTypes
      header.function.context publicArguments header.types)
    {arguments : List Dynamic.Value}
    (inputMeanings : RecursiveNamedPublicDataInputs.Meanings publicArguments arguments)
    (descriptor : SourceCoreCallableContracts.Descriptor recipe.compiled.indexed.ancestry.graph.inputs.callable.table
      (.named header.named.signature.key))
    (invocation : Staging.Recursive.Scope) :
    ∃ failure, ∃ after : State rows anchor initial support.profile recipe returned [],
      SourceCall anchor header invocation ⟨[]⟩ arguments (.fault failure) after.heap ∧
      CallableIndexedOwnedPublicDecodedStagedCallFaults.faults after.receiving.result.diagnostics failure reason := by
  obtain ⟨receiving, contextAt, receiverIssued, receiverExtension⟩ :=
    SelectedCompilationPublicInitialReceiver.of_started support start
  have receiverRegistry := congrArg SourceCoreCompatibleValues.Context.registry contextAt
  have metadata : SourceCoreRawMetadata.Extends start.encodedValues.registry receiving.result.context.registry := by
    rw [receiverRegistry]
    exact .refl _
  obtain ⟨rawD, function, sourceAt⟩ :=
    (CallableIndexedOwnedPreparedFiniteNamedInventories.source_receipts rows).receipts header start.selected.member
  obtain ⟨physicalCaller, stable, globalReference, heaps, heapTyped, represented, argumentsTyped⟩ :=
    SelectedCompilationPublicInitialArguments.initial_data_arguments
      (inputs := inputs) (rows := rows) (distinct := distinct)
      (profile := support.profile) (completion := receiving)
      (bodyRegistry := initial.result.context.registry)
      (semanticFaults := CallableIndexedOwnedPublicDecodedCallFaults.faults initial.result.diagnostics)
      (bodyTyping := support.bodyTyping) (prepared := prepared) (selected := start.selected)
      (opened := start.opened) (fresh := start.fresh) (ready := start.ready)
      (sameRuntime := SourceCoreExecution.Session.SameRuntime.refl session) (atSession := start.atSession)
      (started := start.started) (inputTypes := inputTypes) (inputMeanings := inputMeanings) (metadata := metadata)
  have supports := (SelectedCompilationPublicReturnedValues.header_context_supports header anchor support.bodyTyping).2
  obtain ⟨actual, native, finalStore, capture, sourceSize, outcome, after,
      finalMap, finalWorld, failed, returnedAt, trace, result⟩ :=
    SelectedCompilationPublicBodyInvocationBounds.public_run_failed_reflects
      (stagePrepared := stagePrepared recipe.compiled) (completion := receiving)
      (functions := SelectedCompilationPhysicalProgramSupport.functions support)
      (packet := support.bodies header start.selected.member)
      (reflectsBodies := fun budget {child} selected =>
        SelectedCompilationPhysicalProgramSupport.reflects_bodies support receiverIssued receiverExtension
          header start.selected.member selected budget)
      (owner := CallableIndexedOwnedPreparedBootstrapRootState.owner recipe.compiled)
      (keyPhysical := CallableIndexedOwnedPreparedPhysicalBootstrap.key_physical _ _)
      (physical := physicalCaller.physical) (bodyTyping := support.bodyTyping)
      (selected := start.selected) (caller := physicalCaller.base.val)
      (globalReference := globalReference) (stable := stable) (heapTyped := heapTyped)
      (represented := represented) (argumentsTyped := argumentsTyped) (heaps := heaps)
      (sourceAt := sourceAt) (supports := supports)
      (sameCompiled := SourceCoreIndexedSession.Recipe.prepare_compiled prepared)
      (started := start.started) (invocation := invocation)
      call.started start.atCheckpoint failedCall descriptor
  obtain ⟨failure, outcomeEq⟩ : ∃ failure, outcome = .fault failure := by
    have represented := result.2.1
    cases represented with
    | value _ => have impossible := failed.2.1; cases impossible
    | fault _ => exact ⟨_, rfl⟩
  subst outcome
  have fault : CallableIndexedOwnedPublicDecodedStagedCallFaults.faults
      receiving.result.diagnostics failure reason := by
    have represented := result.2.1
    cases represented with
    | fault matched =>
      have decoded := failed.2.1
      simp only [Core.LanguageResult.decode?] at decoded
      cases decoded
      exact matched
  have contexts := (SelectedCompilationPublicReturnedValues.header_context_supports
    header anchor support.bodyTyping).1
  have callerHeap := heapTyped.transportContext contexts
  have callerArguments := argumentsTyped.transportContext contexts
  obtain ⟨packed, packing⟩ := Dynamic.ValuesPack.exists_pack arguments
  have preserved := Staging.Recursive.SelectedPreservation.applies_fault selectedBodies
    (SelectedCompilationPublicHistorySourceInputs.header_runtime support.bodyTyping anchor) callerHeap
    (SelectedCompilationPublicHistorySourceInputs.source_typed support.bodyTyping sourceAt anchor ⟨[]⟩)
    packing (packing.hasType callerArguments) trace
  obtain ⟨reached, related, post⟩ := result.2.2.2.2.2.2.2
  have retained := RecursiveNamedPublicFunctionHistory.History.first_failed rfl start.started start.selected
    failed result reached ⟨related, post⟩ preserved.1
  have physicalRetained := RecursiveNamedPublicPhysicalHistory.physical_of_result physicalCaller.physical result
  have returnedRegistry : actual.RegistryAt receiving.result.context.registry := by
    have actualValues := failed.2.2.2.2.1.trans start.started.values
    exact (congrArg SourceCoreCompatibleValues.Context.registry actualValues).trans receiverRegistry.symm
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
    receiving := receiving
    issued := receiverIssued
    extension := receiverExtension
    registry := returnedRegistry
    history := ⟨retained, physicalRetained⟩ }
  exact ⟨failure, next, ⟨rawD, function, sourceSize, sourceAt, trace⟩, fault⟩

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicSessionInitialDataFailureStep
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicSessionInitialScalarForward
/-! An initial scalar call retains the real bootstrapped state with an empty
handle history. Independent Source success supplies both required budgets. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicSessionInitialScalarForward
open Core Frontend SourceInference
open CallableIndexedOwnedPreparedFiniteNamedInventories (Input Inventory headers)
open CallableIndexedOwnedFunctionValues (Header)
open RecursiveNamedPublicScalarResults (ScalarOutput)
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
    SelectedCompilationPublicSessionScalarForward.ForwardAt (entries := [])
      rows anchor initial support.profile recipe scalar call after := by
  have _ := simple
  exact SelectedCompilationPublicSessionInitialDataScalarForward.first_scalar
    rows prepared anchor header support distinct scalar call start inputTypes inputMeanings rawType nativeType trace

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicSessionInitialScalarForward
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicSessionRegistryFunctionForward
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicSessionFunctionForward
open Core Frontend SourceInference
open CallableIndexedOwnedPreparedFiniteNamedInventories (Input Inventory headers)
open CallableIndexedOwnedPreparedBootstrapRootState (keys)
open CallableIndexedOwnedFunctionValues (Header)
open SelectedCompilationPublicSessionState
open RecursiveNamedPublicScalarResults (ScalarOutput)
open SelectedCompilationPhysicalProgramSupport (stagePrepared)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {inputs : List (Input compiled)} {rows : Inventory inputs}
  {anchor : Header compiled (Program.ofChecked compiled.sourceProgram)}
  {initial : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
  {profile : compiled.compatible.checked.catalog.callableContracts = true}
  {recipe : SourceCoreIndexedSession.Recipe}
theorem forward_function_at_input_registry (support : SelectedCompilationPhysicalProgramSupport.Support compiled (headers rows) (keys compiled) initial)
    (prepared : SourceCoreIndexedSession.Recipe.prepare compiled = .ok recipe)
    {options : SourceCoreExecution.RunOptions}
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    {entries : List RecursiveNamedPublicFunctionHistory.Entry}
    (state : State rows anchor initial profile recipe session entries)
    {key : SourceCoreIndexedSession.Key} {publicArguments : List SourceCorePublicValues.Value}
    (call : StartedCall session key publicArguments options)
    (request : RecursiveNamedPublicHistoryFrontdoor.Started (headers rows) prepared
      call.checkpoint state.session key publicArguments options.inputValidationFuel state.world state.store)
    {arguments : List Dynamic.Value}
    (inputs : RecursiveNamedPublicFunctionHistoryInputs.Inputs entries request.header.function.context
      (request.header.bindings.map (fun binding => binding.1.scheme.body)) publicArguments arguments)
    {parameterType resultType : TypeSystem.Ty}
    (rawType : request.header.function.resultType = (.function parameterType resultType))
    (ready : session.ExportsReady)
    {invocation : Staging.Recursive.Scope} {after : Dynamic.Heap} {source : Dynamic.Value}
    (trace : SourceCall anchor request.header invocation state.heap arguments (.value source) after) :
    FunctionForwardAt (entries := entries) rows anchor initial profile recipe call parameterType resultType source after := by
  have sameCompiled := SourceCoreIndexedSession.Recipe.prepare_compiled prepared
  cases sameCompiled
  obtain ⟨receiving, contextAt, issued, extension, history⟩ := state.at_named_request prepared request
  have registry : request.encodedValues.registry = receiving.result.context.registry :=
    (congrArg SourceCoreCompatibleValues.Context.registry contextAt).symm
  have metadata : SourceCoreRawMetadata.Extends request.encodedValues.registry receiving.result.context.registry := by
    rw [registry]; exact .refl _
  obtain ⟨stable, heaps, heapTyped, represented, argumentsTyped⟩ :=
    SelectedCompilationPublicClosureHistory.History.current_arguments
      (profile := profile)
      (bodyTyping := support.bodyTyping) (prepared := prepared)
      (selected := request.selected) (history := history)
      (started := request.started) (inputReceipts := inputs) (metadata := metadata)
  have globalReference := CallableIndexedOwnedPreparedBootstrapGlobalReferences.global_reference
    rows request.header request.selected.member
  have supports := (SelectedCompilationPublicReturnedValues.header_context_supports
    request.header anchor support.bodyTyping).2
  obtain ⟨rawD, function, sourceSize, sourceAt, applied⟩ := trace
  obtain ⟨capture, value, finalStore, finalMap, finalWorld, requiredExecution, enough, result⟩ :=
    SelectedCompilationPublicBodyInvocationBounds.preserves_root
      (stagePrepared := stagePrepared recipe.compiled) (completion := receiving)
      (functions := functions rows initial profile)
      (owner := CallableIndexedOwnedPreparedBootstrapRootState.owner recipe.compiled)
      (packet := support.bodies request.header request.selected.member) (preservesBodies := fun budget {child} selected =>
        SelectedCompilationPhysicalProgramSupport.preserves_bodies support issued
          extension request.header request.selected.member selected budget)
      (keyPhysical := CallableIndexedOwnedPreparedPhysicalBootstrap.key_physical _ _)
      (physical := history.physical)
      (bodyTyping := support.bodyTyping)
      (selected := request.selected) (caller := state.caller)
      (globalReference := globalReference) (stable := stable) (heapTyped := heapTyped)
      (represented := represented) (argumentsTyped := argumentsTyped) (heaps := heaps)
      (sourceAt := sourceAt) (supports := supports) applied
  obtain ⟨payload, rfl⟩ : ∃ payload, value = .inRight .word payload := by
    have representedResult := result.2.1
    cases representedResult with
    | value represented => exact ⟨_, rfl⟩
  have completes : ∀ executionFuel, requiredExecution ≤ executionFuel →
      request.checkpoint.NativeDone executionFuel (.inRight .word payload) finalStore :=
    fun fuel bound => request.started.initial.native_done_iff.mpr (enough fuel bound)
  have representedResult : CompatiblePayload.ValueRep recipe.compiled.compatible.checked
      receiving.result.context.registry (functions rows initial profile)
      finalMap finalWorld request.header.function.resultType source payload request.header.output := by
    have representedResult := result.2.1
    cases representedResult with
    | value related => exact related
  have shape : SourceCorePublicOutputShapes.Output recipe.compiled.compatible.checked request.encodedValues.registry
      (finalStore.map Core.Value.type) recipe.program.layouts.definitions request.header.function.resultType payload := by
    have shaped := CompatiblePublicOutputShapes.ValueRep.output representedResult
    rw [← registry] at shaped
    rw [result.2.2.1.runtime_hasTypes.world_eq] at shaped
    exact shaped
  have checkpointRegistry : request.checkpoint.RegistryAt request.encodedValues.registry := by
    have atValues := request.started.values
    generalize checkpointEq : request.checkpoint = checkpoint at atValues ⊢
    cases checkpoint
    change _ = request.encodedValues at atValues
    exact congrArg SourceCoreCompatibleValues.Context.registry atValues
  have atRecipe : state.artifact.RecipeAt recipe := by
    have convert : ∀ (artifact : SourceCoreIndexedSession.Artifact) (recipe : SourceCoreIndexedSession.Recipe),
        RecursiveNamedPublicStartMeaning.ArtifactRecipe artifact recipe → artifact.RecipeAt recipe :=
      fun artifact _ atRecipe => by cases artifact; exact atRecipe
    exact convert _ _ state.atRecipe
  have requested := request.started.original.result_type_at atRecipe request.started.selected
  have selectedResult := (RecursiveNamedPublicRootSourceSignature.inputs_and_result request.selected).2
  rw [selectedResult] at requested
  have checkpointReady := request.started.original.initial_registry.exportsReady (state.atSession.exportsReady_iff.mp ready)
  obtain ⟨requiredOutput, exports⟩ := call.checkpoint.output_succeeded_uniform
    request.atCheckpoint atRecipe checkpointRegistry checkpointReady requested shape
  refine ⟨requiredExecution, max requiredOutput 1, ?_⟩
  intro executionFuel outputFuel outcome executionBound outputBound resumed
  obtain ⟨completion, actual, generation, succeeded, exported, actualAt, returnedReady⟩ :=
    exports executionFuel (completes executionFuel executionBound) outputFuel (Nat.le_trans (Nat.le_max_left _ _) outputBound) outcome resumed
  have requestedRaw := requested
  rw [rawType] at requested
  obtain ⟨exportedCompletion, handle, sameOutcome, functionValue, handleType, _ready⟩ :=
    SourceCoreExecution.Checkpoint.ResumeAt.runtime_function_succeeded request.atCheckpoint resumed checkpointReady
      (completes executionFuel executionBound) requested rfl (by omega)
  have sameCompletion : exportedCompletion = completion :=
    SourceCoreExecution.Outcome.succeeded.inj (sameOutcome.symm.trans succeeded)
  subst exportedCompletion
  let entry : RecursiveNamedPublicFunctionHistory.Entry :=
    ⟨request.header.function.resultType, source, handle, payload, request.header.output, outputFuel⟩
  obtain ⟨reached, related, post⟩ := result.2.2.2.2.2.2.2
  have retained := RecursiveNamedPublicFunctionHistory.History.next history.semantic
    (SourceCoreIndexedSession.Recipe.prepare_compiled prepared) request.started request.selected exported result reached ⟨related, post⟩
    (.remember requestedRaw rfl rfl (actualAt.1.symm.trans functionValue))
  have physicalRetained := history.after_result result retained
  have returnedRegistry := request.started.returned_registry exported
  rw [registry] at returnedRegistry
  let returned : State rows anchor initial profile recipe completion.session (entries ++ [entry]) := {
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
    extension := extension
    registry := returnedRegistry
    history := physicalRetained }
  exact ⟨completion, succeeded, actualAt.2.2.2.exportsReady_iff.mpr returnedReady,
    entry, rawType, rfl, functionValue, handleType, returned, rfl⟩


end Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicSessionFunctionForward
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicSessionFunctionStep
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicSessionFunctionStep
open Core Frontend SourceInference
open CallableIndexedOwnedPreparedFiniteNamedInventories (Input Inventory headers)
open CallableIndexedOwnedPreparedBootstrapRootState (keys)
open CallableIndexedOwnedFunctionValues (Header)
open SelectedCompilationPublicSessionState
open RecursiveNamedPublicScalarResults (ScalarOutput)
open SelectedCompilationPhysicalProgramSupport (stagePrepared)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {inputs : List (Input compiled)} {rows : Inventory inputs}
  {anchor : Header compiled (Program.ofChecked compiled.sourceProgram)}
  {initial : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
  {profile : compiled.compatible.checked.catalog.callableContracts = true}
  {recipe : SourceCoreIndexedSession.Recipe}

theorem State.make_typed_handle (support : SelectedCompilationPhysicalProgramSupport.Support compiled (headers rows) (keys compiled) initial)
    (prepared : SourceCoreIndexedSession.Recipe.prepare compiled = .ok recipe)
    {options : SourceCoreExecution.RunOptions}
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    {entries : List RecursiveNamedPublicFunctionHistory.Entry}
    (state : State rows anchor initial profile recipe session entries)
    {key : SourceCoreIndexedSession.Key} {publicArguments : List SourceCorePublicValues.Value}
    (call : FunctionCall session key publicArguments options)
    (request : RecursiveNamedPublicHistoryFrontdoor.Started (headers rows) prepared
      call.checkpoint state.session key publicArguments options.inputValidationFuel state.world state.store)
    {arguments : List Dynamic.Value}
    (inputs : RecursiveNamedPublicFunctionHistoryInputs.Inputs entries request.header.function.context
      (request.header.bindings.map (fun binding => binding.1.scheme.body)) publicArguments arguments)
    (registry : request.encodedValues.registry = state.receiving.result.context.registry)
    (descriptor : SourceCoreCallableContracts.Descriptor compiled.indexed.ancestry.graph.inputs.callable.table
      (.named request.header.named.signature.key))
    (invocation : Staging.Recursive.Scope) :
    ∃ entry : RecursiveNamedPublicFunctionHistory.Entry,
      entry.sourceType = request.header.function.resultType ∧ entry.handle = call.handle ∧
      call.handle.sourceType = request.header.function.resultType ∧
      ∃ after : State rows anchor initial profile recipe call.completion.session (entries ++ [entry]),
        SourceCall anchor request.header invocation state.heap arguments
          (.value entry.source) after.heap := by
  have sameCompiled := SourceCoreIndexedSession.Recipe.prepare_compiled prepared
  cases sameCompiled
  have metadata : SourceCoreRawMetadata.Extends request.encodedValues.registry state.receiving.result.context.registry := by
    rw [registry]; exact .refl _
  obtain ⟨stable, heaps, heapTyped, represented, argumentsTyped⟩ :=
    SelectedCompilationPublicClosureHistory.History.current_arguments
      (profile := profile)
      (bodyTyping := support.bodyTyping) (prepared := prepared)
      (selected := request.selected) (history := state.history)
      (started := request.started) (inputReceipts := inputs) (metadata := metadata)
  have globalReference := CallableIndexedOwnedPreparedBootstrapGlobalReferences.global_reference
    rows request.header request.selected.member
  have supports := (SelectedCompilationPublicReturnedValues.header_context_supports
    request.header anchor support.bodyTyping).2
  obtain ⟨actual, generation, native, finalStore, capture, sourceSize, outcome, after,
      finalMap, finalWorld, succeeded, valueEq, _typeEq, _budgetEq, returnedAt, trace, result⟩ :=
    SelectedCompilationPublicBodyInvocationBounds.public_run_succeeded_reflects
      (stagePrepared := stagePrepared recipe.compiled) (completion := state.receiving)
      (functions := functions rows initial profile)
      (owner := CallableIndexedOwnedPreparedBootstrapRootState.owner recipe.compiled)
      (packet := support.bodies request.header request.selected.member) (reflectsBodies := fun budget {child} selected =>
        SelectedCompilationPhysicalProgramSupport.reflects_bodies support state.issued
          state.extension request.header request.selected.member selected budget)
      (keyPhysical := CallableIndexedOwnedPreparedPhysicalBootstrap.key_physical _ _)
      (physical := state.history.physical)
      (bodyTyping := support.bodyTyping)
      (selected := request.selected) (caller := state.caller)
      (globalReference := globalReference) (stable := stable) (heapTyped := heapTyped)
      (represented := represented) (argumentsTyped := argumentsTyped) (heaps := heaps)
      (sourceAt := request.sourceAt) (supports := supports)
      (sameCompiled := SourceCoreIndexedSession.Recipe.prepare_compiled prepared)
      (started := request.started) (invocation := invocation)
      call.started request.atCheckpoint call.executed descriptor
  have atRecipe : state.artifact.RecipeAt recipe := by
    have convert : ∀ (artifact : SourceCoreIndexedSession.Artifact) (recipe : SourceCoreIndexedSession.Recipe),
        RecursiveNamedPublicStartMeaning.ArtifactRecipe artifact recipe → artifact.RecipeAt recipe :=
      fun artifact _ atRecipe => by cases artifact; exact atRecipe
    exact convert _ _ state.atRecipe
  have requested := request.started.original.result_type_at atRecipe request.started.selected
  have resultType := (RecursiveNamedPublicRootSourceSignature.inputs_and_result request.selected).2
  rw [resultType] at requested
  obtain ⟨reached, source, payload, sourceValue, _nativeValue, _related, retained⟩ :=
    state.history.semantic.remember_success (SourceCoreIndexedSession.Recipe.prepare_compiled prepared) request.started request.selected requested succeeded result
      (valueEq.symm.trans call.returned)
  have physicalRetained := state.history.after_result result retained
  have handleType := succeeded.function_source_type requested (valueEq.symm.trans call.returned)
  let entry : RecursiveNamedPublicFunctionHistory.Entry :=
    ⟨request.header.function.resultType, source, call.handle, payload, request.header.output,
      options.outputValidationFuel⟩
  have returnedRegistry := request.started.returned_registry succeeded
  rw [registry] at returnedRegistry
  let next : State rows anchor initial profile recipe call.completion.session (entries ++ [entry]) := {
    artifact := state.artifact
    session := actual.session
    mapping := finalMap
    world := finalWorld
    heap := after
    store := finalStore
    caller := reached
    atSession := returnedAt
    atRecipe := state.atRecipe
    receiving := state.receiving
    issued := state.issued
    extension := state.extension
    registry := returnedRegistry
    history := physicalRetained }
  exact ⟨entry, rfl, rfl, handleType, next, request.rawD, request.function, sourceSize, request.sourceAt, sourceValue ▸ trace⟩

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicSessionFunctionStep
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicSessionRegistryFunctionStep
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicSessionFunctionStep
open Core Frontend SourceInference
open CallableIndexedOwnedPreparedFiniteNamedInventories (Input Inventory headers)
open CallableIndexedOwnedPreparedBootstrapRootState (keys)
open CallableIndexedOwnedFunctionValues (Header)
open SelectedCompilationPublicSessionState
open RecursiveNamedPublicScalarResults (ScalarOutput)
open SelectedCompilationPhysicalProgramSupport (stagePrepared)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {inputs : List (Input compiled)} {rows : Inventory inputs}
  {anchor : Header compiled (Program.ofChecked compiled.sourceProgram)}
  {initial : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
  {profile : compiled.compatible.checked.catalog.callableContracts = true}
  {recipe : SourceCoreIndexedSession.Recipe}

theorem State.make_typed_handle_at_input_registry (support : SelectedCompilationPhysicalProgramSupport.Support compiled (headers rows) (keys compiled) initial)
    (prepared : SourceCoreIndexedSession.Recipe.prepare compiled = .ok recipe)
    {options : SourceCoreExecution.RunOptions}
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    {entries : List RecursiveNamedPublicFunctionHistory.Entry}
    (state : State rows anchor initial profile recipe session entries)
    {key : SourceCoreIndexedSession.Key} {publicArguments : List SourceCorePublicValues.Value}
    (call : FunctionCall session key publicArguments options)
    (request : RecursiveNamedPublicHistoryFrontdoor.Started (headers rows) prepared
      call.checkpoint state.session key publicArguments options.inputValidationFuel state.world state.store)
    {arguments : List Dynamic.Value}
    (inputs : RecursiveNamedPublicFunctionHistoryInputs.Inputs entries request.header.function.context
      (request.header.bindings.map (fun binding => binding.1.scheme.body)) publicArguments arguments)
    (descriptor : SourceCoreCallableContracts.Descriptor compiled.indexed.ancestry.graph.inputs.callable.table
      (.named request.header.named.signature.key))
    (invocation : Staging.Recursive.Scope) :
    ∃ entry : RecursiveNamedPublicFunctionHistory.Entry,
      entry.sourceType = request.header.function.resultType ∧ entry.handle = call.handle ∧
      call.handle.sourceType = request.header.function.resultType ∧
      ∃ after : State rows anchor initial profile recipe call.completion.session (entries ++ [entry]),
        SourceCall anchor request.header invocation state.heap arguments
          (.value entry.source) after.heap := by
  have sameCompiled := SourceCoreIndexedSession.Recipe.prepare_compiled prepared
  cases sameCompiled
  obtain ⟨receiving, contextAt, issued, extension, history⟩ := state.at_named_request prepared request
  have registry : request.encodedValues.registry = receiving.result.context.registry :=
    (congrArg SourceCoreCompatibleValues.Context.registry contextAt).symm
  have metadata : SourceCoreRawMetadata.Extends request.encodedValues.registry receiving.result.context.registry := by
    rw [registry]; exact .refl _
  obtain ⟨stable, heaps, heapTyped, represented, argumentsTyped⟩ :=
    SelectedCompilationPublicClosureHistory.History.current_arguments
      (profile := profile)
      (bodyTyping := support.bodyTyping) (prepared := prepared)
      (selected := request.selected) (history := history)
      (started := request.started) (inputReceipts := inputs) (metadata := metadata)
  have globalReference := CallableIndexedOwnedPreparedBootstrapGlobalReferences.global_reference
    rows request.header request.selected.member
  have supports := (SelectedCompilationPublicReturnedValues.header_context_supports
    request.header anchor support.bodyTyping).2
  obtain ⟨actual, generation, native, finalStore, capture, sourceSize, outcome, after,
      finalMap, finalWorld, succeeded, valueEq, _typeEq, _budgetEq, returnedAt, trace, result⟩ :=
    SelectedCompilationPublicBodyInvocationBounds.public_run_succeeded_reflects
      (stagePrepared := stagePrepared recipe.compiled) (completion := receiving)
      (functions := functions rows initial profile)
      (owner := CallableIndexedOwnedPreparedBootstrapRootState.owner recipe.compiled)
      (packet := support.bodies request.header request.selected.member) (reflectsBodies := fun budget {child} selected =>
        SelectedCompilationPhysicalProgramSupport.reflects_bodies support issued
          extension request.header request.selected.member selected budget)
      (keyPhysical := CallableIndexedOwnedPreparedPhysicalBootstrap.key_physical _ _)
      (physical := history.physical)
      (bodyTyping := support.bodyTyping)
      (selected := request.selected) (caller := state.caller)
      (globalReference := globalReference) (stable := stable) (heapTyped := heapTyped)
      (represented := represented) (argumentsTyped := argumentsTyped) (heaps := heaps)
      (sourceAt := request.sourceAt) (supports := supports)
      (sameCompiled := SourceCoreIndexedSession.Recipe.prepare_compiled prepared)
      (started := request.started) (invocation := invocation)
      call.started request.atCheckpoint call.executed descriptor
  have atRecipe : state.artifact.RecipeAt recipe := by
    have convert : ∀ (artifact : SourceCoreIndexedSession.Artifact) (recipe : SourceCoreIndexedSession.Recipe),
        RecursiveNamedPublicStartMeaning.ArtifactRecipe artifact recipe → artifact.RecipeAt recipe :=
      fun artifact _ atRecipe => by cases artifact; exact atRecipe
    exact convert _ _ state.atRecipe
  have requested := request.started.original.result_type_at atRecipe request.started.selected
  have resultType := (RecursiveNamedPublicRootSourceSignature.inputs_and_result request.selected).2
  rw [resultType] at requested
  obtain ⟨reached, source, payload, sourceValue, _nativeValue, _related, retained⟩ :=
    history.semantic.remember_success (SourceCoreIndexedSession.Recipe.prepare_compiled prepared) request.started request.selected requested succeeded result
      (valueEq.symm.trans call.returned)
  have physicalRetained := history.after_result result retained
  have handleType := succeeded.function_source_type requested (valueEq.symm.trans call.returned)
  let entry : RecursiveNamedPublicFunctionHistory.Entry :=
    ⟨request.header.function.resultType, source, call.handle, payload, request.header.output,
      options.outputValidationFuel⟩
  have returnedRegistry := request.started.returned_registry succeeded
  rw [registry] at returnedRegistry
  let next : State rows anchor initial profile recipe call.completion.session (entries ++ [entry]) := {
    artifact := state.artifact
    session := actual.session
    mapping := finalMap
    world := finalWorld
    heap := after
    store := finalStore
    caller := reached
    atSession := returnedAt
    atRecipe := state.atRecipe
    receiving := receiving
    issued := issued
    extension := extension
    registry := returnedRegistry
    history := physicalRetained }
  exact ⟨entry, rfl, rfl, handleType, next, request.rawD, request.function, sourceSize, request.sourceAt, sourceValue ▸ trace⟩


end Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicSessionFunctionStep
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicSessionRegistryScalarStep
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicSessionScalarStep
open Core Frontend SourceInference
open CallableIndexedOwnedPreparedFiniteNamedInventories (Input Inventory headers)
open CallableIndexedOwnedPreparedBootstrapRootState (keys)
open CallableIndexedOwnedFunctionValues (Header)
open SelectedCompilationPublicSessionState
open RecursiveNamedPublicScalarResults (ScalarOutput)
open SelectedCompilationPhysicalProgramSupport (stagePrepared)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {inputs : List (Input compiled)} {rows : Inventory inputs}
  {anchor : Header compiled (Program.ofChecked compiled.sourceProgram)}
  {initial : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
  {profile : compiled.compatible.checked.catalog.callableContracts = true}
  {recipe : SourceCoreIndexedSession.Recipe}

theorem State.finished_call_at_input_registry (support : SelectedCompilationPhysicalProgramSupport.Support compiled (headers rows) (keys compiled) initial)
    (prepared : SourceCoreIndexedSession.Recipe.prepare compiled = .ok recipe)
    {options : SourceCoreExecution.RunOptions}
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    {entries : List RecursiveNamedPublicFunctionHistory.Entry}
    (state : State rows anchor initial profile recipe session entries)
    {key : SourceCoreIndexedSession.Key} {publicArguments : List SourceCorePublicValues.Value}
    (scalar : ScalarOutput) (call : Call session key publicArguments options)
    (returned : call.completion.value = scalar.publicValue)
    (request : RecursiveNamedPublicHistoryFrontdoor.Started (headers rows) prepared
      call.checkpoint state.session key publicArguments options.inputValidationFuel state.world state.store)
    {arguments : List Dynamic.Value}
    (inputs : RecursiveNamedPublicFunctionHistoryInputs.Inputs entries request.header.function.context
      (request.header.bindings.map (fun binding => binding.1.scheme.body)) publicArguments arguments)
    (rawType : request.header.function.resultType = scalar.sourceType)
    (nativeType : request.header.output = scalar.nativeType)
    (descriptor : SourceCoreCallableContracts.Descriptor compiled.indexed.ancestry.graph.inputs.callable.table
      (.named request.header.named.signature.key))
    (invocation : Staging.Recursive.Scope) :
    ∃ after : State rows anchor initial profile recipe call.completion.session entries,
      SourceCall anchor request.header invocation state.heap arguments
        (.value scalar.source) after.heap := by
  have sameCompiled := SourceCoreIndexedSession.Recipe.prepare_compiled prepared
  cases sameCompiled
  obtain ⟨receiving, contextAt, issued, extension, history⟩ := state.at_named_request prepared request
  have registry : request.encodedValues.registry = receiving.result.context.registry :=
    (congrArg SourceCoreCompatibleValues.Context.registry contextAt).symm
  have metadata : SourceCoreRawMetadata.Extends request.encodedValues.registry receiving.result.context.registry := by
    rw [registry]; exact .refl _
  obtain ⟨stable, heaps, heapTyped, represented, argumentsTyped⟩ :=
    SelectedCompilationPublicClosureHistory.History.current_arguments
      (profile := profile)
      (bodyTyping := support.bodyTyping) (prepared := prepared)
      (selected := request.selected) (history := history)
      (started := request.started) (inputReceipts := inputs) (metadata := metadata)
  have globalReference := CallableIndexedOwnedPreparedBootstrapGlobalReferences.global_reference
    rows request.header request.selected.member
  have supports := (SelectedCompilationPublicReturnedValues.header_context_supports
    request.header anchor support.bodyTyping).2
  obtain ⟨actual, generation, native, finalStore, capture, sourceSize, outcome, after,
      finalMap, finalWorld, succeeded, valueEq, _typeEq, _budgetEq, returnedAt, trace, result⟩ :=
    SelectedCompilationPublicBodyInvocationBounds.public_run_succeeded_reflects
      (stagePrepared := stagePrepared recipe.compiled) (completion := receiving)
      (functions := functions rows initial profile)
      (owner := CallableIndexedOwnedPreparedBootstrapRootState.owner recipe.compiled)
      (packet := support.bodies request.header request.selected.member) (reflectsBodies := fun budget {child} selected =>
        SelectedCompilationPhysicalProgramSupport.reflects_bodies support issued
          extension request.header request.selected.member selected budget)
      (keyPhysical := CallableIndexedOwnedPreparedPhysicalBootstrap.key_physical _ _)
      (physical := history.physical)
      (bodyTyping := support.bodyTyping)
      (selected := request.selected) (caller := state.caller)
      (globalReference := globalReference) (stable := stable) (heapTyped := heapTyped)
      (represented := represented) (argumentsTyped := argumentsTyped) (heaps := heaps)
      (sourceAt := request.sourceAt) (supports := supports)
      (sameCompiled := SourceCoreIndexedSession.Recipe.prepare_compiled prepared)
      (started := request.started) (invocation := invocation)
      call.started request.atCheckpoint call.executed descriptor
  obtain ⟨reached, _related, retained⟩ := history.semantic.after_success
    (SourceCoreIndexedSession.Recipe.prepare_compiled prepared) request.started request.selected succeeded result
  have physicalRetained := history.after_result result retained
  have atRecipe : state.artifact.RecipeAt recipe := by
    have convert : ∀ (artifact : SourceCoreIndexedSession.Artifact) (recipe : SourceCoreIndexedSession.Recipe),
        RecursiveNamedPublicStartMeaning.ArtifactRecipe artifact recipe → artifact.RecipeAt recipe :=
      fun artifact _ atRecipe => by cases artifact; exact atRecipe
    exact convert _ _ state.atRecipe
  have requested := request.started.original.result_type_at atRecipe request.started.selected
  have resultType := (RecursiveNamedPublicRootSourceSignature.inputs_and_result request.selected).2
  rw [resultType, rawType] at requested
  have represented := result.2.1
  rw [nativeType] at represented
  have outcomeValue := scalar.source_value succeeded requested (valueEq.symm.trans returned) represented
  have returnedRegistry := request.started.returned_registry succeeded
  rw [registry] at returnedRegistry
  let next : State rows anchor initial profile recipe call.completion.session entries := {
    artifact := state.artifact
    session := actual.session
    mapping := finalMap
    world := finalWorld
    heap := after
    store := finalStore
    caller := reached
    atSession := returnedAt
    atRecipe := state.atRecipe
    receiving := receiving
    issued := issued
    extension := extension
    registry := returnedRegistry
    history := physicalRetained }
  exact ⟨next, request.rawD, request.function, sourceSize, request.sourceAt, outcomeValue ▸ trace⟩


end Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicSessionScalarStep
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicSessionInitialScalarStep
/-! A genuine first scalar completion establishes an empty retained-handle
history and the exact Source outcome, heap and physical store. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicSessionInitialScalarStep
open Core Frontend SourceInference
open CallableIndexedOwnedPreparedFiniteNamedInventories (Input Inventory headers)
open CallableIndexedOwnedFunctionValues (Header)
open RecursiveNamedPublicScalarResults (ScalarOutput)
open CallableIndexedOwnedPreparedBootstrapRootState (keys)
open SelectedCompilationPublicSessionState (StartedCall Call State SourceCall)
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

theorem first_scalar
    (distinct : (inputs.map (fun input => input.prepared.index)).Nodup)
    (scalar : ScalarOutput) (call : Call session key publicArguments options)
    (returned : call.completion.value = scalar.publicValue)
    (start : Started rows prepared header call.toStartedCall)
    (simple : ∀ value ∈ publicArguments, SourceCoreIndexedSession.SimplePublic value)
    (inputTypes : RecursiveNamedPublicDataArgumentReceipts.PublicDataTypes
      header.function.context publicArguments header.types)
    {arguments : List Dynamic.Value}
    (inputMeanings : RecursiveNamedPublicDataInputs.Meanings publicArguments arguments)
    (rawType : header.function.resultType = scalar.sourceType)
    (nativeType : header.output = scalar.nativeType)
    (descriptor : SourceCoreCallableContracts.Descriptor recipe.compiled.indexed.ancestry.graph.inputs.callable.table
      (.named header.named.signature.key))
    (invocation : Staging.Recursive.Scope) :
    ∃ after : State rows anchor initial support.profile recipe call.completion.session [],
      SourceCall anchor header invocation ⟨[]⟩ arguments (.value scalar.source) after.heap := by
  have _ := simple
  exact SelectedCompilationPublicSessionInitialDataScalarStep.first_scalar
    rows prepared anchor header support distinct scalar call returned start inputTypes inputMeanings rawType nativeType descriptor invocation

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicSessionInitialScalarStep
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicSessionInitialFailureForward
/-! An initial Source fault supplies sufficient execution fuel and retains the
exact failed session, decoded reason and physical state with no handles. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicSessionInitialFailureForward
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
  (selectedBodies : Staging.Recursive.SelectedPreservation.SelectedBodies
    (Program.ofChecked recipe.compiled.sourceProgram)
    (SelectedCompilationPhysicalProgramSupport.stages recipe.compiled))
  {publicArtifact : SourceCoreExecution.Artifact}
  {session : SourceCoreExecution.Session publicArtifact}
  {key : SourceCoreIndexedSession.Key} {publicArguments : List SourceCorePublicValues.Value}
  {options : SourceCoreExecution.RunOptions}

include selectedBodies in
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
    SelectedCompilationPublicSessionFailureForward.FailureForwardAt (entries := [])
      rows anchor initial support.profile recipe failure call after := by
  have _ := simple
  exact SelectedCompilationPublicSessionInitialDataFailureForward.first_failure
    rows prepared anchor header support selectedBodies distinct call start inputTypes inputMeanings trace

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicSessionInitialFailureForward
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicSessionInitialFailureStep
/-! A completed initial failure reflects the original staged Source fault and
retains its exact physical state without any prior or fabricated handle. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicSessionInitialFailureStep
open Core Frontend SourceInference
open CallableIndexedOwnedPreparedFiniteNamedInventories (Input Inventory headers)
open CallableIndexedOwnedFunctionValues (Header)
open CallableIndexedOwnedPreparedBootstrapRootState (keys)
open SelectedCompilationPublicSessionState (StartedCall Call State SourceCall)
open SelectedCompilationPublicSessionInitial (Started)
open SelectedCompilationPhysicalProgramSupport (Support stagePrepared)

variable {recipe : SourceCoreIndexedSession.Recipe}
  {inputs : List (Input recipe.compiled)} (rows : Inventory inputs)
  (prepared : SourceCoreIndexedSession.Recipe.prepare recipe.compiled = .ok recipe)
  (anchor header : Header recipe.compiled (Program.ofChecked recipe.compiled.sourceProgram))
  {initial : CallableIndexedOwnedPublicFaultReceivers.Receiver recipe.compiled.indexed}
  (support : Support recipe.compiled (headers rows) (keys recipe.compiled) initial)
  (selectedBodies : Staging.Recursive.SelectedPreservation.SelectedBodies
    (Program.ofChecked recipe.compiled.sourceProgram)
    (SelectedCompilationPhysicalProgramSupport.stages recipe.compiled))
  {publicArtifact : SourceCoreExecution.Artifact}
  {session : SourceCoreExecution.Session publicArtifact}
  {key : SourceCoreIndexedSession.Key} {publicArguments : List SourceCorePublicValues.Value}
  {options : SourceCoreExecution.RunOptions}

include selectedBodies in
theorem first_failure
    (distinct : (inputs.map (fun input => input.prepared.index)).Nodup)
    (call : StartedCall session key publicArguments options)
    (returned : SourceCoreExecution.Session publicArtifact) (reason : Word)
    (failedCall : session.RunAt key publicArguments options (.ok (.failed reason returned)))
    (start : Started rows prepared header call)
    (simple : ∀ value ∈ publicArguments, SourceCoreIndexedSession.SimplePublic value)
    (inputTypes : RecursiveNamedPublicDataArgumentReceipts.PublicDataTypes
      header.function.context publicArguments header.types)
    {arguments : List Dynamic.Value}
    (inputMeanings : RecursiveNamedPublicDataInputs.Meanings publicArguments arguments)
    (descriptor : SourceCoreCallableContracts.Descriptor recipe.compiled.indexed.ancestry.graph.inputs.callable.table
      (.named header.named.signature.key))
    (invocation : Staging.Recursive.Scope) :
    ∃ failure, ∃ after : State rows anchor initial support.profile recipe returned [],
      SourceCall anchor header invocation ⟨[]⟩ arguments (.fault failure) after.heap ∧
      CallableIndexedOwnedPublicDecodedStagedCallFaults.faults after.receiving.result.diagnostics failure reason := by
  have _ := simple
  exact SelectedCompilationPublicSessionInitialDataFailureStep.first_failure
    rows prepared anchor header support selectedBodies distinct call returned reason failedCall start inputTypes inputMeanings descriptor invocation

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicSessionInitialFailureStep
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicSessionRegistryFailureForward
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicSessionFailureForward
open Core Frontend SourceInference
open CallableIndexedOwnedPreparedFiniteNamedInventories (Input Inventory headers)
open CallableIndexedOwnedPreparedBootstrapRootState (keys)
open CallableIndexedOwnedFunctionValues (Header)
open SelectedCompilationPublicSessionState
open SelectedCompilationPhysicalProgramSupport (stagePrepared)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {inputs : List (Input compiled)} {rows : Inventory inputs}
  {anchor : Header compiled (Program.ofChecked compiled.sourceProgram)}
  {initial : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
  {profile : compiled.compatible.checked.catalog.callableContracts = true}
  {recipe : SourceCoreIndexedSession.Recipe}
theorem forward_call_at_input_registry (support : SelectedCompilationPhysicalProgramSupport.Support compiled (headers rows) (keys compiled) initial)
    (selectedBodies : Staging.Recursive.SelectedPreservation.SelectedBodies
      (Program.ofChecked compiled.sourceProgram)
      (SelectedCompilationPhysicalProgramSupport.stages compiled))
    (prepared : SourceCoreIndexedSession.Recipe.prepare compiled = .ok recipe)
    {options : SourceCoreExecution.RunOptions}
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    {entries : List RecursiveNamedPublicFunctionHistory.Entry}
    (state : State rows anchor initial profile recipe session entries)
    {key : SourceCoreIndexedSession.Key} {publicArguments : List SourceCorePublicValues.Value}
    (call : StartedCall session key publicArguments options)
    (request : RecursiveNamedPublicHistoryFrontdoor.Started (headers rows) prepared
      call.checkpoint state.session key publicArguments options.inputValidationFuel state.world state.store)
    {arguments : List Dynamic.Value}
    (inputs : RecursiveNamedPublicFunctionHistoryInputs.Inputs entries request.header.function.context
      (request.header.bindings.map (fun binding => binding.1.scheme.body)) publicArguments arguments)
    (ready : session.ExportsReady)
    {invocation : Staging.Recursive.Scope} {after : Dynamic.Heap} {failure : Staging.Recursive.Failure}
    (trace : SourceCall anchor request.header invocation state.heap arguments (.fault failure) after) :
    FailureForwardAt (entries := entries) rows anchor initial profile recipe failure call after := by
  have sameCompiled := SourceCoreIndexedSession.Recipe.prepare_compiled prepared
  cases sameCompiled
  obtain ⟨receiving, contextAt, issued, extension, history⟩ := state.at_named_request prepared request
  have registry : request.encodedValues.registry = receiving.result.context.registry :=
    (congrArg SourceCoreCompatibleValues.Context.registry contextAt).symm
  have metadata : SourceCoreRawMetadata.Extends request.encodedValues.registry receiving.result.context.registry := by
    rw [registry]; exact .refl _
  obtain ⟨stable, heaps, heapTyped, represented, argumentsTyped⟩ :=
    SelectedCompilationPublicClosureHistory.History.current_arguments
      (profile := profile)
      (bodyTyping := support.bodyTyping) (prepared := prepared)
      (selected := request.selected) (history := history)
      (started := request.started) (inputReceipts := inputs) (metadata := metadata)
  have globalReference := CallableIndexedOwnedPreparedBootstrapGlobalReferences.global_reference
    rows request.header request.selected.member
  have supports := (SelectedCompilationPublicReturnedValues.header_context_supports
    request.header anchor support.bodyTyping).2
  obtain ⟨rawD, function, sourceSize, sourceAt, applied⟩ := trace
  obtain ⟨capture, value, finalStore, finalMap, finalWorld, requiredExecution, enough, result⟩ :=
    SelectedCompilationPublicBodyInvocationBounds.preserves_root
      (stagePrepared := stagePrepared recipe.compiled) (completion := receiving)
      (functions := functions rows initial profile)
      (owner := CallableIndexedOwnedPreparedBootstrapRootState.owner recipe.compiled)
      (packet := support.bodies request.header request.selected.member) (preservesBodies := fun budget {child} selected =>
        SelectedCompilationPhysicalProgramSupport.preserves_bodies support issued
          extension request.header request.selected.member selected budget)
      (keyPhysical := CallableIndexedOwnedPreparedPhysicalBootstrap.key_physical _ _)
      (physical := history.physical)
      (bodyTyping := support.bodyTyping)
      (selected := request.selected) (caller := state.caller)
      (globalReference := globalReference) (stable := stable) (heapTyped := heapTyped)
      (represented := represented) (argumentsTyped := argumentsTyped) (heaps := heaps)
      (sourceAt := sourceAt) (supports := supports) applied
  obtain ⟨token, rfl, faultRelated⟩ : ∃ token,
      value = .inLeft request.header.output (.word token) ∧
      CallableIndexedOwnedPublicDecodedStagedCallFaults.faults receiving.result.diagnostics failure token := by
    have related := result.2.1
    cases related with
    | fault related => exact ⟨_, rfl, related⟩
  have completes : ∀ executionFuel, requiredExecution ≤ executionFuel →
      request.checkpoint.NativeDone executionFuel (.inLeft request.header.output (.word token)) finalStore :=
    fun fuel bound => request.started.initial.native_done_iff.mpr (enough fuel bound)
  have contextSupports := (SelectedCompilationPublicReturnedValues.header_context_supports
    request.header anchor support.bodyTyping).1
  have callerHeap := heapTyped.transportContext contextSupports
  have callerArguments := argumentsTyped.transportContext contextSupports
  obtain ⟨packed, packing⟩ := Dynamic.ValuesPack.exists_pack arguments
  have preserved := Staging.Recursive.SelectedPreservation.applies_fault selectedBodies
    (SelectedCompilationPublicHistorySourceInputs.header_runtime support.bodyTyping anchor) callerHeap
    (SelectedCompilationPublicHistorySourceInputs.source_typed support.bodyTyping sourceAt anchor state.heap)
    packing (packing.hasType callerArguments) applied
  have checkpointReady := request.started.original.initial_registry.exportsReady (state.atSession.exportsReady_iff.mp ready)
  refine ⟨requiredExecution, token, ?_⟩
  intro executionFuel outputFuel outcome executionBound resumed
  have completed := completes executionFuel executionBound
  obtain ⟨returned, outcomeEq⟩ := resumed.native_failed request.atCheckpoint completed rfl
  have failedResume : call.checkpoint.ResumeAt executionFuel outputFuel (.failed token returned) := outcomeEq ▸ resumed
  obtain ⟨actual, _generation, actualValue, actualStore, actualCompleted, failed, returnedAt⟩ :=
    failedResume.indexed_failed request.atCheckpoint
  have same := completed.symm.trans actualCompleted
  cases same
  obtain ⟨reached, _related, retained⟩ := history.semantic.after_failure
    rfl request.started request.selected failed result preserved.1
  have physicalRetained := history.after_result result retained
  have returnedRegistry : actual.RegistryAt receiving.result.context.registry := by
    rw [← registry]
    exact congrArg SourceCoreCompatibleValues.Context.registry (failed.2.2.2.2.1.trans request.started.values)
  let next : State rows anchor initial profile recipe returned entries := {
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
    extension := extension
    registry := returnedRegistry
    history := physicalRetained }
  exact ⟨returned, outcomeEq, returnedAt.exportsReady_iff.mpr (failed.exportsReady checkpointReady),
    next, rfl, faultRelated⟩


end Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicSessionFailureForward
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicSessionRegistryFailureStep
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicSessionFailureStep
open Core Frontend SourceInference
open CallableIndexedOwnedPreparedFiniteNamedInventories (Input Inventory headers)
open CallableIndexedOwnedPreparedBootstrapRootState (keys)
open CallableIndexedOwnedFunctionValues (Header)
open SelectedCompilationPublicSessionState
open SelectedCompilationPhysicalProgramSupport (stagePrepared)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {inputs : List (Input compiled)} {rows : Inventory inputs}
  {anchor : Header compiled (Program.ofChecked compiled.sourceProgram)}
  {initial : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
  {profile : compiled.compatible.checked.catalog.callableContracts = true}
  {recipe : SourceCoreIndexedSession.Recipe}
theorem State.failed_call_at_input_registry (support : SelectedCompilationPhysicalProgramSupport.Support compiled (headers rows) (keys compiled) initial)
    (selectedBodies : Staging.Recursive.SelectedPreservation.SelectedBodies
      (Program.ofChecked compiled.sourceProgram)
      (SelectedCompilationPhysicalProgramSupport.stages compiled))
    (prepared : SourceCoreIndexedSession.Recipe.prepare compiled = .ok recipe)
    {options : SourceCoreExecution.RunOptions}
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    {entries : List RecursiveNamedPublicFunctionHistory.Entry}
    (state : State rows anchor initial profile recipe session entries)
    {key : SourceCoreIndexedSession.Key} {publicArguments : List SourceCorePublicValues.Value}
    (call : StartedCall session key publicArguments options)
    (returned : SourceCoreExecution.Session artifact) (reason : Word)
    (failedCall : session.RunAt key publicArguments options (.ok (.failed reason returned)))
    (request : RecursiveNamedPublicHistoryFrontdoor.Started (headers rows) prepared
      call.checkpoint state.session key publicArguments options.inputValidationFuel state.world state.store)
    {arguments : List Dynamic.Value}
    (inputs : RecursiveNamedPublicFunctionHistoryInputs.Inputs entries request.header.function.context
      (request.header.bindings.map (fun binding => binding.1.scheme.body)) publicArguments arguments)
    (descriptor : SourceCoreCallableContracts.Descriptor compiled.indexed.ancestry.graph.inputs.callable.table
      (.named request.header.named.signature.key))
    (invocation : Staging.Recursive.Scope) :
    ∃ failure, ∃ after : State rows anchor initial profile recipe returned entries,
      SourceCall anchor request.header invocation state.heap arguments
        (.fault failure) after.heap ∧
      CallableIndexedOwnedPublicDecodedStagedCallFaults.faults
        after.receiving.result.diagnostics failure reason := by
  have sameCompiled := SourceCoreIndexedSession.Recipe.prepare_compiled prepared
  cases sameCompiled
  obtain ⟨receiving, contextAt, issued, extension, history⟩ := state.at_named_request prepared request
  have registry : request.encodedValues.registry = receiving.result.context.registry :=
    (congrArg SourceCoreCompatibleValues.Context.registry contextAt).symm
  have metadata : SourceCoreRawMetadata.Extends request.encodedValues.registry receiving.result.context.registry := by
    rw [registry]; exact .refl _
  obtain ⟨stable, heaps, heapTyped, represented, argumentsTyped⟩ :=
    SelectedCompilationPublicClosureHistory.History.current_arguments
      (profile := profile)
      (bodyTyping := support.bodyTyping) (prepared := prepared)
      (selected := request.selected) (history := history)
      (started := request.started) (inputReceipts := inputs) (metadata := metadata)
  have globalReference := CallableIndexedOwnedPreparedBootstrapGlobalReferences.global_reference
    rows request.header request.selected.member
  have supports := (SelectedCompilationPublicReturnedValues.header_context_supports
    request.header anchor support.bodyTyping).2
  obtain ⟨actual, native, finalStore, capture, sourceSize, outcome, after,
      finalMap, finalWorld, failed, returnedAt, trace, result⟩ :=
    SelectedCompilationPublicBodyInvocationBounds.public_run_failed_reflects
      (stagePrepared := stagePrepared recipe.compiled) (completion := receiving)
      (functions := functions rows initial profile)
      (owner := CallableIndexedOwnedPreparedBootstrapRootState.owner recipe.compiled)
      (packet := support.bodies request.header request.selected.member) (reflectsBodies := fun budget {child} selected =>
        SelectedCompilationPhysicalProgramSupport.reflects_bodies support issued
          extension request.header request.selected.member selected budget)
      (keyPhysical := CallableIndexedOwnedPreparedPhysicalBootstrap.key_physical _ _)
      (physical := history.physical)
      (bodyTyping := support.bodyTyping)
      (selected := request.selected) (caller := state.caller)
      (globalReference := globalReference) (stable := stable) (heapTyped := heapTyped)
      (represented := represented) (argumentsTyped := argumentsTyped) (heaps := heaps)
      (sourceAt := request.sourceAt) (supports := supports)
      (sameCompiled := SourceCoreIndexedSession.Recipe.prepare_compiled prepared)
      (started := request.started) (invocation := invocation)
      call.started request.atCheckpoint failedCall descriptor
  obtain ⟨failure, outcomeEq⟩ : ∃ failure, outcome = .fault failure := by
    have represented := result.2.1
    cases represented with
    | value _ => have impossible := failed.2.1; cases impossible
    | fault _ => exact ⟨_, rfl⟩
  subst outcome
  have fault : CallableIndexedOwnedPublicDecodedStagedCallFaults.faults
      receiving.result.diagnostics failure reason := by
    have represented := result.2.1
    cases represented with
    | fault matched =>
      have decoded := failed.2.1
      simp only [Core.LanguageResult.decode?] at decoded
      cases decoded
      exact matched
  have contexts := (SelectedCompilationPublicReturnedValues.header_context_supports
    request.header anchor support.bodyTyping).1
  have callerHeap := heapTyped.transportContext contexts
  have callerArguments := argumentsTyped.transportContext contexts
  obtain ⟨packed, packing⟩ := Dynamic.ValuesPack.exists_pack arguments
  have preserved := Staging.Recursive.SelectedPreservation.applies_fault selectedBodies
    (SelectedCompilationPublicHistorySourceInputs.header_runtime support.bodyTyping anchor) callerHeap
    (SelectedCompilationPublicHistorySourceInputs.source_typed support.bodyTyping request.sourceAt anchor state.heap)
    packing (packing.hasType callerArguments) trace
  obtain ⟨reached, _related, retained⟩ := history.semantic.after_failure
    (SourceCoreIndexedSession.Recipe.prepare_compiled prepared) request.started request.selected
    failed result preserved.1
  have physicalRetained := history.after_result result retained
  have returnedRegistry : actual.RegistryAt receiving.result.context.registry := by
    have actualValues := failed.2.2.2.2.1.trans request.started.values
    exact (congrArg SourceCoreCompatibleValues.Context.registry actualValues).trans registry
  let next : State rows anchor initial profile recipe returned entries := {
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
    extension := extension
    registry := returnedRegistry
    history := physicalRetained }
  exact ⟨failure, next, ⟨request.rawD, request.function, sourceSize, request.sourceAt, trace⟩, fault⟩


end Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicSessionFailureStep
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicSessionInitialExportForward
/-! Independent initial Source success determines execution and export budgets.
Every sufficiently fueled public resume reimports its actual exported handle
at the same output budget, retaining the exact Source heap and physical cells. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicSessionInitialExportForward
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

theorem first_function
    (distinct : (inputs.map (fun input => input.prepared.index)).Nodup)
    (call : StartedCall session key publicArguments options)
    (start : Started rows prepared header call)
    (simple : ∀ value ∈ publicArguments, SourceCoreIndexedSession.SimplePublic value)
    (inputTypes : RecursiveNamedPublicDataArgumentReceipts.PublicDataTypes
      header.function.context publicArguments header.types)
    {arguments : List Dynamic.Value}
    (inputMeanings : RecursiveNamedPublicDataInputs.Meanings publicArguments arguments)
    {parameter resultType : TypeSystem.Ty}
    (functionResult : SourceCoreRawMetadata.runtimeType header.function.resultType = .function parameter resultType)
    {invocation : Staging.Recursive.Scope} {after : Dynamic.Heap} {source : Dynamic.Value}
    (trace : SourceCall anchor header invocation ⟨[]⟩ arguments (.value source) after) :
    SelectedCompilationPublicSessionExportForward.ForwardAt rows anchor initial support.profile
      recipe [] call.checkpoint header.function.resultType source after := by
  have startupRegistry := start.registry rows prepared header simple
  have metadata : SourceCoreRawMetadata.Extends start.encodedValues.registry initial.result.context.registry := by
    rw [startupRegistry, support.registry]
    exact .refl _
  obtain ⟨caller, stable, globalReference, heaps, heapTyped, represented, argumentsTyped⟩ :=
    SelectedCompilationPublicInitialArguments.initial_data_arguments
      (inputs := inputs) (rows := rows) (distinct := distinct) (completion := initial)
      (profile := support.profile) (bodyRegistry := initial.result.context.registry)
      (semanticFaults := CallableIndexedOwnedPublicDecodedCallFaults.faults initial.result.diagnostics)
      (bodyTyping := support.bodyTyping) (prepared := prepared) (selected := start.selected)
      (opened := start.opened) (fresh := start.fresh) (ready := start.ready)
      (sameRuntime := SourceCoreExecution.Session.SameRuntime.refl session) (atSession := start.atSession)
      (started := start.started) (inputTypes := inputTypes) (inputMeanings := inputMeanings) (metadata := metadata)
  obtain ⟨rawD, function, sourceSize, sourceAt, applied⟩ := trace
  obtain ⟨capture, value, finalStore, finalMap, finalWorld, requiredExecution, enough, result⟩ :=
    SelectedCompilationPublicBodyInvocationBounds.preserves_root
      (stagePrepared := stagePrepared recipe.compiled) (completion := initial)
      (functions := SelectedCompilationPhysicalProgramSupport.functions support)
      (owner := CallableIndexedOwnedPreparedBootstrapRootState.owner recipe.compiled)
      (packet := support.bodies header start.selected.member)
      (preservesBodies := fun budget {child} selected =>
        SelectedCompilationPhysicalProgramSupport.preserves_bodies support support.issued (.refl _)
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
      initial.result.context.registry (SelectedCompilationPhysicalProgramSupport.functions support)
      finalMap finalWorld header.function.resultType source payload header.output := by
    have representedResult := result.2.1
    cases representedResult with
    | value related => exact related
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
  refine ⟨requiredExecution, max requiredOutput 1, ?_⟩
  intro executionFuel outputFuel outcome executionBound outputBound resumed
  obtain ⟨completion, actual, generation, succeeded, exported, actualAt, returnedReady⟩ :=
    exports executionFuel (completes executionFuel executionBound) outputFuel (Nat.le_trans (Nat.le_max_left _ _) outputBound) outcome resumed
  obtain ⟨exportedCompletion, handle, sameOutcome, functionValue, handleType, _ready⟩ :=
    SourceCoreExecution.Checkpoint.ResumeAt.runtime_function_succeeded start.atCheckpoint resumed checkpointReady
      (completes executionFuel executionBound) requested functionResult (by omega)
  have sameCompletion : exportedCompletion = completion :=
    SourceCoreExecution.Outcome.succeeded.inj (sameOutcome.symm.trans succeeded)
  subst exportedCompletion
  obtain ⟨reached, related, post⟩ := result.2.2.2.2.2.2.2
  have retained := RecursiveNamedPublicFunctionHistory.History.first rfl start.started start.selected exported result
    reached ⟨related, post⟩ .skip
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
  have encoded := (exported.reimports_payload requested rfl).2
  rw [← actualAt.1] at encoded
  exact ⟨completion, succeeded, handle, functionValue, handleType,
    actualAt.2.2.2.exportsReady_iff.mpr returnedReady, returned, rfl,
    payload, _, encoded, representedResult⟩

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicSessionInitialExportForward
end
