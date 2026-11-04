import Solcore.SourceSemantics.CoreLowering.Internal.Selected.StagePublicInputs
import Solcore.SourceSemantics.CoreLowering.PublicSessions
import Solcore.SourceSemantics.CoreLowering.Internal.Selected.PublicSessionSteps
import Solcore.SourceSemantics.CoreLowering.Internal.Selected.PublicDirectSessions
import Solcore.SourceSemantics.CoreLowering.Internal.Selected.NamedAdmission
import Solcore.SourceSemantics.CoreLowering.CompatiblePublicOutputShapes
import Solcore.SourceSemantics.CoreLowering.PublicSessionOutcomes
import Solcore.SourceSemantics.CoreLowering.Internal.Selected.PublicDirectBounds
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicActualRegistryNamedOutputPreservation
import Solcore.SourceSemantics.CoreLowering.PublicSupport
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicScalarResults
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicActualRegistryStart
import Solcore.SourceSemantics.CoreLowering.Internal.Selected.MethodRoots

/-!
# Public outputs of closed staged bodies

Ordinary Source success determines the complete public value, including its metadata
and the callable leaves retained for later calls. These are the last links of the
profiled-session route.

Main declarations:
- `SelectedCompilationStageClosedPublicForward.scalar`,
  `SelectedCompilationStageClosedPublicForward.function` and
  `SelectedCompilationStageClosedPublicForward.fault`, later calls;
- `SelectedCompilationStageClosedInitialForward.scalar`,
  `SelectedCompilationStageClosedInitialForward.function` and
  `SelectedCompilationStageClosedInitialForward.fault`, the first call;
- `SelectedCompilationStageClosedDirectForward.output`, direct calls through a handle;
- `SelectedCompilationStageClosedOutputForward.initial` and
  `SelectedCompilationStageClosedOutputForward.later`, the complete public value;
- `SelectedCompilationCertifiedPublicSession.Initial.forward_data_output_plain` and
  `SelectedCompilationCertifiedPublicSession.Initial.reflect_data_output_plain`, inputs of
  structured data;
- `SelectedCompilationCertifiedPublicSession.Profiled.reflect_output_plain`, a public
  output reflected back to Source.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationStagePublicForward
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationStagePublicForward
open Core Frontend SourceInference
open CallableIndexedOwnedPreparedFiniteNamedInventories (headers)
open CallableIndexedOwnedFunctionValues (Header)
open SelectedCompilationPublicSessionState
open SelectedCompilationCertifiedPublicSession (Profiled)
open SelectedCompilationStagePublicInputLifting
open RecursiveNamedPublicScalarResults (ScalarOutput)

variable {recipe : SourceCoreIndexedSession.Recipe} (issued : Profiled recipe)
  {anchor : Header recipe.compiled (Program.ofChecked recipe.compiled.sourceProgram)}
  {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
  {entries : List RecursiveNamedPublicFunctionHistory.Entry}
  {key : SourceCoreIndexedSession.Key} {publicArguments : List SourceCorePublicValues.Value}
  {options : SourceCoreExecution.RunOptions}

/-- A stage stop retains the actual rejected guard, exact reached Source heap
and a public failure bound independent of output-validation fuel. -/
def StageStopped (state : issued.toIssued.State anchor session entries)
    (call : StartedCall session key publicArguments options)
    (header : Header recipe.compiled (Program.ofChecked recipe.compiled.sourceProgram))
    (invocation : Staging.Recursive.Scope) (arguments : List Dynamic.Value) : Prop :=
  ∃ origin occurrence reason reached,
    Staging.Recursive.Generated origin occurrence reason ∧
    SourceCall anchor header invocation state.heap arguments (.fault (.stage origin occurrence reason)) reached ∧
    SelectedCompilationPublicSessionFailureForward.FailureForwardAt (entries := entries)
      issued.catalog.rows anchor issued.initial issued.support.profile recipe
      (.stage origin occurrence reason) call reached

variable (bodies : NamedBodies issued.support)
  (state : issued.toIssued.State anchor session entries)
  (call : StartedCall session key publicArguments options)
  (request : RecursiveNamedPublicHistoryFrontdoor.Started (headers issued.catalog.rows) issued.prepared
    call.checkpoint state.session key publicArguments options.inputValidationFuel state.world state.store)
  {arguments : List Dynamic.Value}
  (inputs : RecursiveNamedPublicFunctionHistoryInputs.Inputs entries request.header.function.context
    (request.header.bindings.map (fun binding => binding.1.scheme.body)) publicArguments arguments)
  (ready : session.ExportsReady)
  {invocation : Staging.Recursive.Scope} {after : Dynamic.Heap}

include bodies inputs ready in
/-- An ordinary scalar application completes publicly with the same value
and heap, unless an authentic earlier stage check rejects the call. -/
theorem scalar (scalar : ScalarOutput)
    (rawType : request.header.function.resultType = scalar.sourceType)
    (nativeType : request.header.output = scalar.nativeType)
    (trace : PlainValue anchor request.header invocation state.heap arguments scalar.source after) :
    (SourceCall anchor request.header invocation state.heap arguments (.value scalar.source) after ∧
      SelectedCompilationPublicSessionScalarForward.ForwardAt (entries := entries)
        issued.catalog.rows anchor issued.initial issued.support.profile recipe scalar call after) ∨
    StageStopped issued state call request.header invocation arguments := by
  obtain ⟨staged, reached, lifted, adapted⟩ := lift_call_at_input_registry issued.support bodies
    issued.prepared state call request inputs (plain_value trace)
  cases adapted with
  | completed =>
    exact .inl ⟨lifted, SelectedCompilationPublicSessionScalarForward.forward_call_at_input_registry
      issued.support issued.prepared state scalar call request inputs rawType nativeType ready lifted⟩
  | rejected origin occurrence reason reached =>
    exact .inr ⟨origin, occurrence, reason, reached, lifted.failure_plain, lifted,
      SelectedCompilationPublicSessionFailureForward.forward_call_at_input_registry
        issued.support issued.registryBodies issued.prepared state call request inputs ready lifted⟩

include bodies inputs ready in
/-- Ordinary semantic failure preserves its reason and reached heap, with
an explicit alternative for a genuine earlier stage rejection. -/
theorem fault (reason : Dynamic.SemanticFault)
    (trace : PlainFault anchor request.header invocation state.heap arguments reason after) :
    (SourceCall anchor request.header invocation state.heap arguments (.fault (.semantic reason)) after ∧
      SelectedCompilationPublicSessionFailureForward.FailureForwardAt (entries := entries)
        issued.catalog.rows anchor issued.initial issued.support.profile recipe (.semantic reason) call after) ∨
    StageStopped issued state call request.header invocation arguments := by
  obtain ⟨staged, reached, lifted, adapted⟩ := lift_call_at_input_registry issued.support bodies
    issued.prepared state call request inputs (plain_fault trace)
  cases adapted with
  | completed =>
    exact .inl ⟨lifted, SelectedCompilationPublicSessionFailureForward.forward_call_at_input_registry
      issued.support issued.registryBodies issued.prepared state call request inputs ready lifted⟩
  | rejected origin occurrence reason reached =>
    exact .inr ⟨origin, occurrence, reason, reached, lifted.failure_plain, lifted,
      SelectedCompilationPublicSessionFailureForward.forward_call_at_input_registry
        issued.support issued.registryBodies issued.prepared state call request inputs ready lifted⟩

include bodies inputs ready in
/-- The actual returned function can be exported and imported again at the
same output budget while preserving every earlier retained handle. -/
theorem function {parameterType resultType : TypeSystem.Ty} {value : Dynamic.Value}
    (rawType : request.header.function.resultType = .function parameterType resultType)
    (trace : PlainValue anchor request.header invocation state.heap arguments value after) :
    (SourceCall anchor request.header invocation state.heap arguments (.value value) after ∧
      SelectedCompilationPublicSessionExportForward.ForwardAt
        issued.catalog.rows anchor issued.initial issued.support.profile recipe entries call.checkpoint
        (.function parameterType resultType) value after) ∨
    StageStopped issued state call request.header invocation arguments := by
  obtain ⟨staged, reached, lifted, adapted⟩ := lift_call_at_input_registry issued.support bodies
    issued.prepared state call request inputs (plain_value trace)
  cases adapted with
  | completed =>
    exact .inl ⟨lifted, SelectedCompilationPublicSessionExportForward.forward_function_at_input_registry
      issued.support issued.prepared state call request inputs rawType ready lifted⟩
  | rejected origin occurrence reason reached =>
    exact .inr ⟨origin, occurrence, reason, reached, lifted.failure_plain, lifted,
      SelectedCompilationPublicSessionFailureForward.forward_call_at_input_registry
        issued.support issued.registryBodies issued.prepared state call request inputs ready lifted⟩

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationStagePublicForward
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageClosedPublicForward
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageClosedPublicForward
open Core Frontend SourceInference
open CallableIndexedOwnedPreparedFiniteNamedInventories (headers)
open CallableIndexedOwnedFunctionValues (Header)
open SelectedCompilationPublicSessionState
open SelectedCompilationCertifiedPublicSession (Profiled)
open SelectedCompilationStagePublicInputLifting
open RecursiveNamedPublicScalarResults (ScalarOutput)

variable {recipe : SourceCoreIndexedSession.Recipe} (issued : Profiled recipe)
  {anchor : Header recipe.compiled (Program.ofChecked recipe.compiled.sourceProgram)}
  {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
  {entries : List RecursiveNamedPublicFunctionHistory.Entry}
  {key : SourceCoreIndexedSession.Key} {publicArguments : List SourceCorePublicValues.Value}
  {options : SourceCoreExecution.RunOptions}

open SelectedCompilationStagePublicForward (StageStopped)

variable (state : issued.toIssued.State anchor session entries)
  (call : StartedCall session key publicArguments options)
  (request : RecursiveNamedPublicHistoryFrontdoor.Started (headers issued.catalog.rows) issued.prepared
    call.checkpoint state.session key publicArguments options.inputValidationFuel state.world state.store)
  {arguments : List Dynamic.Value}
  (inputs : RecursiveNamedPublicFunctionHistoryInputs.Inputs entries request.header.function.context
    (request.header.bindings.map (fun binding => binding.1.scheme.body)) publicArguments arguments)
  (ready : session.ExportsReady)
  {invocation : Staging.Recursive.Scope} {after : Dynamic.Heap}

include inputs ready in
/-- An ordinary scalar application completes publicly with the same value
and heap, unless an authentic earlier stage check rejects the call. -/
theorem scalar (scalar : ScalarOutput)
    (rawType : request.header.function.resultType = scalar.sourceType)
    (nativeType : request.header.output = scalar.nativeType)
    (trace : PlainValue anchor request.header invocation state.heap arguments scalar.source after) :
    (SourceCall anchor request.header invocation state.heap arguments (.value scalar.source) after ∧
      SelectedCompilationPublicSessionScalarForward.ForwardAt (entries := entries)
        issued.catalog.rows anchor issued.initial issued.support.profile recipe scalar call after) ∨
    StageStopped issued state call request.header invocation arguments := by
  obtain ⟨staged, reached, lifted, adapted⟩ := lift_call_at_input_registry issued.support
    (SelectedCompilationStagePublicProgramLifting.named_bodies issued.support)
    issued.prepared state call request inputs (plain_value trace)
  cases adapted with
  | completed =>
    exact .inl ⟨lifted, SelectedCompilationPublicSessionScalarForward.forward_call_at_input_registry
      issued.support issued.prepared state scalar call request inputs rawType nativeType ready lifted⟩
  | rejected origin occurrence reason reached =>
    exact .inr ⟨origin, occurrence, reason, reached, lifted.failure_plain, lifted,
      SelectedCompilationPublicSessionFailureForward.forward_call_at_input_registry
        issued.support issued.registryBodies issued.prepared state call request inputs ready lifted⟩

include inputs ready in
/-- Ordinary semantic failure preserves its reason and reached heap, with
an explicit alternative for a genuine earlier stage rejection. -/
theorem fault (reason : Dynamic.SemanticFault)
    (trace : PlainFault anchor request.header invocation state.heap arguments reason after) :
    (SourceCall anchor request.header invocation state.heap arguments (.fault (.semantic reason)) after ∧
      SelectedCompilationPublicSessionFailureForward.FailureForwardAt (entries := entries)
        issued.catalog.rows anchor issued.initial issued.support.profile recipe (.semantic reason) call after) ∨
    StageStopped issued state call request.header invocation arguments := by
  obtain ⟨staged, reached, lifted, adapted⟩ := lift_call_at_input_registry issued.support
    (SelectedCompilationStagePublicProgramLifting.named_bodies issued.support)
    issued.prepared state call request inputs (plain_fault trace)
  cases adapted with
  | completed =>
    exact .inl ⟨lifted, SelectedCompilationPublicSessionFailureForward.forward_call_at_input_registry
      issued.support issued.registryBodies issued.prepared state call request inputs ready lifted⟩
  | rejected origin occurrence reason reached =>
    exact .inr ⟨origin, occurrence, reason, reached, lifted.failure_plain, lifted,
      SelectedCompilationPublicSessionFailureForward.forward_call_at_input_registry
        issued.support issued.registryBodies issued.prepared state call request inputs ready lifted⟩

include inputs ready in
/-- The actual returned function can be exported and imported again at the
same output budget while preserving every earlier retained handle. -/
theorem function {parameterType resultType : TypeSystem.Ty} {value : Dynamic.Value}
    (rawType : request.header.function.resultType = .function parameterType resultType)
    (trace : PlainValue anchor request.header invocation state.heap arguments value after) :
    (SourceCall anchor request.header invocation state.heap arguments (.value value) after ∧
      SelectedCompilationPublicSessionExportForward.ForwardAt
        issued.catalog.rows anchor issued.initial issued.support.profile recipe entries call.checkpoint
        (.function parameterType resultType) value after) ∨
    StageStopped issued state call request.header invocation arguments := by
  obtain ⟨staged, reached, lifted, adapted⟩ := lift_call_at_input_registry issued.support
    (SelectedCompilationStagePublicProgramLifting.named_bodies issued.support)
    issued.prepared state call request inputs (plain_value trace)
  cases adapted with
  | completed =>
    exact .inl ⟨lifted, SelectedCompilationPublicSessionExportForward.forward_function_at_input_registry
      issued.support issued.prepared state call request inputs rawType ready lifted⟩
  | rejected origin occurrence reason reached =>
    exact .inr ⟨origin, occurrence, reason, reached, lifted.failure_plain, lifted,
      SelectedCompilationPublicSessionFailureForward.forward_call_at_input_registry
        issued.support issued.registryBodies issued.prepared state call request inputs ready lifted⟩

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageClosedPublicForward
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageClosedDirectForward
/-! A complete returned value retains its actual reimport receipt and Source
representation, alongside ordered selection of nested exported callables. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageClosedDirectForward.Output
open Core Frontend SourceInference
open CallableIndexedOwnedPreparedFiniteNamedInventories (Input Inventory headers)
open CallableIndexedOwnedPreparedBootstrapRootState (keys)
open CallableIndexedOwnedFunctionValues (Header)
open RecursiveNamedPublicFunctionHistory (Entry)
open SelectedCompilationPublicSessionState
open RecursiveNamedPublicNestedOutputSelections (Selection)
open SelectedCompilationPublicSessionDirectOutputCollection (SelectedAt selected_of_cast)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {inputs : List (Input compiled)} {rows : Inventory inputs}
  {anchor : Header compiled (Program.ofChecked compiled.sourceProgram)}
  {initial : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
  {profile : compiled.compatible.checked.catalog.callableContracts = true}
  {recipe : SourceCoreIndexedSession.Recipe}

/-- Host and Source raw types retain their actual compatibility equality. -/
def ReturnedValue
    {artifact : SourceCoreExecution.Artifact}
    (completion : SourceCoreExecution.Completion artifact) {entries : List Entry}
    (state : State rows anchor initial profile recipe completion.session entries)
    (sourceType : TypeSystem.Ty) (source : Dynamic.Value) (fuel : Nat) : Prop :=
  ∃ hostType payload nativeType,
    SourceCoreRawMetadata.runtimeType hostType = SourceCoreRawMetadata.runtimeType sourceType ∧
    state.session.EncodesAt fuel hostType completion.value payload ∧
    CompatiblePayload.ValueRep compiled.compatible.checked state.receiving.result.context.registry
      (functions rows initial profile) state.mapping state.world sourceType source payload nativeType

def ForwardAt (rows : Inventory inputs)
    (anchor : Header compiled (Program.ofChecked compiled.sourceProgram))
    (initial : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed)
    (profile : compiled.compatible.checked.catalog.callableContracts = true)
    (recipe : SourceCoreIndexedSession.Recipe)
    {artifact : SourceCoreExecution.Artifact} (entries : List Entry)
    (result : TypeSystem.Ty) (checkpoint : SourceCoreExecution.Checkpoint artifact)
    (source : Dynamic.Value) (after : Dynamic.Heap) : Prop :=
  ∃ requiredExecution requiredOutput,
    ∀ executionFuel outputFuel (outcome : SourceCoreExecution.Outcome artifact),
      requiredExecution ≤ executionFuel → requiredOutput ≤ outputFuel →
      checkpoint.ResumeAt executionFuel outputFuel outcome →
      ∃ completion : SourceCoreExecution.Completion artifact,
        outcome = .succeeded completion ∧ completion.session.ExportsReady ∧
        ∃ returned : State rows anchor initial profile recipe completion.session entries,
          returned.heap = after ∧ ReturnedValue completion returned result source outputFuel ∧
        ∀ selection : Selection result completion.value,
          ∃ (added : List Entry) (next : State rows anchor initial profile recipe completion.session (entries ++ added)),
            next.heap = after ∧ added.map Entry.handle = selection.handles ∧
            SelectedAt compiled.compatible.checked completion selection source outputFuel added

/-- Only an accepted original start and independent Source success are inputs.
The shared static program package closes every callable body internally. -/
theorem forward_call
    (support : SelectedCompilationPhysicalProgramSupport.Support
      compiled (headers rows) (keys compiled) initial)
    (prepared : SourceCoreIndexedSession.Recipe.prepare compiled = .ok recipe)
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    {entries : List Entry}
    (state : State rows anchor initial profile recipe session entries)
    (entry : Entry) (member : entry ∈ entries)
    {parameter result : TypeSystem.Ty}
    (entryType : entry.sourceType = .function parameter result)
    {argument : SourceCorePublicValues.Value} {packedSource : Dynamic.Value}
    (input : RecursiveNamedPublicFunctionHistoryInputs.Input entries anchor.function.context
      parameter argument packedSource)
    {inputFuel : Nat} {publicCheckpoint : SourceCoreExecution.Checkpoint artifact}
    (accepted : session.startHandlePacked entry.handle argument inputFuel = .ok publicCheckpoint)
    (exportsReady : session.ExportsReady)
    {invocation : Staging.Recursive.Scope} {sources : List Dynamic.Value}
    (packing : Dynamic.ValuesPack sources packedSource)
    {sourceSize : Nat} {source : Dynamic.Value} {after : Dynamic.Heap}
    (trace : Staging.Recursive.Size.Applies (Program.ofChecked compiled.sourceProgram)
      (SelectedCompilationPhysicalProgramSupport.stages compiled) sourceSize
      invocation anchor.function.context state.heap entry.source sources (.value source) after) :
    ForwardAt rows anchor initial profile recipe entries result publicCheckpoint source after := by
  have sameCompiled := SourceCoreIndexedSession.Recipe.prepare_compiled prepared
  cases sameCompiled
  obtain ⟨checkpoint, atCheckpoint, original⟩ :=
    RecursiveNamedPublicDirectHandleMeaning.recover_handle_start state.atSession accepted
  have imported := (state.history.semantic.current.2.2.2.2 entry member).1
  rw [entryType] at imported
  obtain ⟨actualParameter, actualResult, nativeParameter, nativeResult, callable, packed, encodedValues,
      started, _parameterView, _resultView⟩ :=
    RecursiveNamedPublicDirectPackedInputMeaning.actual_start_compatible state.atRecipe
      state.history.semantic.current.1 imported original
  obtain ⟨parameterView, resultView⟩ := TypeSystem.Ty.function.inj
    (started.selected.spec.2.1.symm.trans imported.function_type.symm)
  obtain ⟨receiving, _indexed, contextAt, issued, extended, retained, _represented, _typed, _diagnostics⟩ :=
    RecursiveNamedPublicActualRegistryStart.packed_input state.history.semantic state.registry
      member entryType input started
  have metadata : SourceCoreRawMetadata.Extends encodedValues.registry receiving.result.context.registry := by
    rw [contextAt]
    exact .refl _
  have outputMetadata : SourceCoreRawMetadata.Extends receiving.result.context.registry encodedValues.registry := by
    rw [contextAt]
    exact .refl _
  obtain ⟨value, finalStore, finalMap, finalWorld, requiredExecution, enough, resultAt⟩ :=
    SelectedCompilationPublicDirectCallableHistory.has_sufficient_fuel
      (completion := receiving) support issued (state.extension.trans extended)
      retained state.history.physical entry member entryType input
      started parameterView.symm metadata packing trace
  obtain ⟨payload, rfl⟩ : ∃ payload, value = .inRight .word payload := by
    have represented := resultAt.1
    cases represented with
    | value related => exact ⟨_, rfl⟩
  have represented : CompatiblePayload.ValueRep recipe.compiled.compatible.checked
      receiving.result.context.registry (functions rows initial profile) finalMap finalWorld
      result source payload nativeResult := by
    have represented := resultAt.1
    cases represented with
    | value related => exact related
  have shape : SourceCorePublicOutputShapes.Output recipe.compiled.compatible.checked encodedValues.registry
      (finalStore.map Core.Value.type) recipe.program.layouts.definitions actualResult payload := by
    have shaped := CompatiblePublicOutputShapes.ValueRep.output represented
    rw [contextAt] at shaped
    rw [resultAt.2.1.runtime_hasTypes.world_eq] at shaped
    exact .compatible resultView shaped
  have checkpointRegistry : checkpoint.RegistryAt encodedValues.registry := by
    have values := started.values
    cases checkpoint
    change _ = encodedValues at values
    exact congrArg SourceCoreCompatibleValues.Context.registry values
  have ready := started.original.initial_registry.exportsReady (state.atSession.exportsReady_iff.mp exportsReady)
  obtain ⟨requiredOutput, exports⟩ := publicCheckpoint.output_succeeded_uniform
    atCheckpoint started.recipe_eq checkpointRegistry ready started.requested shape
  refine ⟨requiredExecution, requiredOutput, ?_⟩
  intro executionFuel outputFuel outcome executionBound outputBound resumed
  obtain ⟨completion, actual, generation, success, exported, atCompletion, returnedReady⟩ :=
    exports executionFuel (enough executionFuel executionBound) outputFuel outputBound outcome resumed
  obtain ⟨returnedCaller, _returnedRelated, returnedHistory⟩ :=
    retained.after_packed_success started.original exported resultAt
  have returnedRegistry := started.returned_registry exported
  let returned : State rows anchor initial profile recipe completion.session entries := {
    artifact := state.artifact
    session := actual.session
    mapping := finalMap
    world := finalWorld
    heap := after
    store := finalStore
    caller := returnedCaller
    atSession := atCompletion.2.2.2
    atRecipe := state.atRecipe
    receiving := receiving
    issued := issued
    extension := state.extension.trans extended
    registry := (congrArg (·.registry) contextAt).symm ▸ returnedRegistry
    history := ⟨returnedHistory, state.history.physical.extend resultAt.2.2.2.2.1⟩ }
  have encoded := (exported.reimports_payload started.requested rfl).2
  rw [← atCompletion.1] at encoded
  refine ⟨completion, success, atCompletion.2.2.2.exportsReady_iff.mpr returnedReady,
    returned, rfl, ⟨actualResult, payload, nativeResult, resultView, encoded, represented⟩, ?_⟩
  intro selection
  have returnedRegistry := started.returned_registry exported
  obtain ⟨reached, actualSource, native, added, sourceValue, nativeValue, selected, handles, _related, history⟩ :=
    retained.collect_packed_nested_success rfl state.atRecipe started.original started.requested resultView.symm
      exported resultAt returnedRegistry outputMetadata (atCompletion.1 ▸ selection)
  have sourceEq := Staging.Recursive.Outcome.value.inj sourceValue
  have nativeEq : payload = native := (Core.Value.inRight.inj nativeValue).2
  cases sourceEq
  cases nativeEq
  have originalSelected := selected_of_cast atCompletion.1 selected
  have originalHandles := handles.trans (Selection.handles_cast atCompletion.1 selection)
  let next : State rows anchor initial profile recipe completion.session (entries ++ added) := {
    artifact := state.artifact
    session := actual.session
    mapping := finalMap
    world := finalWorld
    heap := after
    store := finalStore
    caller := reached
    atSession := atCompletion.2.2.2
    atRecipe := state.atRecipe
    receiving := receiving
    issued := issued
    extension := state.extension.trans extended
    registry := (congrArg (·.registry) contextAt).symm ▸ returnedRegistry
    history := ⟨history, state.history.physical.extend resultAt.2.2.2.2.1⟩ }
  exact ⟨added, next, rfl, originalHandles, state.artifact, actual, payload, nativeResult,
    atCompletion, originalSelected⟩

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageClosedDirectForward.Output

namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageClosedDirectForward
open Core Frontend SourceInference
open CallableIndexedOwnedFunctionValues (Header)
open RecursiveNamedPublicFunctionHistory (Entry)
open SelectedCompilationCertifiedPublicSession (Profiled)
open RecursiveNamedPublicScalarResults (ScalarOutput)

variable {recipe : SourceCoreIndexedSession.Recipe} (issued : Profiled recipe)
  {anchor : Header recipe.compiled (Program.ofChecked recipe.compiled.sourceProgram)}
  {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
  {entries : List Entry}

/-- A real body guard rejects at its actual heap, retaining every prior handle. -/
def StageStopped (state : issued.toIssued.State anchor session entries) (entry : Entry)
    (checkpoint : SourceCoreExecution.Checkpoint artifact)
    (invocation : Staging.Recursive.Scope) (sources : List Dynamic.Value) : Prop :=
  ∃ origin occurrence reason reached,
    Staging.Recursive.Generated origin occurrence reason ∧
    Staging.Recursive.Applies (Program.ofChecked recipe.compiled.sourceProgram)
      (SelectedCompilationPhysicalProgramSupport.stages recipe.compiled) invocation
      anchor.function.context state.heap entry.source sources (.fault (.stage origin occurrence reason)) reached ∧
    SelectedCompilationPublicSessionDirectFailureForward.FailureForwardAt
      issued.catalog.rows anchor issued.initial issued.support.profile recipe entries
      (.stage origin occurrence reason) checkpoint reached

variable (state : issued.toIssued.State anchor session entries)
  (entry : Entry) (member : entry ∈ entries)
  {parameter result : TypeSystem.Ty}
  (entryType : entry.sourceType = .function parameter result)
  {argument : SourceCorePublicValues.Value} {packedSource : Dynamic.Value}
  (input : RecursiveNamedPublicFunctionHistoryInputs.Input entries anchor.function.context
    parameter argument packedSource)
  {inputFuel : Nat} {checkpoint : SourceCoreExecution.Checkpoint artifact}
  (accepted : session.startHandlePacked entry.handle argument inputFuel = .ok checkpoint)
  (ready : session.ExportsReady)
  {invocation : Staging.Recursive.Scope} {sources : List Dynamic.Value}
  (packing : Dynamic.ValuesPack sources packedSource)
  {after : Dynamic.Heap}

include member entryType input accepted ready packing in
/-- An independent ordinary scalar call preserves its result and complete
history, unless an authentic nested stage check rejects first. -/
theorem scalar (scalar : ScalarOutput)
    (resultEq : result = scalar.sourceType)
    {hostParameter : TypeSystem.Ty}
    (handleType : entry.handle.sourceType = .function hostParameter scalar.sourceType)
    (trace : Dynamic.CallableApplies (Program.ofChecked recipe.compiled.sourceProgram)
      anchor.function.context invocation.evidence (Staging.Recursive.callableEvidence entry.source)
      state.heap entry.source sources scalar.source after) :
    (Staging.Recursive.Applies (Program.ofChecked recipe.compiled.sourceProgram)
        (SelectedCompilationPhysicalProgramSupport.stages recipe.compiled) invocation
        anchor.function.context state.heap entry.source sources (.value scalar.source) after ∧
      SelectedCompilationPublicSessionDirectScalarForward.ForwardAt
        issued.catalog.rows anchor issued.initial issued.support.profile recipe entries scalar checkpoint after) ∨
    StageStopped issued state entry checkpoint invocation sources := by
  have arity := SelectedCompilationStagePublicDirectInputLifting.arity_of_value trace
  obtain ⟨staged, reached, lifted, adapted⟩ := SelectedCompilationStagePublicDirectInputLifting.lift_call
    issued state entry member entryType input accepted packing arity (.value trace)
  cases adapted with
  | completed =>
    obtain ⟨size, measured⟩ := Staging.Recursive.Size.Applies.of_trace lifted
    exact .inl ⟨lifted, SelectedCompilationPublicSessionDirectScalarForward.forward_call
      issued.support issued.prepared state entry member scalar (resultEq ▸ entryType) handleType
      input accepted ready packing measured⟩
  | rejected origin occurrence reason reached =>
    obtain ⟨size, measured⟩ := Staging.Recursive.Size.Applies.of_trace lifted
    exact .inr ⟨origin, occurrence, reason, reached, lifted.stage_origin rfl, lifted,
      issued.forward_direct_failure state entry member entryType input accepted ready packing arity measured⟩

include member entryType input accepted ready packing in
/-- A genuine arity keeps the ordinary packed fault at the same heap and
preserves all prior entries, with a separate earlier-stage alternative. -/
theorem fault
    (arity : RecursivePublicCallableArity.Arity (Program.ofChecked recipe.compiled.sourceProgram)
      entry.source sources.length)
    (reason : Dynamic.SemanticFault)
    (trace : Dynamic.CallableFaults (Program.ofChecked recipe.compiled.sourceProgram)
      anchor.function.context invocation.evidence (Staging.Recursive.callableEvidence entry.source)
      state.heap entry.source sources reason after) :
    (Staging.Recursive.Applies (Program.ofChecked recipe.compiled.sourceProgram)
        (SelectedCompilationPhysicalProgramSupport.stages recipe.compiled) invocation
        anchor.function.context state.heap entry.source sources (.fault (.semantic reason)) after ∧
      SelectedCompilationPublicSessionDirectFailureForward.FailureForwardAt
        issued.catalog.rows anchor issued.initial issued.support.profile recipe entries
        (.semantic reason) checkpoint after) ∨
    StageStopped issued state entry checkpoint invocation sources := by
  obtain ⟨staged, reached, lifted, adapted⟩ := SelectedCompilationStagePublicDirectInputLifting.lift_call
    issued state entry member entryType input accepted packing arity (.fault trace)
  cases adapted with
  | completed =>
    obtain ⟨size, measured⟩ := Staging.Recursive.Size.Applies.of_trace lifted
    exact .inl ⟨lifted,
      issued.forward_direct_failure state entry member entryType input accepted ready packing arity measured⟩
  | rejected origin occurrence reason reached =>
    obtain ⟨size, measured⟩ := Staging.Recursive.Size.Applies.of_trace lifted
    exact .inr ⟨origin, occurrence, reason, reached, lifted.stage_origin rfl, lifted,
      issued.forward_direct_failure state entry member entryType input accepted ready packing arity measured⟩

include member entryType input accepted ready packing in
/-- General public output retains the whole Source value and its real reimport,
plus any ordered nested callable selection, or an authentic earlier stage stop. -/
theorem output {source : Dynamic.Value}
    (trace : Dynamic.CallableApplies (Program.ofChecked recipe.compiled.sourceProgram)
      anchor.function.context invocation.evidence (Staging.Recursive.callableEvidence entry.source)
      state.heap entry.source sources source after) :
    (Staging.Recursive.Applies (Program.ofChecked recipe.compiled.sourceProgram)
        (SelectedCompilationPhysicalProgramSupport.stages recipe.compiled) invocation
        anchor.function.context state.heap entry.source sources (.value source) after ∧
      Output.ForwardAt issued.catalog.rows anchor issued.initial issued.support.profile recipe
        entries result checkpoint source after) ∨
    StageStopped issued state entry checkpoint invocation sources := by
  have arity := SelectedCompilationStagePublicDirectInputLifting.arity_of_value trace
  obtain ⟨staged, reached, lifted, adapted⟩ := SelectedCompilationStagePublicDirectInputLifting.lift_call
    issued state entry member entryType input accepted packing arity (.value trace)
  cases adapted with
  | completed =>
    obtain ⟨size, measured⟩ := Staging.Recursive.Size.Applies.of_trace lifted
    exact .inl ⟨lifted, Output.forward_call issued.support issued.prepared state entry member
      entryType input accepted ready packing measured⟩
  | rejected origin occurrence reason reached =>
    obtain ⟨size, measured⟩ := Staging.Recursive.Size.Applies.of_trace lifted
    exact .inr ⟨origin, occurrence, reason, reached, lifted.stage_origin rfl, lifted,
      issued.forward_direct_failure state entry member entryType input accepted ready packing arity measured⟩

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageClosedDirectForward
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageClosedInitialForward
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageClosedInitialForward
open Core Frontend SourceInference
open SelectedCompilationPublicSessionState
open SelectedCompilationCertifiedPublicSession (Profiled Initial)
open SelectedCompilationStagePublicInputLifting
open RecursiveNamedPublicScalarResults (ScalarOutput)

variable {recipe : SourceCoreIndexedSession.Recipe} (issued : Profiled recipe)
  {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
  {key : SourceCoreIndexedSession.Key} {publicArguments : List SourceCorePublicValues.Value}
  {options : SourceCoreExecution.RunOptions}

/-- An authentic early stage rejection keeps its reached heap and the public
failure continuation from the actual initial bootstrap. -/
def StageStopped (call : StartedCall session key publicArguments options)
    (initial : Initial issued.toIssued call)
    (invocation : Staging.Recursive.Scope) (arguments : List Dynamic.Value) : Prop :=
  ∃ origin occurrence reason reached,
    Staging.Recursive.Generated origin occurrence reason ∧
    SourceCall initial.header initial.header invocation ⟨[]⟩ arguments
      (.fault (.stage origin occurrence reason)) reached ∧
    SelectedCompilationPublicSessionFailureForward.FailureForwardAt (entries := [])
      issued.catalog.rows initial.header issued.initial issued.support.profile recipe
      (.stage origin occurrence reason) call reached

variable (call : StartedCall session key publicArguments options)
  (initial : Initial issued.toIssued call)
  (simple : ∀ value ∈ publicArguments, SourceCoreIndexedSession.SimplePublic value)
  (inputTypes : RecursiveNamedPublicDataArgumentReceipts.PublicDataTypes
    initial.header.function.context publicArguments initial.header.types)
  {arguments : List Dynamic.Value}
  (inputMeanings : RecursiveNamedPublicDataInputs.Meanings publicArguments arguments)
  {invocation : Staging.Recursive.Scope} {after : Dynamic.Heap}

include simple inputTypes inputMeanings in
/-- The selected physical support supplies every internal body lifting proof. -/
theorem lift_call {plain : Dynamic.ExpressionOutcome}
    (trace : PlainCall initial.header initial.header invocation ⟨[]⟩ arguments plain after) :
    ∃ staged reached,
      SourceCall initial.header initial.header invocation ⟨[]⟩ arguments staged reached ∧
      Staging.Recursive.Lifting.Adapted plain after staged reached :=
  SelectedCompilationStageInitialInputLifting.lift_call
    issued.catalog.rows issued.prepared initial.header initial.header issued.support
    (SelectedCompilationStagePublicProgramLifting.named_bodies issued.support)
    issued.catalog.distinct call initial.start simple inputTypes inputMeanings trace

include simple inputTypes inputMeanings in
/-- An ordinary initial scalar result gives the same public result and heap,
with a separate alternative for a genuine earlier stage rejection. -/
theorem scalar (scalar : ScalarOutput)
    (rawType : initial.header.function.resultType = scalar.sourceType)
    (nativeType : initial.header.output = scalar.nativeType)
    (trace : PlainValue initial.header initial.header invocation ⟨[]⟩ arguments scalar.source after) :
    (SourceCall initial.header initial.header invocation ⟨[]⟩ arguments (.value scalar.source) after ∧
      SelectedCompilationPublicSessionScalarForward.ForwardAt (entries := [])
        issued.catalog.rows initial.header issued.initial issued.support.profile recipe scalar call after) ∨
    StageStopped issued call initial invocation arguments := by
  obtain ⟨staged, reached, lifted, adapted⟩ :=
    lift_call issued call initial simple inputTypes inputMeanings (plain_value trace)
  cases adapted with
  | completed =>
    exact .inl ⟨lifted, SelectedCompilationPublicSessionInitialScalarForward.first_scalar
      issued.catalog.rows issued.prepared initial.header initial.header issued.support
      issued.catalog.distinct scalar call initial.start simple inputTypes inputMeanings rawType nativeType lifted⟩
  | rejected origin occurrence reason reached =>
    exact .inr ⟨origin, occurrence, reason, reached, lifted.failure_plain, lifted,
      Profiled.forward_initial_failure initial simple inputTypes inputMeanings lifted⟩

include simple inputTypes inputMeanings in
/-- An ordinary initial semantic fault retains its diagnostic and heap, unless
an actual stage check rejects before that fault is reached. -/
theorem fault (reason : Dynamic.SemanticFault)
    (trace : PlainFault initial.header initial.header invocation ⟨[]⟩ arguments reason after) :
    (SourceCall initial.header initial.header invocation ⟨[]⟩ arguments (.fault (.semantic reason)) after ∧
      SelectedCompilationPublicSessionFailureForward.FailureForwardAt (entries := [])
        issued.catalog.rows initial.header issued.initial issued.support.profile recipe (.semantic reason) call after) ∨
    StageStopped issued call initial invocation arguments := by
  obtain ⟨staged, reached, lifted, adapted⟩ :=
    lift_call issued call initial simple inputTypes inputMeanings (plain_fault trace)
  cases adapted with
  | completed =>
    exact .inl ⟨lifted, Profiled.forward_initial_failure initial simple inputTypes inputMeanings lifted⟩
  | rejected origin occurrence reason reached =>
    exact .inr ⟨origin, occurrence, reason, reached, lifted.failure_plain, lifted,
      Profiled.forward_initial_failure initial simple inputTypes inputMeanings lifted⟩

include simple inputTypes inputMeanings in
/-- An ordinary initial function result can be exported as a retained handle
with the same Source value and heap, or stop at a genuine earlier stage check. -/
theorem function {parameter resultType : TypeSystem.Ty} {value : Dynamic.Value}
    (functionResult : SourceCoreRawMetadata.runtimeType initial.header.function.resultType =
      .function parameter resultType)
    (trace : PlainValue initial.header initial.header invocation ⟨[]⟩ arguments value after) :
    (SourceCall initial.header initial.header invocation ⟨[]⟩ arguments (.value value) after ∧
      SelectedCompilationPublicSessionInitialForward.ForwardAt issued.catalog.rows
        initial.header initial.header issued.support call value after) ∨
    StageStopped issued call initial invocation arguments := by
  obtain ⟨staged, reached, lifted, adapted⟩ :=
    lift_call issued call initial simple inputTypes inputMeanings (plain_value trace)
  cases adapted with
  | completed =>
    exact .inl ⟨lifted, initial.forward_function simple inputTypes inputMeanings functionResult lifted⟩
  | rejected origin occurrence reason reached =>
    exact .inr ⟨origin, occurrence, reason, reached, lifted.failure_plain, lifted,
      Profiled.forward_initial_failure initial simple inputTypes inputMeanings lifted⟩

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageClosedInitialForward
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageNamedOutputForward
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageNamedOutputForward
open Core Frontend SourceInference
open SelectedCompilationStageClosedDirectForward.Output (ForwardAt)
open RecursiveNamedPublicNestedOutputSelections (Selection)
open RecursiveNamedPublicFunctionHistory (Entry)
open SelectedCompilationPublicSessionDirectOutputCollection (selected_of_cast)
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
theorem forward_at_input_registry (support : SelectedCompilationPhysicalProgramSupport.Support compiled (headers rows) (keys compiled) initial)
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
    {invocation : Staging.Recursive.Scope} {after : Dynamic.Heap} {source : Dynamic.Value}
    (trace : SourceCall anchor request.header invocation state.heap arguments (.value source) after) :
    ForwardAt rows anchor initial profile recipe entries request.header.function.resultType call.checkpoint source after := by
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
  have encoded := (exported.reimports_payload requested rfl).2
  rw [← actualAt.1] at encoded
  refine ⟨completion, succeeded, actualAt.2.2.2.exportsReady_iff.mpr returnedReady,
    returned, rfl, ⟨request.header.function.resultType, payload, request.header.output,
      rfl, encoded, representedResult⟩, ?_⟩
  intro selection
  obtain ⟨encodedValue, encodedAt, payloadAt⟩ := (exported.reimports_payload requested rfl).2
  have actualRegistry := request.started.returned_registry exported
  have outputMetadata : SourceCoreRawMetadata.Extends receiving.result.context.registry request.encodedValues.registry := by
    rw [registry]
    exact .refl _
  have prior := actualRegistry.symm ▸ outputMetadata
  obtain ⟨added, selected, handles⟩ := (actualAt.1 ▸ selection : Selection request.header.function.resultType actual.value).collect
    state.atRecipe rfl representedResult encodedAt rfl payloadAt prior
  obtain ⟨reached, related, post⟩ := result.2.2.2.2.2.2.2
  have collected := RecursiveNamedPublicFunctionHistory.History.next history.semantic rfl
    request.started request.selected exported result reached ⟨related, post⟩
    (.selectNestedCompatible requested rfl rfl rfl _ selected)
  let next : State rows anchor initial profile recipe completion.session (entries ++ added) := {
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
    history := history.after_result result collected }
  exact ⟨added, next, rfl, handles.trans (Selection.handles_cast actualAt.1 selection),
    state.artifact, actual, payload, request.header.output, actualAt, selected_of_cast actualAt.1 selected⟩

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageNamedOutputForward
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageInitialDataOutputForward
/-! Initial Source success preserves the whole exported value and any selected
nested callable leaves at the exact reached heap. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageInitialDataOutputForward
open Core Frontend SourceInference
open SelectedCompilationStageClosedDirectForward.Output (ForwardAt)
open RecursiveNamedPublicNestedOutputSelections (Selection)
open RecursiveNamedPublicFunctionHistory (Entry)
open SelectedCompilationPublicSessionDirectOutputCollection (selected_of_cast)
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

theorem first_output
    (distinct : (inputs.map (fun input => input.prepared.index)).Nodup)
    (call : StartedCall session key publicArguments options)
    (start : Started rows prepared header call)
    (inputTypes : RecursiveNamedPublicDataArgumentReceipts.PublicDataTypes
      header.function.context publicArguments header.types)
    {arguments : List Dynamic.Value}
    (inputMeanings : RecursiveNamedPublicDataInputs.Meanings publicArguments arguments)
    {invocation : Staging.Recursive.Scope} {after : Dynamic.Heap} {source : Dynamic.Value}
    (trace : SourceCall anchor header invocation ⟨[]⟩ arguments (.value source) after) :
    ForwardAt rows anchor initial support.profile
      recipe [] header.function.resultType call.checkpoint source after := by
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
  refine ⟨requiredExecution, requiredOutput, ?_⟩
  intro executionFuel outputFuel outcome executionBound outputBound resumed
  obtain ⟨completion, actual, generation, succeeded, exported, actualAt, returnedReady⟩ :=
    exports executionFuel (completes executionFuel executionBound) outputFuel outputBound outcome resumed
  obtain ⟨reached, related, post⟩ := result.2.2.2.2.2.2.2
  have retained := RecursiveNamedPublicFunctionHistory.History.first rfl start.started start.selected exported result
    reached ⟨related, post⟩ .skip
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
  have encoded := (exported.reimports_payload requested rfl).2
  rw [← actualAt.1] at encoded
  refine ⟨completion, succeeded, actualAt.2.2.2.exportsReady_iff.mpr returnedReady,
    returned, rfl, ⟨header.function.resultType, payload, header.output, rfl, encoded, representedResult⟩, ?_⟩
  intro selection
  obtain ⟨encodedValue, encodedAt, payloadAt⟩ := (exported.reimports_payload requested rfl).2
  have actualRegistry := start.started.returned_registry exported
  have outputMetadata : SourceCoreRawMetadata.Extends receiving.result.context.registry start.encodedValues.registry := by
    rw [receiverRegistry]
    exact .refl _
  have prior := actualRegistry.symm ▸ outputMetadata
  obtain ⟨added, selected, handles⟩ := (actualAt.1 ▸ selection : Selection header.function.resultType actual.value).collect
    start.started.recipe_eq rfl representedResult encodedAt rfl payloadAt prior
  have collected := RecursiveNamedPublicFunctionHistory.History.first rfl start.started start.selected exported result
    reached ⟨related, post⟩ (.selectNestedCompatible requested rfl rfl rfl _ selected)
  let next : State rows anchor initial support.profile recipe completion.session ([] ++ added) := {
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
    history := ⟨collected, physicalRetained⟩ }
  exact ⟨added, next, rfl, handles.trans (Selection.handles_cast actualAt.1 selection),
    start.artifact, actual, payload, header.output, actualAt, selected_of_cast actualAt.1 selected⟩

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageInitialDataOutputForward
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageInitialOutputForward
/-! Initial Source success preserves the whole exported value and any selected
nested callable leaves at the exact reached heap. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageInitialOutputForward
open Core Frontend SourceInference
open SelectedCompilationStageClosedDirectForward.Output (ForwardAt)
open RecursiveNamedPublicNestedOutputSelections (Selection)
open RecursiveNamedPublicFunctionHistory (Entry)
open SelectedCompilationPublicSessionDirectOutputCollection (selected_of_cast)
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

theorem first_output
    (distinct : (inputs.map (fun input => input.prepared.index)).Nodup)
    (call : StartedCall session key publicArguments options)
    (start : Started rows prepared header call)
    (simple : ∀ value ∈ publicArguments, SourceCoreIndexedSession.SimplePublic value)
    (inputTypes : RecursiveNamedPublicDataArgumentReceipts.PublicDataTypes
      header.function.context publicArguments header.types)
    {arguments : List Dynamic.Value}
    (inputMeanings : RecursiveNamedPublicDataInputs.Meanings publicArguments arguments)
    {invocation : Staging.Recursive.Scope} {after : Dynamic.Heap} {source : Dynamic.Value}
    (trace : SourceCall anchor header invocation ⟨[]⟩ arguments (.value source) after) :
    ForwardAt rows anchor initial support.profile
      recipe [] header.function.resultType call.checkpoint source after := by
  have _ := simple
  exact SelectedCompilationStageInitialDataOutputForward.first_output
    rows prepared anchor header support distinct call start inputTypes inputMeanings trace

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageInitialOutputForward
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageClosedOutputForward
/-! Ordinary Source success determines the complete public value, including
its original metadata and any selected callable leaves retained for later use. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageClosedOutputForward
open Core Frontend SourceInference
open CallableIndexedOwnedPreparedFiniteNamedInventories (headers)
open CallableIndexedOwnedFunctionValues (Header)
open SelectedCompilationPublicSessionState
open SelectedCompilationCertifiedPublicSession (Profiled Initial)
open SelectedCompilationStagePublicInputLifting
open SelectedCompilationStageClosedDirectForward.Output (ForwardAt)

variable {recipe : SourceCoreIndexedSession.Recipe} (issued : Profiled recipe)
  {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
  {key : SourceCoreIndexedSession.Key} {publicArguments : List SourceCorePublicValues.Value}
  {options : SourceCoreExecution.RunOptions}

/-- Initial data inputs and an ordinary Source result suffice for full output
reimport and ordered retention of nested callables, or genuine stage failure. -/
theorem initial (call : StartedCall session key publicArguments options)
    (start : Initial issued.toIssued call)
    (simple : ∀ value ∈ publicArguments, SourceCoreIndexedSession.SimplePublic value)
    (inputTypes : RecursiveNamedPublicDataArgumentReceipts.PublicDataTypes
      start.header.function.context publicArguments start.header.types)
    {arguments : List Dynamic.Value}
    (inputMeanings : RecursiveNamedPublicDataInputs.Meanings publicArguments arguments)
    {invocation : Staging.Recursive.Scope} {after : Dynamic.Heap} {value : Dynamic.Value}
    (trace : PlainValue start.header start.header invocation ⟨[]⟩ arguments value after) :
    (SourceCall start.header start.header invocation ⟨[]⟩ arguments (.value value) after ∧
      ForwardAt issued.catalog.rows start.header issued.initial issued.support.profile recipe []
        start.header.function.resultType call.checkpoint value after) ∨
    SelectedCompilationStageClosedInitialForward.StageStopped issued call start invocation arguments := by
  obtain ⟨staged, reached, lifted, adapted⟩ :=
    SelectedCompilationStageClosedInitialForward.lift_call issued call start simple inputTypes
      inputMeanings (plain_value trace)
  cases adapted with
  | completed =>
    exact .inl ⟨lifted, SelectedCompilationStageInitialOutputForward.first_output
      issued.catalog.rows issued.prepared start.header start.header issued.support
      issued.catalog.distinct call start.start simple inputTypes inputMeanings lifted⟩
  | rejected origin occurrence reason reached =>
    exact .inr ⟨origin, occurrence, reason, reached, lifted.failure_plain, lifted,
      Profiled.forward_initial_failure start simple inputTypes inputMeanings lifted⟩

/-- A later named call preserves the whole result and earlier handle history;
selected nested handles can join that same returned physical state. -/
theorem later
    {anchor : Header recipe.compiled (Program.ofChecked recipe.compiled.sourceProgram)}
    {entries : List RecursiveNamedPublicFunctionHistory.Entry}
    (state : issued.toIssued.State anchor session entries)
    (call : StartedCall session key publicArguments options)
    (request : RecursiveNamedPublicHistoryFrontdoor.Started (headers issued.catalog.rows) issued.prepared
      call.checkpoint state.session key publicArguments options.inputValidationFuel state.world state.store)
    {arguments : List Dynamic.Value}
    (inputs : RecursiveNamedPublicFunctionHistoryInputs.Inputs entries request.header.function.context
      (request.header.bindings.map (fun binding => binding.1.scheme.body)) publicArguments arguments)
    (ready : session.ExportsReady)
    {invocation : Staging.Recursive.Scope} {after : Dynamic.Heap} {value : Dynamic.Value}
    (trace : PlainValue anchor request.header invocation state.heap arguments value after) :
    (SourceCall anchor request.header invocation state.heap arguments (.value value) after ∧
      ForwardAt issued.catalog.rows anchor issued.initial issued.support.profile recipe entries
        request.header.function.resultType call.checkpoint value after) ∨
    SelectedCompilationStagePublicForward.StageStopped issued state call request.header invocation arguments := by
  obtain ⟨staged, reached, lifted, adapted⟩ := lift_call_at_input_registry issued.support
    (SelectedCompilationStagePublicProgramLifting.named_bodies issued.support)
    issued.prepared state call request inputs (plain_value trace)
  cases adapted with
  | completed =>
    exact .inl ⟨lifted, SelectedCompilationStageNamedOutputForward.forward_at_input_registry
      issued.support issued.prepared state call request inputs ready lifted⟩
  | rejected origin occurrence reason reached =>
    exact .inr ⟨origin, occurrence, reason, reached, lifted.failure_plain, lifted,
      SelectedCompilationPublicSessionFailureForward.forward_call_at_input_registry
        issued.support issued.registryBodies issued.prepared state call request inputs ready lifted⟩

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageClosedOutputForward
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicDirectOutputReflection
/-! Actual packed callable execution retains the complete physical cache and
all previous exports. The input encoder supplies the reached registry, and the
shared static package closes every body meaning used by reflection. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicDirectOutputReflection
open Core Frontend SourceInference
open CallableIndexedOwnedPreparedFiniteNamedInventories (Input Inventory headers)
open CallableIndexedOwnedPreparedBootstrapRootState (keys)
open CallableIndexedOwnedFunctionValues (Header)
open RecursiveNamedPublicFunctionHistory (Entry)
open SelectedCompilationPublicSessionState
open SelectedCompilationStageClosedDirectForward.Output (ReturnedValue)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {inputs : List (Input compiled)} {rows : Inventory inputs}
  {anchor : Header compiled (Program.ofChecked compiled.sourceProgram)}
  {initial : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
  {profile : compiled.compatible.checked.catalog.callableContracts = true}
  {recipe : SourceCoreIndexedSession.Recipe}

/-- Every actual direct completion has an ordinary Source result represented
by the complete public value, with prior captures and heap correspondence. -/
theorem State.reflect_output
    (support : SelectedCompilationPhysicalProgramSupport.Support
      compiled (headers rows) (keys compiled) initial)
    (prepared : SourceCoreIndexedSession.Recipe.prepare compiled = .ok recipe)
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    {entries : List Entry}
    (state : State rows anchor initial profile recipe session entries)
    (entry : Entry) (member : entry ∈ entries)
    {parameter result : TypeSystem.Ty}
    (entryType : entry.sourceType = .function parameter result)
    {argument : SourceCorePublicValues.Value} {packedSource : Dynamic.Value}
    (input : RecursiveNamedPublicFunctionHistoryInputs.Input entries anchor.function.context
      parameter argument packedSource)
    {options : SourceCoreExecution.RunOptions}
    {completion : SourceCoreExecution.Completion artifact}
    (invoked : session.InvokeAt entry.handle argument options (.ok (.succeeded completion)))
    (invocation : Staging.Recursive.Scope) :
    ∃ sources, Dynamic.ValuesPack sources packedSource ∧
      RecursivePublicCallableArity.Arity (Program.ofChecked compiled.sourceProgram) entry.source sources.length ∧
      ∃ source, ∃ next : State rows anchor initial profile recipe completion.session entries,
      ∃ size, Staging.Recursive.Size.Applies (Program.ofChecked compiled.sourceProgram)
        (SelectedCompilationPhysicalProgramSupport.stages compiled) size
        invocation anchor.function.context state.heap entry.source sources (.value source) next.heap ∧
      Dynamic.CallableApplies (Program.ofChecked compiled.sourceProgram) anchor.function.context
        invocation.evidence (Staging.Recursive.callableEvidence entry.source) state.heap entry.source sources source next.heap ∧
      ReturnedValue completion next result source options.outputValidationFuel := by
  have sameCompiled := SourceCoreIndexedSession.Recipe.prepare_compiled prepared
  cases sameCompiled
  obtain ⟨publicCheckpoint, accepted, resumed⟩ := invoked
  obtain ⟨checkpoint, atCheckpoint, original⟩ :=
    RecursiveNamedPublicDirectHandleMeaning.recover_handle_start state.atSession accepted
  have imported := (state.history.semantic.current.2.2.2.2 entry member).1
  rw [entryType] at imported
  obtain ⟨actualParameter, actualResult, nativeParameter, nativeResult, callable, packed, encodedValues,
      started, _parameterView, _resultView⟩ :=
    RecursiveNamedPublicDirectPackedInputMeaning.actual_start_compatible state.atRecipe
      state.history.semantic.current.1 imported original
  obtain ⟨receiving, _indexed, contextAt, issued, extended, retained, _represented, _typed, _diagnostics⟩ :=
    RecursiveNamedPublicActualRegistryStart.packed_input state.history.semantic state.registry
      member entryType input started
  have metadata : SourceCoreRawMetadata.Extends encodedValues.registry receiving.result.context.registry := by
    rw [contextAt]
    exact .refl _
  obtain ⟨parameterView, resultView⟩ := TypeSystem.Ty.function.inj
    (started.selected.spec.2.1.symm.trans imported.function_type.symm)
  obtain ⟨actual, generation, value, finalStore, completed, exported, valueEq, _typeEq, _budgetEq, sessionAt⟩ :=
    resumed.indexed_succeeded atCheckpoint
  obtain ⟨sources, packing, arity, sourceSize, outcome, after, finalMap, finalWorld, trace, resultAt⟩ :=
    SelectedCompilationPublicDirectCallableHistory.completed_reflects_at_arity
      (completion := receiving) support issued (state.extension.trans extended)
      retained state.history.physical entry member entryType input
      started parameterView.symm metadata completed invocation
  obtain ⟨payload, decoded, _imported⟩ := exported.reimports
  obtain ⟨source, sourceValue, represented, _heaps, _world, _returned, _related, _stable, _typed, _valueTyped⟩ :=
    RecursivePublicApplicationResult.returned_value resultAt decoded
  obtain ⟨reached, _related, history⟩ := retained.after_packed_success started.original exported resultAt
  have returnedRegistry := started.returned_registry exported
  let next : State rows anchor initial profile recipe completion.session entries := {
    artifact := state.artifact
    session := actual.session
    mapping := finalMap
    world := finalWorld
    heap := after
    store := finalStore
    caller := reached
    atSession := sessionAt
    atRecipe := state.atRecipe
    receiving := receiving
    issued := issued
    extension := state.extension.trans extended
    registry := (congrArg (·.registry) contextAt).symm ▸ returnedRegistry
    history := ⟨history, state.history.physical.extend resultAt.2.2.2.2.1⟩ }
  have lifted : Staging.Recursive.Size.Applies (Program.ofChecked recipe.compiled.sourceProgram)
      (SelectedCompilationPhysicalProgramSupport.stages recipe.compiled) sourceSize invocation
      anchor.function.context state.heap entry.source sources (.value source) next.heap := sourceValue ▸ trace
  have encoded := (exported.reimports_payload started.requested decoded).2
  rw [← valueEq] at encoded
  exact ⟨sources, packing, arity, source, next, sourceSize, lifted, lifted.sound.value_plain,
    actualResult, payload, nativeResult, resultView, encoded, represented⟩

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicDirectOutputReflection
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicNamedOutputReflection
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicNamedOutputReflection
open Core Frontend SourceInference
open CallableIndexedOwnedPreparedFiniteNamedInventories (Input Inventory headers)
open CallableIndexedOwnedPreparedBootstrapRootState (keys)
open CallableIndexedOwnedFunctionValues (Header)
open SelectedCompilationPublicSessionState
open SelectedCompilationStageClosedDirectForward.Output (ReturnedValue)
open SelectedCompilationPhysicalProgramSupport (stagePrepared)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {inputs : List (Input compiled)} {rows : Inventory inputs}
  {anchor : Header compiled (Program.ofChecked compiled.sourceProgram)}
  {initial : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
  {profile : compiled.compatible.checked.catalog.callableContracts = true}
  {recipe : SourceCoreIndexedSession.Recipe}

theorem State.reflect_output_at_input_registry (support : SelectedCompilationPhysicalProgramSupport.Support compiled (headers rows) (keys compiled) initial)
    (prepared : SourceCoreIndexedSession.Recipe.prepare compiled = .ok recipe)
    {options : SourceCoreExecution.RunOptions}
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    {entries : List RecursiveNamedPublicFunctionHistory.Entry}
    (state : State rows anchor initial profile recipe session entries)
    {key : SourceCoreIndexedSession.Key} {publicArguments : List SourceCorePublicValues.Value}
    (call : Call session key publicArguments options)
    (request : RecursiveNamedPublicHistoryFrontdoor.Started (headers rows) prepared
      call.checkpoint state.session key publicArguments options.inputValidationFuel state.world state.store)
    {arguments : List Dynamic.Value}
    (inputs : RecursiveNamedPublicFunctionHistoryInputs.Inputs entries request.header.function.context
      (request.header.bindings.map (fun binding => binding.1.scheme.body)) publicArguments arguments)
    (descriptor : SourceCoreCallableContracts.Descriptor compiled.indexed.ancestry.graph.inputs.callable.table
      (.named request.header.named.signature.key))
    (invocation : Staging.Recursive.Scope) :
    ∃ source, ∃ after : State rows anchor initial profile recipe call.completion.session entries,
      SourceCall anchor request.header invocation state.heap arguments (.value source) after.heap ∧
      PlainValue anchor request.header invocation state.heap arguments source after.heap ∧
      ReturnedValue call.completion after request.header.function.resultType source options.outputValidationFuel := by
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
  obtain ⟨payload, decoded, _imported⟩ := succeeded.reimports
  obtain ⟨source, sourceValue, represented, _heaps, _world, _returned, _related, _stable, _typed, _valueTyped⟩ :=
    RecursiveNamedPublicReturnedValues.returned_value result decoded
  obtain ⟨reached, _related, retained⟩ := history.semantic.after_success
    (SourceCoreIndexedSession.Recipe.prepare_compiled prepared) request.started request.selected succeeded result
  have physicalRetained := history.after_result result retained
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
  have lifted : SourceCall anchor request.header invocation state.heap arguments (.value source) next.heap :=
    ⟨request.rawD, request.function, sourceSize, request.sourceAt, sourceValue ▸ trace⟩
  have encoded := (succeeded.reimports_payload requested decoded).2
  rw [← valueEq] at encoded
  exact ⟨source, next, lifted, lifted.value_plain, request.header.function.resultType,
    payload, request.header.output, rfl, encoded, represented⟩


end Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicNamedOutputReflection
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicInitialDataOutputReflection
/-! Initial public success reflects to a complete Source value and heap. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicInitialDataOutputReflection
open Core Frontend SourceInference
open CallableIndexedOwnedPreparedFiniteNamedInventories (Input Inventory headers)
open CallableIndexedOwnedFunctionValues (Header)
open SelectedCompilationStageClosedDirectForward.Output (ReturnedValue)
open CallableIndexedOwnedPreparedBootstrapRootState (keys)
open SelectedCompilationPublicSessionState (StartedCall Call State SourceCall PlainValue)
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

theorem first_output
    (distinct : (inputs.map (fun input => input.prepared.index)).Nodup)
    (call : Call session key publicArguments options)
    (start : Started rows prepared header call.toStartedCall)
    (inputTypes : RecursiveNamedPublicDataArgumentReceipts.PublicDataTypes
      header.function.context publicArguments header.types)
    {arguments : List Dynamic.Value}
    (inputMeanings : RecursiveNamedPublicDataInputs.Meanings publicArguments arguments)
    (descriptor : SourceCoreCallableContracts.Descriptor recipe.compiled.indexed.ancestry.graph.inputs.callable.table
      (.named header.named.signature.key))
    (invocation : Staging.Recursive.Scope) :
    ∃ source, ∃ after : State rows anchor initial support.profile recipe call.completion.session [],
      SourceCall anchor header invocation ⟨[]⟩ arguments (.value source) after.heap ∧
      PlainValue anchor header invocation ⟨[]⟩ arguments source after.heap ∧
      ReturnedValue call.completion after header.function.resultType source options.outputValidationFuel := by
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
  rw [resultType] at requested
  obtain ⟨payload, decoded, _imported⟩ := succeeded.reimports
  obtain ⟨source, sourceValue, represented, _heaps, _world, _returned, _related, _stable, _typed, _valueTyped⟩ :=
    RecursiveNamedPublicReturnedValues.returned_value result decoded
  have returnedRegistry := start.started.returned_registry succeeded
  rw [← receiverRegistry] at returnedRegistry
  let next : State rows anchor initial support.profile recipe call.completion.session [] := {
    artifact := start.artifact, session := actual.session, mapping := finalMap, world := finalWorld,
    heap := after, store := finalStore, caller := reached, atSession := returnedAt,
    atRecipe := start.started.recipe_eq, receiving := receiving, issued := receiverIssued,
    extension := receiverExtension, registry := returnedRegistry, history := ⟨retained, physicalRetained⟩ }
  have lifted : SourceCall anchor header invocation ⟨[]⟩ arguments (.value source) next.heap :=
    ⟨rawD, function, sourceSize, sourceAt, sourceValue ▸ trace⟩
  have encoded := (succeeded.reimports_payload requested decoded).2
  rw [← valueEq] at encoded
  exact ⟨source, next, lifted, lifted.value_plain, header.function.resultType,
    payload, header.output, rfl, encoded, represented⟩

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicInitialDataOutputReflection
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicInitialOutputReflection
/-! Initial public success reflects to a complete Source value and heap. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicInitialOutputReflection
open Core Frontend SourceInference
open CallableIndexedOwnedPreparedFiniteNamedInventories (Input Inventory headers)
open CallableIndexedOwnedFunctionValues (Header)
open SelectedCompilationStageClosedDirectForward.Output (ReturnedValue)
open CallableIndexedOwnedPreparedBootstrapRootState (keys)
open SelectedCompilationPublicSessionState (StartedCall Call State SourceCall PlainValue)
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

theorem first_output
    (distinct : (inputs.map (fun input => input.prepared.index)).Nodup)
    (call : Call session key publicArguments options)
    (start : Started rows prepared header call.toStartedCall)
    (simple : ∀ value ∈ publicArguments, SourceCoreIndexedSession.SimplePublic value)
    (inputTypes : RecursiveNamedPublicDataArgumentReceipts.PublicDataTypes
      header.function.context publicArguments header.types)
    {arguments : List Dynamic.Value}
    (inputMeanings : RecursiveNamedPublicDataInputs.Meanings publicArguments arguments)
    (descriptor : SourceCoreCallableContracts.Descriptor recipe.compiled.indexed.ancestry.graph.inputs.callable.table
      (.named header.named.signature.key))
    (invocation : Staging.Recursive.Scope) :
    ∃ source, ∃ after : State rows anchor initial support.profile recipe call.completion.session [],
      SourceCall anchor header invocation ⟨[]⟩ arguments (.value source) after.heap ∧
      PlainValue anchor header invocation ⟨[]⟩ arguments source after.heap ∧
      ReturnedValue call.completion after header.function.resultType source options.outputValidationFuel := by
  have _ := simple
  exact SelectedCompilationPublicInitialDataOutputReflection.first_output
    rows prepared anchor header support distinct call start inputTypes inputMeanings descriptor invocation

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicInitialOutputReflection
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationCertifiedPublicOutputReflection
/-! Closed reflection entry points retain the complete public result and the
ordinary Source outcome using the actual checker-derived selected support. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationCertifiedPublicSession
open Core Frontend SourceInference
open CallableIndexedOwnedPreparedFiniteNamedInventories (headers)
open CallableIndexedOwnedFunctionValues (Header)
open SelectedCompilationPublicSessionState (Call SourceCall PlainValue)
open RecursiveNamedPublicFunctionHistory (Entry)
open SelectedCompilationStageClosedDirectForward.Output (ReturnedValue)

variable {recipe : SourceCoreIndexedSession.Recipe} {issued : Profiled recipe}
  {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
  {key : SourceCoreIndexedSession.Key} {publicArguments : List SourceCorePublicValues.Value}
  {options : SourceCoreExecution.RunOptions}

/-- Actual initial success reflects to the whole Source value and exact heap. -/
theorem Initial.reflect_output_plain
    {call : Call session key publicArguments options}
    (initial : Initial issued.toIssued call.toStartedCall)
    (simple : ∀ value ∈ publicArguments, SourceCoreIndexedSession.SimplePublic value)
    (inputTypes : RecursiveNamedPublicDataArgumentReceipts.PublicDataTypes
      initial.header.function.context publicArguments initial.header.types)
    {arguments : List Dynamic.Value}
    (inputMeanings : RecursiveNamedPublicDataInputs.Meanings publicArguments arguments)
    (invocation : Staging.Recursive.Scope) :
    ∃ source, ∃ after : issued.toIssued.State initial.header call.completion.session [],
      SourceCall initial.header initial.header invocation ⟨[]⟩ arguments (.value source) after.heap ∧
      PlainValue initial.header initial.header invocation ⟨[]⟩ arguments source after.heap ∧
      ReturnedValue call.completion after initial.header.function.resultType source options.outputValidationFuel := by
  obtain ⟨descriptor⟩ := header_descriptor initial.header
  exact SelectedCompilationPublicInitialOutputReflection.first_output issued.catalog.rows issued.prepared
    initial.header initial.header issued.support issued.catalog.distinct call initial.start simple
    inputTypes inputMeanings descriptor invocation

variable (issued : Profiled recipe)
  {anchor : Header recipe.compiled (Program.ofChecked recipe.compiled.sourceProgram)}
  {entries : List Entry}

/-- Named completion keeps the receiving registry and all prior callable captures. -/
theorem Profiled.reflect_output_plain
    (state : issued.toIssued.State anchor session entries)
    (call : Call session key publicArguments options)
    (request : RecursiveNamedPublicHistoryFrontdoor.Started (headers issued.catalog.rows) issued.prepared
      call.checkpoint state.session key publicArguments options.inputValidationFuel state.world state.store)
    {arguments : List Dynamic.Value}
    (inputs : RecursiveNamedPublicFunctionHistoryInputs.Inputs entries request.header.function.context
      (request.header.bindings.map (fun binding => binding.1.scheme.body)) publicArguments arguments)
    (invocation : Staging.Recursive.Scope) :
    ∃ source, ∃ after : issued.toIssued.State anchor call.completion.session entries,
      SourceCall anchor request.header invocation state.heap arguments (.value source) after.heap ∧
      PlainValue anchor request.header invocation state.heap arguments source after.heap ∧
      ReturnedValue call.completion after request.header.function.resultType source options.outputValidationFuel := by
  obtain ⟨descriptor⟩ := header_descriptor request.header
  exact SelectedCompilationPublicNamedOutputReflection.State.reflect_output_at_input_registry
    issued.support issued.prepared state call request inputs descriptor invocation

/-- Packed direct completion recovers the true arity and complete Source value;
host and Source raw result types retain their actual compatibility equality. -/
theorem Profiled.reflect_direct_output_plain
    (state : issued.toIssued.State anchor session entries)
    (entry : Entry) (member : entry ∈ entries)
    {parameter result : TypeSystem.Ty}
    (entryType : entry.sourceType = .function parameter result)
    {argument : SourceCorePublicValues.Value} {packedSource : Dynamic.Value}
    (input : RecursiveNamedPublicFunctionHistoryInputs.Input entries anchor.function.context
      parameter argument packedSource)
    {completion : SourceCoreExecution.Completion artifact}
    (invoked : session.InvokeAt entry.handle argument options (.ok (.succeeded completion)))
    (invocation : Staging.Recursive.Scope) :
    ∃ sources, Dynamic.ValuesPack sources packedSource ∧
      RecursivePublicCallableArity.Arity (Program.ofChecked recipe.compiled.sourceProgram) entry.source sources.length ∧
      ∃ source, ∃ after : issued.toIssued.State anchor completion.session entries,
      ∃ size, Staging.Recursive.Size.Applies (Program.ofChecked recipe.compiled.sourceProgram)
        (SelectedCompilationPhysicalProgramSupport.stages recipe.compiled) size
        invocation anchor.function.context state.heap entry.source sources (.value source) after.heap ∧
      Dynamic.CallableApplies (Program.ofChecked recipe.compiled.sourceProgram) anchor.function.context
        invocation.evidence (Staging.Recursive.callableEvidence entry.source)
        state.heap entry.source sources source after.heap ∧
      ReturnedValue completion after result source options.outputValidationFuel :=
  SelectedCompilationPublicDirectOutputReflection.State.reflect_output issued.support issued.prepared
    state entry member entryType input invoked invocation

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationCertifiedPublicSession
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationCertifiedPublicInitialData
/-! Initial calls accept the complete structurally typed data input family.
Actual bootstrap and public encoding construct the heap and receiving registry;
ordinary Source traces supply execution outcomes. The raw input certificate
retains constructor, mapping and proxy metadata before runtime erasure. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationCertifiedPublicSession
open Core Frontend SourceInference
open SelectedCompilationPublicSessionState
open SelectedCompilationStagePublicInputLifting
open RecursiveNamedPublicScalarResults (ScalarOutput)
open SelectedCompilationStageClosedDirectForward.Output (ReturnedValue)

variable {recipe : SourceCoreIndexedSession.Recipe} {issued : Profiled recipe}
  {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
  {key : SourceCoreIndexedSession.Key} {publicArguments : List SourceCorePublicValues.Value}
  {options : SourceCoreExecution.RunOptions}

theorem Initial.lift_data_call
    {call : StartedCall session key publicArguments options} (initial : Initial issued.toIssued call)
    (inputTypes : RecursiveNamedPublicDataArgumentReceipts.PublicDataTypes
      initial.header.function.context publicArguments initial.header.types)
    {arguments : List Dynamic.Value}
    (inputMeanings : RecursiveNamedPublicDataInputs.Meanings publicArguments arguments)
    {invocation : Staging.Recursive.Scope} {plain : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (trace : PlainCall initial.header initial.header invocation ⟨[]⟩ arguments plain after) :
    ∃ staged reached,
      SourceCall initial.header initial.header invocation ⟨[]⟩ arguments staged reached ∧
      Staging.Recursive.Lifting.Adapted plain after staged reached :=
  SelectedCompilationStageInitialDataInputLifting.lift_call
    issued.catalog.rows issued.prepared initial.header initial.header issued.support
    (SelectedCompilationStagePublicProgramLifting.named_bodies issued.support)
    issued.catalog.distinct call initial.start inputTypes inputMeanings trace

theorem Initial.forward_data_failure
    {call : StartedCall session key publicArguments options} (initial : Initial issued.toIssued call)
    (inputTypes : RecursiveNamedPublicDataArgumentReceipts.PublicDataTypes
      initial.header.function.context publicArguments initial.header.types)
    {arguments : List Dynamic.Value}
    (inputMeanings : RecursiveNamedPublicDataInputs.Meanings publicArguments arguments)
    {invocation : Staging.Recursive.Scope} {after : Dynamic.Heap} {failure : Staging.Recursive.Failure}
    (trace : SourceCall initial.header initial.header invocation ⟨[]⟩ arguments (.fault failure) after) :
    SelectedCompilationPublicSessionFailureForward.FailureForwardAt (entries := []) issued.catalog.rows
      initial.header issued.initial issued.support.profile recipe failure call after :=
  SelectedCompilationPublicSessionInitialDataFailureForward.first_failure issued.catalog.rows issued.prepared
    initial.header initial.header issued.support issued.registryBodies issued.catalog.distinct call initial.start
    inputTypes inputMeanings trace

theorem Initial.forward_data_scalar_plain
    {call : StartedCall session key publicArguments options} (initial : Initial issued.toIssued call)
    (inputTypes : RecursiveNamedPublicDataArgumentReceipts.PublicDataTypes
      initial.header.function.context publicArguments initial.header.types)
    {arguments : List Dynamic.Value}
    (inputMeanings : RecursiveNamedPublicDataInputs.Meanings publicArguments arguments)
    (scalar : ScalarOutput)
    (rawType : initial.header.function.resultType = scalar.sourceType)
    (nativeType : initial.header.output = scalar.nativeType)
    {invocation : Staging.Recursive.Scope} {after : Dynamic.Heap}
    (trace : PlainValue initial.header initial.header invocation ⟨[]⟩ arguments scalar.source after) :
    (SourceCall initial.header initial.header invocation ⟨[]⟩ arguments (.value scalar.source) after ∧
      SelectedCompilationPublicSessionScalarForward.ForwardAt (entries := []) issued.catalog.rows
        initial.header issued.initial issued.support.profile recipe scalar call after) ∨
    SelectedCompilationStageClosedInitialForward.StageStopped issued call initial invocation arguments := by
  obtain ⟨staged, reached, lifted, adapted⟩ := initial.lift_data_call inputTypes inputMeanings (plain_value trace)
  cases adapted with
  | completed =>
    exact .inl ⟨lifted, SelectedCompilationPublicSessionInitialDataScalarForward.first_scalar
      issued.catalog.rows issued.prepared initial.header initial.header issued.support issued.catalog.distinct
      scalar call initial.start inputTypes inputMeanings rawType nativeType lifted⟩
  | rejected origin occurrence reason reached =>
    exact .inr ⟨origin, occurrence, reason, reached, lifted.failure_plain, lifted,
      initial.forward_data_failure inputTypes inputMeanings lifted⟩

theorem Initial.forward_data_fault_plain
    {call : StartedCall session key publicArguments options} (initial : Initial issued.toIssued call)
    (inputTypes : RecursiveNamedPublicDataArgumentReceipts.PublicDataTypes
      initial.header.function.context publicArguments initial.header.types)
    {arguments : List Dynamic.Value}
    (inputMeanings : RecursiveNamedPublicDataInputs.Meanings publicArguments arguments)
    {invocation : Staging.Recursive.Scope} {after : Dynamic.Heap} {reason : Dynamic.SemanticFault}
    (trace : PlainFault initial.header initial.header invocation ⟨[]⟩ arguments reason after) :
    (SourceCall initial.header initial.header invocation ⟨[]⟩ arguments (.fault (.semantic reason)) after ∧
      SelectedCompilationPublicSessionFailureForward.FailureForwardAt (entries := []) issued.catalog.rows
        initial.header issued.initial issued.support.profile recipe (.semantic reason) call after) ∨
    SelectedCompilationStageClosedInitialForward.StageStopped issued call initial invocation arguments := by
  obtain ⟨staged, reached, lifted, adapted⟩ := initial.lift_data_call inputTypes inputMeanings (plain_fault trace)
  cases adapted with
  | completed => exact .inl ⟨lifted, initial.forward_data_failure inputTypes inputMeanings lifted⟩
  | rejected origin occurrence reason reached =>
    exact .inr ⟨origin, occurrence, reason, reached, lifted.failure_plain, lifted,
      initial.forward_data_failure inputTypes inputMeanings lifted⟩

theorem Initial.forward_data_output_plain
    {call : StartedCall session key publicArguments options} (initial : Initial issued.toIssued call)
    (inputTypes : RecursiveNamedPublicDataArgumentReceipts.PublicDataTypes
      initial.header.function.context publicArguments initial.header.types)
    {arguments : List Dynamic.Value}
    (inputMeanings : RecursiveNamedPublicDataInputs.Meanings publicArguments arguments)
    {invocation : Staging.Recursive.Scope} {after : Dynamic.Heap} {value : Dynamic.Value}
    (trace : PlainValue initial.header initial.header invocation ⟨[]⟩ arguments value after) :
    (SourceCall initial.header initial.header invocation ⟨[]⟩ arguments (.value value) after ∧
      SelectedCompilationStageClosedDirectForward.Output.ForwardAt issued.catalog.rows initial.header issued.initial
        issued.support.profile recipe [] initial.header.function.resultType call.checkpoint value after) ∨
    SelectedCompilationStageClosedInitialForward.StageStopped issued call initial invocation arguments := by
  obtain ⟨staged, reached, lifted, adapted⟩ := initial.lift_data_call inputTypes inputMeanings (plain_value trace)
  cases adapted with
  | completed =>
    exact .inl ⟨lifted, SelectedCompilationStageInitialDataOutputForward.first_output
      issued.catalog.rows issued.prepared initial.header initial.header issued.support issued.catalog.distinct
      call initial.start inputTypes inputMeanings lifted⟩
  | rejected origin occurrence reason reached =>
    exact .inr ⟨origin, occurrence, reason, reached, lifted.failure_plain, lifted,
      initial.forward_data_failure inputTypes inputMeanings lifted⟩

theorem Initial.forward_data_function_plain
    {call : StartedCall session key publicArguments options} (initial : Initial issued.toIssued call)
    (inputTypes : RecursiveNamedPublicDataArgumentReceipts.PublicDataTypes
      initial.header.function.context publicArguments initial.header.types)
    {arguments : List Dynamic.Value}
    (inputMeanings : RecursiveNamedPublicDataInputs.Meanings publicArguments arguments)
    {parameter resultType : TypeSystem.Ty} {value : Dynamic.Value}
    (functionResult : SourceCoreRawMetadata.runtimeType initial.header.function.resultType =
      .function parameter resultType)
    {invocation : Staging.Recursive.Scope} {after : Dynamic.Heap}
    (trace : PlainValue initial.header initial.header invocation ⟨[]⟩ arguments value after) :
    (SourceCall initial.header initial.header invocation ⟨[]⟩ arguments (.value value) after ∧
      SelectedCompilationPublicSessionInitialForward.ForwardAt issued.catalog.rows initial.header
        initial.header issued.support call value after) ∨
    SelectedCompilationStageClosedInitialForward.StageStopped issued call initial invocation arguments := by
  obtain ⟨staged, reached, lifted, adapted⟩ := initial.lift_data_call inputTypes inputMeanings (plain_value trace)
  cases adapted with
  | completed =>
    exact .inl ⟨lifted, SelectedCompilationPublicSessionInitialDataForward.first_function
      issued.catalog.rows issued.prepared initial.header initial.header issued.support issued.catalog.distinct
      call initial.start inputTypes inputMeanings functionResult lifted⟩
  | rejected origin occurrence reason reached =>
    exact .inr ⟨origin, occurrence, reason, reached, lifted.failure_plain, lifted,
      initial.forward_data_failure inputTypes inputMeanings lifted⟩

theorem Initial.reflect_data_scalar_plain
    {call : Call session key publicArguments options} (initial : Initial issued.toIssued call.toStartedCall)
    (inputTypes : RecursiveNamedPublicDataArgumentReceipts.PublicDataTypes
      initial.header.function.context publicArguments initial.header.types)
    {arguments : List Dynamic.Value}
    (inputMeanings : RecursiveNamedPublicDataInputs.Meanings publicArguments arguments)
    (scalar : ScalarOutput) (returned : call.completion.value = scalar.publicValue)
    (rawType : initial.header.function.resultType = scalar.sourceType)
    (nativeType : initial.header.output = scalar.nativeType)
    (invocation : Staging.Recursive.Scope) :
    ∃ after : issued.toIssued.State initial.header call.completion.session [],
      PlainValue initial.header initial.header invocation ⟨[]⟩ arguments scalar.source after.heap := by
  obtain ⟨descriptor⟩ := header_descriptor initial.header
  obtain ⟨after, trace⟩ := SelectedCompilationPublicSessionInitialDataScalarStep.first_scalar
    issued.catalog.rows issued.prepared initial.header initial.header issued.support issued.catalog.distinct
    scalar call returned initial.start inputTypes inputMeanings rawType nativeType descriptor invocation
  exact ⟨after, trace.value_plain⟩

theorem Initial.reflect_data_failure_plain
    {call : StartedCall session key publicArguments options} (initial : Initial issued.toIssued call)
    (returned : SourceCoreExecution.Session artifact) (reason : Word)
    (failedCall : session.RunAt key publicArguments options (.ok (.failed reason returned)))
    (inputTypes : RecursiveNamedPublicDataArgumentReceipts.PublicDataTypes
      initial.header.function.context publicArguments initial.header.types)
    {arguments : List Dynamic.Value}
    (inputMeanings : RecursiveNamedPublicDataInputs.Meanings publicArguments arguments)
    (invocation : Staging.Recursive.Scope) :
    ∃ failure, ∃ after : issued.toIssued.State initial.header returned [],
      SourceCall initial.header initial.header invocation ⟨[]⟩ arguments (.fault failure) after.heap ∧
      FailureProjection initial.header initial.header invocation ⟨[]⟩ arguments failure after.heap ∧
      CallableIndexedOwnedPublicDecodedStagedCallFaults.faults after.receiving.result.diagnostics failure reason := by
  obtain ⟨descriptor⟩ := header_descriptor initial.header
  obtain ⟨failure, after, trace, diagnostic⟩ := SelectedCompilationPublicSessionInitialDataFailureStep.first_failure
    issued.catalog.rows issued.prepared initial.header initial.header issued.support issued.registryBodies
    issued.catalog.distinct call returned reason failedCall initial.start inputTypes inputMeanings descriptor invocation
  exact ⟨failure, after, trace, trace.failure_plain, diagnostic⟩

theorem Initial.reflect_data_output_plain
    {call : Call session key publicArguments options} (initial : Initial issued.toIssued call.toStartedCall)
    (inputTypes : RecursiveNamedPublicDataArgumentReceipts.PublicDataTypes
      initial.header.function.context publicArguments initial.header.types)
    {arguments : List Dynamic.Value}
    (inputMeanings : RecursiveNamedPublicDataInputs.Meanings publicArguments arguments)
    (invocation : Staging.Recursive.Scope) :
    ∃ source, ∃ after : issued.toIssued.State initial.header call.completion.session [],
      SourceCall initial.header initial.header invocation ⟨[]⟩ arguments (.value source) after.heap ∧
      PlainValue initial.header initial.header invocation ⟨[]⟩ arguments source after.heap ∧
      ReturnedValue call.completion after initial.header.function.resultType source options.outputValidationFuel := by
  obtain ⟨descriptor⟩ := header_descriptor initial.header
  exact SelectedCompilationPublicInitialDataOutputReflection.first_output issued.catalog.rows issued.prepared
    initial.header initial.header issued.support issued.catalog.distinct call initial.start
    inputTypes inputMeanings descriptor invocation

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationCertifiedPublicSession
end
