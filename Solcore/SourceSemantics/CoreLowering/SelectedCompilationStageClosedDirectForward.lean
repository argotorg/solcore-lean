import Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicSessionDirectScalarForward
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationStagePublicDirectInputLifting
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicReturnedValues
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicClosureHistory
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicSessionDirectOutputCollection
import Solcore.SourceSemantics.CoreLowering.CompatiblePublicOutputShapes

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
open RecursiveNamedPublicPhysicalSessionState
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
