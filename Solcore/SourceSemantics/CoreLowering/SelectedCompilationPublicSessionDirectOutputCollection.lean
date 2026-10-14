import Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicReturnedValues
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicClosureHistory
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicSessionDirectSuccessStep
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicNestedOutputCollection

/-! Actual nested output encoding selects complete callable leaves in their
original payload and mapping-row order. Each selected leaf joins the positive
physical history at the same returned Source heap. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicSessionDirectOutputCollection
open Core Frontend SourceInference
open CallableIndexedOwnedPreparedFiniteNamedInventories (Input Inventory headers)
open CallableIndexedOwnedPreparedBootstrapRootState (keys)
open CallableIndexedOwnedFunctionValues (Header)
open RecursiveNamedPublicFunctionHistory (Entry)
open RecursiveNamedPublicPhysicalSessionState
open RecursiveNamedPublicNestedOutputSelections (Selection Selected)

def SelectedAt (checked : SourceCoreCompatibleCatalog.Checked)
    {artifact : SourceCoreExecution.Artifact}
    (completion : SourceCoreExecution.Completion artifact)
    {result : TypeSystem.Ty} (selection : Selection result completion.value)
    (source : Dynamic.Value) (fuel : Nat) (added : List Entry) : Prop :=
  ∃ (nativeArtifact : SourceCoreIndexedSession.Artifact)
    (actual : SourceCoreIndexedSession.Completion nativeArtifact) (native : Core.Value) (type : Core.Ty),
    completion.IndexedAt actual ∧ Selected checked actual.session selection source native type fuel added

theorem selected_of_cast {checked : SourceCoreCompatibleCatalog.Checked}
    {artifact : SourceCoreIndexedSession.Artifact} {session : SourceCoreIndexedSession.Session artifact}
    {result : TypeSystem.Ty} {first second : SourceCorePublicValues.Value} (same : first = second)
    {selection : Selection result first}
    {source : Dynamic.Value} {native : Core.Value} {type : Core.Ty} {fuel : Nat} {added : List Entry}
    (selected : Selected checked session (same ▸ selection : Selection result second)
      source native type fuel added) :
    Selected checked session selection source native type fuel added := by
  cases same
  exact selected

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {inputs : List (Input compiled)} {rows : Inventory inputs}
  {anchor : Header compiled (Program.ofChecked compiled.sourceProgram)}
  {initial : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
  {profile : compiled.compatible.checked.catalog.callableContracts = true}
  {recipe : SourceCoreIndexedSession.Recipe}

/-- Actual success determines the Source result and exact recursive output
selection. The receiving table comes from the real input encoder. -/
theorem State.collect
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
    (selection : Selection result completion.value)
    (invocation : Staging.Recursive.Scope) :
    ∃ sources, Dynamic.ValuesPack sources packedSource ∧
      RecursivePublicCallableArity.Arity (Program.ofChecked compiled.sourceProgram) entry.source sources.length ∧
      ∃ source added, ∃ next : State rows anchor initial profile recipe completion.session (entries ++ added),
      ∃ size, Staging.Recursive.Size.Applies (Program.ofChecked compiled.sourceProgram)
        (SelectedCompilationPhysicalProgramSupport.stages compiled) size
        invocation anchor.function.context state.heap entry.source sources (.value source) next.heap ∧
      added.map Entry.handle = selection.handles ∧
      SelectedAt compiled.compatible.checked completion selection source options.outputValidationFuel added := by
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
  have outputMetadata : SourceCoreRawMetadata.Extends receiving.result.context.registry encodedValues.registry := by
    rw [contextAt]
    exact .refl _
  obtain ⟨parameterView, resultView⟩ := TypeSystem.Ty.function.inj
    (started.selected.spec.2.1.symm.trans imported.function_type.symm)
  obtain ⟨actual, generation, value, finalStore, completed, exported, valueEq, typeEq, budgetEq, sessionAt⟩ :=
    resumed.indexed_succeeded atCheckpoint
  obtain ⟨sources, packing, arity, sourceSize, outcome, after, finalMap, finalWorld, trace, resultAt⟩ :=
    SelectedCompilationPublicDirectCallableHistory.completed_reflects_at_arity
      (completion := receiving) support issued (state.extension.trans extended)
      retained state.history.physical entry member entryType input
      started parameterView.symm metadata completed invocation
  have returnedRegistry := started.returned_registry exported
  obtain ⟨reached, source, payload, added, sourceValue, _nativeValue, selected, handles, _related, history⟩ :=
    retained.collect_packed_nested_success rfl state.atRecipe started.original started.requested resultView.symm
      exported resultAt returnedRegistry outputMetadata (valueEq ▸ selection)
  have originalSelected := selected_of_cast valueEq selected
  have originalHandles := handles.trans (Selection.handles_cast valueEq selection)
  let next : State rows anchor initial profile recipe completion.session (entries ++ added) := {
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
  exact ⟨sources, packing, arity, source, added, next, sourceSize, sourceValue ▸ trace,
    originalHandles, state.artifact, actual, payload, nativeResult,
    ⟨valueEq, typeEq, budgetEq, sessionAt⟩, originalSelected⟩

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicSessionDirectOutputCollection
