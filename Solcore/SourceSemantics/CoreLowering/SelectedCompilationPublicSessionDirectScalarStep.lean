import Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicReturnedValues
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicClosureHistory
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicSessionState
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicScalarResults
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicDirectCallableHistory
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicActualRegistryStart

/-! Actual packed callable execution retains the complete physical cache and
all previous exports. The input encoder supplies the reached registry, and the
shared static package closes every body meaning used by reflection. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicSessionDirectScalarStep
open Core Frontend SourceInference
open CallableIndexedOwnedPreparedFiniteNamedInventories (Input Inventory headers)
open CallableIndexedOwnedPreparedBootstrapRootState (keys)
open CallableIndexedOwnedFunctionValues (Header)
open RecursiveNamedPublicFunctionHistory (Entry)
open SelectedCompilationPublicSessionState
open RecursiveNamedPublicScalarResults (ScalarOutput)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {inputs : List (Input compiled)} {rows : Inventory inputs}
  {anchor : Header compiled (Program.ofChecked compiled.sourceProgram)}
  {initial : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
  {profile : compiled.compatible.checked.catalog.callableContracts = true}
  {recipe : SourceCoreIndexedSession.Recipe}

/-- The retained Source callable determines the exact argument arity and the
actual public result determines the Source scalar, at the returned heap. -/
theorem State.invoke_scalar
    (support : SelectedCompilationPhysicalProgramSupport.Support
      compiled (headers rows) (keys compiled) initial)
    (prepared : SourceCoreIndexedSession.Recipe.prepare compiled = .ok recipe)
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    {entries : List Entry}
    (state : State rows anchor initial profile recipe session entries)
    (entry : Entry) (member : entry ∈ entries) (scalar : ScalarOutput)
    {parameter hostParameter : TypeSystem.Ty}
    (entryType : entry.sourceType = .function parameter scalar.sourceType)
    (handleType : entry.handle.sourceType = .function hostParameter scalar.sourceType)
    {argument : SourceCorePublicValues.Value} {packedSource : Dynamic.Value}
    (input : RecursiveNamedPublicFunctionHistoryInputs.Input entries anchor.function.context
      parameter argument packedSource)
    {options : SourceCoreExecution.RunOptions}
    {completion : SourceCoreExecution.Completion artifact}
    (invoked : session.InvokeAt entry.handle argument options (.ok (.succeeded completion)))
    (output : completion.value = scalar.publicValue)
    (invocation : Staging.Recursive.Scope) :
    ∃ sources, Dynamic.ValuesPack sources packedSource ∧
      RecursivePublicCallableArity.Arity (Program.ofChecked compiled.sourceProgram) entry.source sources.length ∧
      ∃ next : State rows anchor initial profile recipe completion.session entries,
      ∃ size, Staging.Recursive.Size.Applies (Program.ofChecked compiled.sourceProgram)
        (SelectedCompilationPhysicalProgramSupport.stages compiled) size
        invocation anchor.function.context state.heap entry.source sources (.value scalar.source) next.heap := by
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
  have signature := started.selected.signature handleType
  have requested := started.requested_exact handleType
  have projected := started.resultProjection
  rw [signature.2] at projected
  have nativeResultEq : nativeResult = scalar.nativeType := by
    cases scalar <;> exact (Except.ok.inj projected).symm
  subst nativeResult
  obtain ⟨receiving, _indexed, contextAt, issued, extended, retained, _represented, _typed, _diagnostics⟩ :=
    RecursiveNamedPublicActualRegistryStart.packed_input state.history.semantic state.registry
      member entryType input started
  have metadata : SourceCoreRawMetadata.Extends encodedValues.registry receiving.result.context.registry := by
    rw [contextAt]
    exact .refl _
  obtain ⟨parameterView, _resultView⟩ := TypeSystem.Ty.function.inj
    (started.selected.spec.2.1.symm.trans imported.function_type.symm)
  obtain ⟨actual, generation, value, finalStore, completed, exported, valueEq, _typeEq, _budgetEq, sessionAt⟩ :=
    resumed.indexed_succeeded atCheckpoint
  obtain ⟨sources, packing, arity, sourceSize, outcome, after, finalMap, finalWorld, trace, resultAt⟩ :=
    SelectedCompilationPublicDirectCallableHistory.completed_reflects_at_arity
      (completion := receiving) support issued (state.extension.trans extended)
      retained state.history.physical entry member entryType input
      started parameterView.symm metadata completed invocation
  have outcomeValue := scalar.source_value exported requested (valueEq.symm.trans output) resultAt.1
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
  exact ⟨sources, packing, arity, next, sourceSize, outcomeValue ▸ trace⟩

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicSessionDirectScalarStep
