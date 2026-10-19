import Solcore.SourceSemantics.CoreLowering.CellAwarePublicSessionRegistry
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicDirectHandleMeaning
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicDirectPackedInputMeaning

/-! A direct packed handle start is recovered from the actual public receipt.
Its current history and encoder supply the receiving registry and input meaning. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwarePublicHandleStart
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedOwnedPreparedFiniteNamedInventories (Input Inventory headers)
open CallableIndexedOwnedPreparedBootstrapRootState (keys)
open CallableIndexedOwnedFunctionValues (Header)
open RecursiveNamedPublicFunctionHistory (Entry)

structure StartedCall {artifact : SourceCoreExecution.Artifact}
    (session : SourceCoreExecution.Session artifact) (handle : SourceCorePublicValues.Handle)
    (argument : SourceCorePublicValues.Value) (fuel : Nat) where
  checkpoint : SourceCoreExecution.Checkpoint artifact
  accepted : session.startHandlePacked handle argument fuel = .ok checkpoint

variable {recipe : SourceCoreIndexedSession.Recipe}
  {inputs : List (Input recipe.compiled)} {rows : Inventory inputs}
  {anchor : Header recipe.compiled (Program.ofChecked recipe.compiled.sourceProgram)}
  {initial : CallableIndexedOwnedPublicFaultReceivers.Receiver recipe.compiled.indexed}
  {functions : FunctionModel recipe.compiled.compatible.checked.catalog
    (CallableIndexedAmbient.ambientDefinitions recipe.compiled.indexed)}
  {cells : CellAwarePublicCells.Family (CallableIndexedAmbient.ambientDefinitions recipe.compiled.indexed).definitions}
  {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
  {entries : List Entry}
  (state : CellAwarePublicSessionState.State rows functions cells anchor initial recipe session entries)
  (entry : Entry) {parameter result : TypeSystem.Ty}
  {argument : SourceCorePublicValues.Value} {fuel : Nat}
  (call : StartedCall session entry.handle argument fuel)

structure Started (parameter result : TypeSystem.Ty) where
  checkpoint : SourceCoreIndexedSession.Checkpoint state.artifact
  actualParameter : TypeSystem.Ty
  actualResult : TypeSystem.Ty
  nativeParameter : Core.Ty
  nativeResult : Core.Ty
  callable : Core.Value
  packed : Core.Value
  encodedValues : SourceCoreCompatibleValues.Context
  atCheckpoint : call.checkpoint.IndexedAt checkpoint
  started : RecursiveNamedPublicDirectPackedInputMeaning.StartAt state.session entry.handle argument fuel
    checkpoint recipe state.world state.store actualParameter actualResult nativeParameter nativeResult callable packed encodedValues
  parameterView : SourceCoreRawMetadata.runtimeType parameter = SourceCoreRawMetadata.runtimeType actualParameter
  resultView : SourceCoreRawMetadata.runtimeType result = SourceCoreRawMetadata.runtimeType actualResult

/-- This inverts only the accepted original public start; it never executes a
second call or obtains callable meaning from the handle's spelling. -/
theorem from_call (member : entry ∈ entries) (entryType : entry.sourceType = .function parameter result) :
    Nonempty (Started state entry call parameter result) := by
  obtain ⟨checkpoint,atCheckpoint,original⟩ :=
    RecursiveNamedPublicDirectHandleMeaning.recover_handle_start state.atSession call.accepted
  have imported := (state.history.semantic.current.2.2.2.2 entry member).1
  rw [entryType] at imported
  obtain ⟨actualParameter,actualResult,nativeParameter,nativeResult,callable,packed,encodedValues,
      started,parameterView,resultView⟩ :=
    RecursiveNamedPublicDirectPackedInputMeaning.actual_start_compatible state.atRecipe
      state.history.semantic.current.1 imported original
  exact ⟨⟨checkpoint,actualParameter,actualResult,nativeParameter,nativeResult,callable,packed,encodedValues,
    atCheckpoint,started,parameterView.symm,resultView.symm⟩⟩

structure Ready (start : Started state entry call parameter result) (source : Dynamic.Value) where
  receiving : CallableIndexedOwnedPublicFaultReceivers.Receiver recipe.compiled.indexed
  contextAt : receiving.result.context = start.encodedValues
  issued : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt recipe.compiled.indexed receiving.entry
    receiving.result.context.registry receiving.result.extension receiving.result.diagnostics
  extension : SourceCoreRawMetadata.Extends initial.result.context.registry receiving.result.context.registry
  history : CellAwarePublicPhysicalHistory.History (headers := headers rows) (keys := keys recipe.compiled)
    (functions := functions) (cells := cells receiving.result.context.registry)
    (receiving := receiving.result.context.registry) (anchor := anchor)
    state.session state.mapping state.world state.heap state.store state.caller entries
  represented : ValueRep recipe.compiled.compatible.checked receiving.result.context.registry functions
    state.mapping state.world parameter source start.packed start.nativeParameter
  typed : Dynamic.ValueHasType anchor.function.context state.heap source parameter

/-- The original packed encoder transports all retained functions and derives
the Source input type at the exact current heap. -/
theorem of_started (covariant : CellAwarePublicCells.ExtendsRegistry cells)
    (member : entry ∈ entries) (entryType : entry.sourceType = .function parameter result)
    {source : Dynamic.Value}
    (input : RecursiveNamedPublicFunctionHistoryInputs.Input entries anchor.function.context parameter argument source)
    (start : Started state entry call parameter result) :
    Nonempty (Ready state entry call start source) := by
  obtain ⟨receiving,_indexed,contextAt,issued,extended,retained,represented,typed,_diagnostics⟩ :=
    CellAwarePublicActualRegistryStart.packed_input covariant state.history.semantic state.registry
      member entryType input start.started
  exact ⟨⟨receiving,contextAt,issued,state.extension.trans extended,
    ⟨retained,state.history.physical⟩,represented,typed⟩⟩

end Solcore.SourceSemantics.CoreLowering.CellAwarePublicHandleStart
