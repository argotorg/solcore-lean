import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedBodyRestorationAdmission
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedLambdaSourceAdmission

/-! Real parameter allocation retains the actual installed stable frame.
All rows sharing that physical frame carry the new history; other rows keep
their own stable histories. The literal allocation frame then authenticates
every row of the reached pool. Original Source argument typing supplies the
deep heap field at that same parameter endpoint. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedLambdaParameterAdmission
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedHistory SourceCoreCallableIndexedFrames CallableIndexedLambdaValues
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedIndirectExpressionHeads (StableRows)

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}

/-- Installation updates every key sharing the written physical frame. Its
actual stable history authenticates all of those rows, including duplicates. -/
theorem install_rows {index : ProtectedStateTransition.Index}
    (saved : State headers keys index) (selected : Fin keys.length)
    (stable : StableRows saved) {next : NativeFrame} {ghost : GhostFrame}
    {metadata : Option MetadataState}
    (history : Carries compiled.indexed.ancestry.graph.inputs
      compiled.indexed.ancestry.graph.table next ghost metadata) :
    StableRows (install saved selected (.stable history)) := by
  intro i
  have current := CallableIndexedAuthorityPool.Pool.install_current saved selected i (.stable history)
  have actualGhost := CallableIndexedAuthorityPool.Pool.install_ghost saved selected i (.stable history)
  change ((install saved selected (.stable history)).rows i).authority.current = _ at current
  change ((install saved selected (.stable history)).rows i).authority.ghost = _ at actualGhost
  by_cases same : keys[i.val].frameLocation = keys[selected.val].frameLocation
  · refine ⟨metadata, ?_⟩
    erw [current, actualGhost, if_pos same, if_pos same]
    exact history
  · obtain ⟨oldMetadata, oldHistory⟩ := stable i
    refine ⟨oldMetadata, ?_⟩
    erw [current, actualGhost, if_neg same, if_neg same]
    exact oldHistory

/-- The genuine frame-preserving allocation may have any returned pool with
its own actual cells and ghosts. No record-prefix inverse supplies stability. -/
theorem after_parameters {index reachedIndex : ProtectedStateTransition.Index}
    (saved : State headers keys index) (reached : State headers keys reachedIndex)
    (selected : Fin keys.length) (stable : StableRows saved)
    {next : NativeFrame} {ghost : GhostFrame} {metadata : Option MetadataState}
    (history : Carries compiled.indexed.ancestry.graph.inputs
      compiled.indexed.ancestry.graph.table next ghost metadata)
    (frame : AdministrativePreserved index.mapping
      (index.store.set keys[selected.val].frameLocation (encode compiled.indexed.ancestry.layout.frame next))
      reachedIndex.mapping reachedIndex.store) :
    StableRows reached :=
  StableRows.after_administrative (install saved selected (.stable history)) reached
    (install_rows saved selected stable history) frame

variable {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope}
  {mapping : LocationMap} {world : StoreTyping} {actual : Environment}
  (captured : Captures compiled.indexed mapping world scope function.captured actual)
  (code : Code compiled.indexed function scope captured.administrative) (history : History code)
  (inputs : CallableIndexedLambdaEntryPrefix.Context (values := .initial compiled.compatible.checked) code)
  (functions : FunctionModel compiled.compatible.checked.catalog
    (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {registry : SourceCoreRawMetadata.Registry} {arguments : List Dynamic.Value} {nativeArguments : List Value}
  {before : Dynamic.Heap} {store : Store} {callerScope : SourceCoreLocalCell.Scope}
  {callerCanonical : Environment}
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (caller : State headers keys ⟨callerScope, mapping, world, before, store, callerCanonical⟩)
  (entry : CallableIndexedLambdaEntryPrefix.EntryFor (values := .initial compiled.compatible.checked)
    captured code history inputs functions registry arguments nativeArguments before store owner.key.frameLocation
    (caller.rows owner.position).authority.current (caller.rows owner.position).authority.ghost)
  (reached : State headers keys
    ⟨code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope,
      entry.entry.mapping, entry.entry.world, entry.entry.heap, entry.entry.store, entry.entry.canonical⟩)

/-- Full body admission is derived at the literal parameter entry. The real
ClosureFrame and Source-typed arguments supply heap typing; entry.nextHistory
and entry.frame supply every reached stable row. -/
theorem at_parameters (frame : Dynamic.ClosureFrame program function)
    (beforeTyped : Dynamic.HeapWellTyped function.context before)
    (argumentsTyped : Dynamic.ValuesHaveTypes function.context before arguments inputs.types)
    (stable : StableRows caller) :
    Admission CallableIndexedOwnedBodyRestorationAdmission.bridge inputs.context reached := by
  refine ⟨CallableIndexedOwnedLambdaSourceAdmission.heap_typed_at_parameters
    captured code history inputs functions entry frame beforeTyped argumentsTyped, ?_⟩
  exact after_parameters caller reached owner.position stable entry.nextHistory entry.entry.frame

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedLambdaParameterAdmission
