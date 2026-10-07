import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedFunctionState

/-! Returning from an actual body restores the saved physical caller cell in
its reached pool. Scope and canonical values then return to the caller while
all reached ordered record lists and full capture receipts remain retained. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedBodyRestoration
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedHistory SourceCoreCallableIndexedFrames
open CallableIndexedOwnedFunctionState

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {caller body : ProtectedStateTransition.Index}
  (saved : State headers keys caller) (reached : State headers keys body) (selected : Fin keys.length)

/-- The actual final map, world, heap and store come from the completed body.
Only the saved caller's source scope and canonical spine return. -/
def finalIndex : ProtectedStateTransition.Index :=
  ⟨caller.scope, body.mapping, body.world, body.heap,
    body.store.set keys[selected.val].frameLocation
      (encode compiled.indexed.ancestry.layout.frame (saved.rows selected).authority.current),
    caller.canonical⟩

/-- Owned pools are independent of the source spine, so this is the same
restored reached pool, with no new rows or capture reconstruction. -/
def returned : State headers keys (finalIndex (body := body) saved selected) :=
  CallableIndexedOwnedFunctionState.restored saved reached selected

theorem returned_records : records (returned saved reached selected) = records reached :=
  CallableIndexedOwnedFunctionState.restored_records saved reached selected

theorem returned_registered {record : CallableIndexedSnapshots.Record} :
    (returned saved reached selected).Registered record ↔ reached.Registered record := by
  constructor
  · intro registered
    obtain ⟨row, member⟩ := registered
    refine ⟨row, ?_⟩
    change record ∈ records (returned saved reached selected) row at member
    change record ∈ records reached row
    rw [← returned_records saved reached selected]
    exact member
  · intro registered
    obtain ⟨row, member⟩ := registered
    refine ⟨row, ?_⟩
    change record ∈ records reached row at member
    change record ∈ records (returned saved reached selected) row
    rw [returned_records saved reached selected]
    exact member

theorem returned_related : Relates reached (returned saved reached selected) :=
  Relates.of_records_eq (returned_records saved reached selected)

theorem returned_from_saved (related : Relates saved reached) :
    Relates saved (returned saved reached selected) :=
  related.trans (returned_related saved reached selected)

theorem returned_same_frame (row : Fin keys.length)
    (same : keys[row.val].frameLocation = keys[selected.val].frameLocation) :
    ((returned saved reached selected).rows row).authority.current = (saved.rows selected).authority.current ∧
    ((returned saved reached selected).rows row).authority.ghost = (saved.rows selected).authority.ghost :=
  CallableIndexedOwnedFunctionState.restored_same_frame saved reached selected row same

theorem returned_other_frame (row : Fin keys.length)
    (different : keys[row.val].frameLocation ≠ keys[selected.val].frameLocation) :
    ((returned saved reached selected).rows row).authority.current = (reached.rows row).authority.current ∧
    ((returned saved reached selected).rows row).authority.ghost = (reached.rows row).authority.ghost :=
  CallableIndexedOwnedFunctionState.restored_other_frame saved reached selected row different

theorem returned_snapshot (row : Fin keys.length) {record : CallableIndexedSnapshots.Record}
    (member : record ∈ records reached row) :
    CallableIndexedSnapshots.Holds compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table
      compiled.indexed.ancestry.layout.frame body.mapping (finalIndex (body := body) saved selected).store record :=
  CallableIndexedOwnedFunctionState.restored_snapshot saved reached selected row member

theorem returned_capture_read (row : Fin keys.length)
    {header : CallableIndexedOwnedFunctionValues.Header compiled program} (member : header ∈ headers)
    (capture : RecursiveNamedCatalog.Capture (prepared := compiled.indexed.ancestry)
      (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      headers keys[row.val].locations keys[row.val].capturePrefix (reached.rows row).authority.frameLocation
      header body.mapping body.world body.heap body.store) :
    (finalIndex (body := body) saved selected).store.read? (keys[row.val].locations header) = some (.inRight .unit
      (.closure header.named.signature.parameterType (LanguageResult.resultType header.named.signature.resultType)
        (header.code.rename capture.embedding.lift) capture.captured)) :=
  CallableIndexedOwnedFunctionState.restored_capture_read saved reached selected row member capture

/-- The one actual restore producer retains the completed body's full heap,
records and captures. Its related receipt comes from the actual invocation
chain; administrative effects alone do not supply that receipt. -/
theorem restore_return {next : NativeFrame}
    {functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed)}
    {registry : SourceCoreRawMetadata.Registry}
    (registered : compiled.indexed.ancestry.layout.frame.Registered compiled.indexed.layouts.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions
      body.mapping body.world body.heap body.store)
    (worlds : WorldExtends caller.world body.world)
    (frame : AdministrativePreserved caller.mapping
      (caller.store.set keys[selected.val].frameLocation (encode compiled.indexed.ancestry.layout.frame next))
      body.mapping body.store)
    (related : Relates saved reached) :
    CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions
      body.mapping body.world body.heap (finalIndex (body := body) saved selected).store ∧
    AdministrativePreserved caller.mapping caller.store body.mapping (finalIndex (body := body) saved selected).store ∧
    CellState compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table
      compiled.indexed.ancestry.layout.frame keys[selected.val].frameLocation
      (saved.rows selected).authority.current (saved.rows selected).authority.ghost (finalIndex (body := body) saved selected).store ∧
    Relates reached (returned saved reached selected) ∧
    Relates saved (returned saved reached selected) ∧
    records (returned saved reached selected) = records reached ∧
    ProtectedStateTransition.Transition (protocol headers keys) saved (finalIndex (body := body) saved selected) := by
  obtain ⟨final, same, finalHeaps, finalFrame, finalCell, _related, _records⟩ :=
    CallableIndexedOwnedFunctionState.restore_reached saved reached selected registered heaps worlds frame
  exact ⟨finalHeaps, finalFrame, finalCell, returned_related saved reached selected,
    returned_from_saved saved reached selected related, returned_records saved reached selected,
    returned saved reached selected, returned_from_saved saved reached selected related⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedBodyRestoration
