import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedBodyRestoration
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedSourceAdmission

/-! The actual body post survives restoration of the saved caller cell.
Successful Source typing moves only along a genuine context-support receipt;
faults retain every row's stable history without a deep heap typing claim. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedBodyRestorationAdmission
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedHistory SourceCoreCallableIndexedFrames
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedIndirectExpressionHeads (StableRows)

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {caller body : ProtectedStateTransition.Index}

/-- This carrier observes the actual owned pool before and after restoration. -/
def bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers)
    (fun _ => True) (protocol headers keys) :=
  CallableIndexedOwnedIndirectCallerProtocol.of_legacy CallableIndexedOwnedCallerProtocol.base

/-- Saved stable reads and the actual restored frame authenticate every
returned row against that row's own current ghost. -/
theorem restore_rows (saved : State headers keys caller) (reached : State headers keys body)
    (selected : Fin keys.length) (savedRows : StableRows saved)
    (restoredFrame : AdministrativePreserved caller.mapping caller.store body.mapping
      (CallableIndexedOwnedBodyRestoration.finalIndex (body := body) saved selected).store) :
    StableRows (CallableIndexedOwnedBodyRestoration.returned saved reached selected) :=
  StableRows.after_administrative saved
    (CallableIndexedOwnedBodyRestoration.returned saved reached selected) savedRows restoredFrame

/-- A genuine fault post retains rows without requiring value or heap typing,
or a relation between the body and caller's static type contexts. -/
theorem restore_fault_post (saved : State headers keys caller) (reached : State headers keys body)
    (selected : Fin keys.length) {context : SourceSemantics.Context} {type : TypeSystem.Ty}
    {reason : Dynamic.SemanticFault} (savedRows : StableRows saved)
    (restoredFrame : AdministrativePreserved caller.mapping caller.store body.mapping
      (CallableIndexedOwnedBodyRestoration.finalIndex (body := body) saved selected).store) :
    PostAdmission bridge context type (.fault reason)
      (CallableIndexedOwnedBodyRestoration.returned saved reached selected) := by
  refine ⟨restore_rows saved reached selected savedRows restoredFrame, ?_⟩
  intro value same
  cases same

/-- Restoration keeps the body's raw heap and the returned pool's own ghosts.
The saved caller's stable reads authenticate all of those restored rows. -/
theorem restore_post (saved : State headers keys caller) (reached : State headers keys body)
    (selected : Fin keys.length) {bodyContext callerContext : SourceSemantics.Context}
    {type : TypeSystem.Ty} {outcome : Dynamic.ExpressionOutcome}
    (savedRows : StableRows saved)
    (post : PostAdmission bridge bodyContext type outcome reached)
    (supports : Dynamic.TypeContextSupports bodyContext callerContext)
    (restoredFrame : AdministrativePreserved caller.mapping caller.store body.mapping
      (CallableIndexedOwnedBodyRestoration.finalIndex (body := body) saved selected).store) :
    PostAdmission bridge callerContext type outcome
      (CallableIndexedOwnedBodyRestoration.returned saved reached selected) := by
  refine ⟨restore_rows saved reached selected savedRows restoredFrame, ?_⟩
  intro value same
  obtain ⟨valueTyped, heapTyped⟩ := post.successful value same
  exact ⟨valueTyped.transportContext supports, heapTyped.transportContext supports⟩

/-- The original restore producer runs once and retains its complete tuple.
The added post describes that same returned state and unchanged Source heap. -/
theorem restore_return_with_post (saved : State headers keys caller)
    (reached : State headers keys body) (selected : Fin keys.length) {next : NativeFrame}
    {functions : FunctionModel compiled.compatible.checked.catalog
      (CallableIndexedAmbient.ambientDefinitions compiled.indexed)}
    {registry : SourceCoreRawMetadata.Registry}
    {bodyContext callerContext : SourceSemantics.Context} {type : TypeSystem.Ty}
    {outcome : Dynamic.ExpressionOutcome}
    (registered : compiled.indexed.ancestry.layout.frame.Registered compiled.indexed.layouts.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions
      body.mapping body.world body.heap body.store)
    (worlds : WorldExtends caller.world body.world)
    (frame : AdministrativePreserved caller.mapping
      (caller.store.set keys[selected.val].frameLocation (encode compiled.indexed.ancestry.layout.frame next))
      body.mapping body.store)
    (related : Relates saved reached) (savedRows : StableRows saved)
    (post : PostAdmission bridge bodyContext type outcome reached)
    (supports : Dynamic.TypeContextSupports bodyContext callerContext) :
    CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions
      body.mapping body.world body.heap
      (CallableIndexedOwnedBodyRestoration.finalIndex (body := body) saved selected).store ∧
    AdministrativePreserved caller.mapping caller.store body.mapping
      (CallableIndexedOwnedBodyRestoration.finalIndex (body := body) saved selected).store ∧
    CellState compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table
      compiled.indexed.ancestry.layout.frame keys[selected.val].frameLocation
      (saved.rows selected).authority.current (saved.rows selected).authority.ghost
      (CallableIndexedOwnedBodyRestoration.finalIndex (body := body) saved selected).store ∧
    Relates reached (CallableIndexedOwnedBodyRestoration.returned saved reached selected) ∧
    Relates saved (CallableIndexedOwnedBodyRestoration.returned saved reached selected) ∧
    records (CallableIndexedOwnedBodyRestoration.returned saved reached selected) = records reached ∧
    ProtectedStateTransition.Transition (protocol headers keys) saved
      (CallableIndexedOwnedBodyRestoration.finalIndex (body := body) saved selected) ∧
    PostAdmission bridge callerContext type outcome
      (CallableIndexedOwnedBodyRestoration.returned saved reached selected) := by
  obtain ⟨finalHeaps, finalFrame, finalCell, fromBody, fromSaved, sameRecords, transition⟩ :=
    CallableIndexedOwnedBodyRestoration.restore_return saved reached selected registered heaps worlds frame related
  exact ⟨finalHeaps, finalFrame, finalCell, fromBody, fromSaved, sameRecords, transition,
    restore_post saved reached selected savedRows post supports finalFrame⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedBodyRestorationAdmission
