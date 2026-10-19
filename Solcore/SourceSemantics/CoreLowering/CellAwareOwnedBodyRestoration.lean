import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedBodyRestoration
import Solcore.SourceSemantics.CoreLowering.CellAwareBodyFrames
import Solcore.SourceSemantics.CoreLowering.CellAwareScopeAuthority

/-! The same reached owned pool returns through its saved physical caller
while ordinary and generalized Source cells retain their respective relations. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareOwnedBodyRestoration
open Core Frontend GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedHistory SourceCoreCallableIndexedFrames CallableIndexedOwnedFunctionState
open CallableIndexedOwnedBodyRestoration

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {caller body : ProtectedStateTransition.Index}
  (saved : State headers keys caller) (reached : State headers keys body) (selected : Fin keys.length)
  {cells : GenericHeap.CellModel compiled.indexed.layouts.definitions}

/-- Actual frame restoration uses the selected saved row, preserving every
record produced by the body and the exact completed Source heap. -/
theorem restore_return {next : NativeFrame}
    (heaps : GenericHeap.CellHeapRepresents cells body.mapping body.world body.heap body.store)
    (worlds : WorldExtends caller.world body.world)
    (frame : AdministrativePreserved caller.mapping
      (caller.store.set keys[selected.val].frameLocation (encode compiled.indexed.ancestry.layout.frame next))
      body.mapping body.store)
    (related : Relates saved reached) :
    GenericHeap.CellHeapRepresents cells body.mapping body.world body.heap
      (finalIndex (body := body) saved selected).store ∧
    AdministrativePreserved caller.mapping caller.store body.mapping
      (finalIndex (body := body) saved selected).store ∧
    CellState compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table
      compiled.indexed.ancestry.layout.frame keys[selected.val].frameLocation
      (saved.rows selected).authority.current (saved.rows selected).authority.ghost
      (finalIndex (body := body) saved selected).store ∧
    Relates saved (returned saved reached selected) := by
  let row := saved.rows selected
  obtain ⟨finalHeaps, finalFrame, finalCell⟩ := CellAwareBodyFrames.restore (next := next)
    (CallableIndexedAmbient.frame_registered compiled.indexed) row.authority.unmapped row.authority.typed
    row.authority.frame heaps worlds (by simp only [row.frame_eq]; exact frame)
  rw [row.frame_eq] at finalHeaps finalFrame finalCell
  exact ⟨finalHeaps, finalFrame, finalCell, returned_from_saved saved reached selected related⟩

include reached in
/-- Descriptor payloads survive the concrete restore write; administrative
preservation alone is not used to claim equality of mapped Source cells. -/
theorem restored_effect
    (instances : GeneralizedLocalDescriptorHeap.InstanceModel compiled.indexed.layouts.definitions)
    (effect : CellAwareScopeAuthority.Effect instances caller.mapping caller.world caller.heap caller.store
      body.mapping body.world body.heap body.store) :
    CellAwareScopeAuthority.Effect instances caller.mapping caller.world caller.heap caller.store
      body.mapping body.world body.heap (finalIndex (body := body) saved selected).store := by
  have unmapped : keys[selected.val].frameLocation ∉ body.mapping := by
    have absent := (reached.rows selected).authority.unmapped
    simp only [(reached.rows selected).frame_eq] at absent
    exact absent
  exact effect.trans (.set_unmapped body.store
    (encode compiled.indexed.ancestry.layout.frame (saved.rows selected).authority.current) unmapped)

end Solcore.SourceSemantics.CoreLowering.CellAwareOwnedBodyRestoration
