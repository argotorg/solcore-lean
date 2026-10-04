import Solcore.SourceSemantics.CoreLowering.CallableIndexedAuthorityPool

/-! Formal protocol consumers. No body grammar or indirect-call semantics is
asserted here; registered snapshots are the exact retained record domain. -/
set_option autoImplicit false
namespace Solcore.Test.SourceCoreCallableIndexedAuthorityPool
open Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open GeneralHeap ReadOnly CompatiblePayload CallableAncestryPairedLookup
open RecursiveNamedCatalog CallableIndexedHistory SourceCoreCallableIndexedFrames
open CallableIndexedAuthorityPool

variable {checked : Checked} {base : Base checked}
  {prepared : SourceCoreCallableIndexedAncestry.Prepared base} {values : ValuesContext}
  {ambient : AmbientDefinitions values.checked.catalog.definitions} {program : SourceSemantics.Program}
  {headers : Inventory prepared values ambient.definitions program}
  {keys : List (Key prepared values ambient.definitions program)}
  {key otherKey : Key prepared values ambient.definitions program}
  {mapping : LocationMap} {world : StoreTyping} {heap : Dynamic.Heap} {store : Store}

/-- Real prepared recipe, exact original heap and catalogue entry. -/
abbrev actual_initial_pool := @CallableIndexedAuthorityPool.initial_entry

/-- Actual allocator receipts produce the exact three-cell append and its
record registration; no final separation law is supplied. -/
abbrev actual_snapshot_registration := @Pool.completed_snapshot

/-- The actual fresh allocator and full initialized entry close registration. -/
abbrev actual_fresh_frame_registration := @Pool.register_fresh_frame
abbrev actual_fresh_frame_history := @fresh_frame_state

/-- The concrete native allocator initializes an empty frame at its exact
fresh location. A decoder is not part of this construction. -/
theorem actual_empty_frame_append :
    CellState prepared.graph.inputs prepared.graph.table prepared.layout.frame store.length .empty .empty
      (store ++ [encode prepared.layout.frame .empty]) :=
  fresh_frame_state (.stable .empty) rfl

/-- Registration consumes that actual one-cell append and an independently
initialized complete catalogue; its cross-separation is proved internally. -/
def actual_fresh_empty_registration (pool : Pool headers keys mapping world heap store)
    {futureWorld : StoreTyping} (worlds : WorldExtends world futureWorld)
    (entry : EntryValid headers key mapping futureWorld heap (store ++ [encode prepared.layout.frame .empty]))
    (fresh : key.frameLocation = store.length)
    (records : ∀ record ∈ entry.authority.records, pool.Registered record) :
    Pool headers (keys ++ [key]) mapping futureWorld heap (store ++ [encode prepared.layout.frame .empty]) :=
  pool.register_fresh_frame rfl worlds entry fresh records

/-- Restoration promises the original key domain, keeping final body effects. -/
abbrev actual_original_pool_restore := @Pool.restore

/-- The exact code and every original captured value survive the real write. -/
abbrev full_capture_after_write := @Pool.install_capture_read

def duplicate_key (pool : Pool headers keys mapping world heap store) (i : Fin keys.length) :
    Pool headers (keys ++ [keys[i.val]]) mapping world heap store := pool.duplicate i

theorem shared_frame_update (pool : Pool headers keys mapping world heap store)
    (i j : Fin keys.length) (same : keys[j.val].frameLocation = keys[i.val].frameLocation)
    {next : NativeFrame} {ghost : GhostFrame}
    (history : Current prepared.graph.inputs prepared.graph.table next ghost) :
    ((pool.install i history).rows i).authority.current = next ∧
    ((pool.install i history).rows j).authority.current = next := by
  constructor <;> rw [Pool.install_current] <;> simp [same]

theorem other_frame_keeps_history (pool : Pool headers keys mapping world heap store)
    (i j : Fin keys.length) (different : keys[j.val].frameLocation ≠ keys[i.val].frameLocation)
    {next : NativeFrame} {ghost : GhostFrame}
    (history : Current prepared.graph.inputs prepared.graph.table next ghost) :
    ((pool.install i history).rows j).authority.current = (pool.rows j).authority.current ∧
    ((pool.install i history).rows j).authority.ghost = (pool.rows j).authority.ghost ∧
    ((pool.install i history).rows j).authority.records = (pool.rows j).authority.records := by
  exact ⟨by rw [Pool.install_current]; simp [different],
    by rw [Pool.install_ghost]; simp [different], pool.install_records i j history⟩

theorem different_catalogue_global (left : EntryValid headers key mapping world heap store)
    (right : EntryValid headers otherKey mapping world heap store)
    {header : Header prepared values ambient.definitions program} (member : header ∈ headers) :
    key.locations header ≠ otherKey.frameLocation := left.global_ne_frame right member

theorem old_record_protected_after_install (pool : Pool headers keys mapping world heap store)
    (i selected : Fin keys.length) (record : CallableIndexedSnapshots.Record)
    (member : record ∈ (pool.rows i).authority.records)
    {next : NativeFrame} {ghost : GhostFrame}
    (history : Current prepared.graph.inputs prepared.graph.table next ghost) :
    CallableIndexedSnapshots.Holds prepared.graph.inputs prepared.graph.table prepared.layout.frame mapping
      (store.set keys[selected.val].frameLocation (encode prepared.layout.frame next)) record :=
  ((pool.install selected history).rows i).authority.snapshots record (by simpa only [Pool.install_records] using member)

section CrossBoundary
/-- Two different physical cells, both with actual initialized empty frames. -/
def keyAt (location : Location) : Key prepared values ambient.definitions program :=
  ⟨fun _ => 7, 0, location⟩

def twoStore : Store := [encode prepared.layout.frame .empty, encode prepared.layout.frame .empty]
def twoWorld : StoreTyping := [prepared.layout.frame.type, prepared.layout.frame.type]
def snapshotAt (location : Location) : CallableIndexedSnapshots.Record := ⟨location, .empty, .empty, none⟩

/-- Each individual authority can have self-distinct records while its
snapshot is the other authority's mutable frame. The cross invariant is real. -/
def firstAuthority : Authority ([] : Inventory prepared values ambient.definitions program)
    (keyAt (prepared := prepared) (values := values) (ambient := ambient) (program := program) 0).locations
    0 [] (twoWorld (prepared := prepared)) ⟨[]⟩ (twoStore (prepared := prepared)) where
  frameLocation := 0
  unmapped := by simp
  typed := rfl
  current := .empty
  ghost := .empty
  frame := ⟨rfl, .stable .empty⟩
  records := [snapshotAt 1]
  snapshots := by
    intro record member
    have same := List.mem_singleton.mp member; subst record
    exact ⟨rfl, by simp, .empty⟩
  distinct := by
    intro record member
    have same := List.mem_singleton.mp member; subst record
    decide
  captures := by intro header member; simp at member

def secondAuthority : Authority ([] : Inventory prepared values ambient.definitions program)
    (keyAt (prepared := prepared) (values := values) (ambient := ambient) (program := program) 1).locations
    0 [] (twoWorld (prepared := prepared)) ⟨[]⟩ (twoStore (prepared := prepared)) where
  frameLocation := 1
  unmapped := by simp
  typed := rfl
  current := .empty
  ghost := .empty
  frame := ⟨rfl, .stable .empty⟩
  records := [snapshotAt 0]
  snapshots := by
    intro record member
    have same := List.mem_singleton.mp member; subst record
    exact ⟨rfl, by simp, .empty⟩
  distinct := by
    intro record member
    have same := List.mem_singleton.mp member; subst record
    decide
  captures := by intro header member; simp at member

theorem self_distinct_does_not_supply_cross :
    ¬ ∃ pool : Pool ([] : Inventory prepared values ambient.definitions program)
        [keyAt 0, keyAt 1] [] (twoWorld (prepared := prepared)) ⟨[]⟩ (twoStore (prepared := prepared)),
      (pool.rows 0).authority.records = [snapshotAt 1] := by
  rintro ⟨pool, records⟩
  have member : snapshotAt 1 ∈ (pool.rows 0).authority.records := by rw [records]; exact List.mem_singleton_self _
  have impossible := pool.separated 0 1 (snapshotAt 1) member
  exact impossible rfl

/-- Duplicating the actual first authority is valid: both rows share frame 0
and the retained snapshot at 1 remains separated from both rows. -/
def concrete_duplicate :
    Pool ([] : Inventory prepared values ambient.definitions program)
      [keyAt 0, keyAt 0] [] (twoWorld (prepared := prepared)) ⟨[]⟩ (twoStore (prepared := prepared)) :=
  (Pool.singleton (EntryValid.of_authority (firstAuthority (prepared := prepared) (values := values)
    (ambient := ambient) (program := program)))).duplicate 0

theorem concrete_frames_different :
    (firstAuthority (prepared := prepared) (values := values) (ambient := ambient) (program := program)).frameLocation ≠
      (secondAuthority (prepared := prepared) (values := values) (ambient := ambient) (program := program)).frameLocation := by change (0 : Nat) ≠ 1; decide
end CrossBoundary

end Solcore.Test.SourceCoreCallableIndexedAuthorityPool
