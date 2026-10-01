import Solcore.SourceSemantics.CoreLowering.CallableIndexedAllocation
import Solcore.SourceSemantics.CoreLowering.GeneralHeapFrame

/-! Source allocation snapshots are protected administrative locations.
Persistence uses an explicit semantic store frame, not native typing alone.
The completed-source frame already used by general heap correspondence supplies
that contract; temporary context/global writes require a distinct location. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedSnapshots
open Core Frontend CallableAncestryPairedLookup CallableIndexedHistory GeneralHeap

structure Record where
  location : Location
  native : NativeFrame
  ghost : GhostFrame
  metadata : Option MetadataState

structure Holds {checked : Checked} {base : Base checked} (inputs : Inputs base) (table : Table)
    (layout : SourceCoreCallableIndexedFrames.Layout) (mapping : LocationMap) (store : Store) (record : Record) : Prop where
  read : store.read? record.location = some (SourceCoreCallableIndexedFrames.encode layout record.native)
  administrative : record.location ∉ mapping
  history : Carries inputs table record.native record.ghost record.metadata

/-- Completed source correspondence preserves existing snapshot locations and
keeps them outside the future source-location map. -/
theorem Holds.transport {checked : Checked} {base : Base checked} {inputs : Inputs base} {table : Table}
    {layout : SourceCoreCallableIndexedFrames.Layout} {mapping futureMapping : LocationMap} {before after : Store} {record : Record}
    (snapshot : Holds inputs table layout mapping before record)
    (frame : AdministrativePreserved mapping before futureMapping after) :
    Holds inputs table layout futureMapping after record := by
  obtain ⟨unmapped, preserved⟩ := frame record.location snapshot.administrative
    (List.getElem?_eq_some_iff.mp snapshot.read).1
  exact ⟨preserved.trans snapshot.read, unmapped, snapshot.history⟩

theorem Holds.append {checked : Checked} {base : Base checked} {inputs : Inputs base} {table : Table}
    {layout : SourceCoreCallableIndexedFrames.Layout} {mapping : LocationMap} {before : Store} {record : Record}
    (snapshot : Holds inputs table layout mapping before record) (suffix : Store) :
    Holds inputs table layout mapping (before ++ suffix) record := by
  refine ⟨?_, snapshot.administrative, snapshot.history⟩
  simpa only [Store.read?, List.getElem?_append_left (List.getElem?_eq_some_iff.mp snapshot.read).1] using snapshot.read

/-- Source writes address mapped payload locations and cannot target this
snapshot. The actual write receipt supplies the store equality. -/
theorem Holds.source_write {checked : Checked} {base : Base checked} {inputs : Inputs base} {table : Table}
    {layout : SourceCoreCallableIndexedFrames.Layout} {mapping : LocationMap} {before after : Store} {record : Record}
    (snapshot : Holds inputs table layout mapping before record) {location : Location} {value : Value}
    (mapped : location ∈ mapping) (written : before.write? location value = some after) :
    Holds inputs table layout mapping after record :=
  snapshot.transport (AdministrativePreserved.write mapped written)

/-- Mutable context or helper cells need a separate location receipt. Their
native element type is not used to infer separation from snapshot cells. -/
theorem Holds.other_write {checked : Checked} {base : Base checked} {inputs : Inputs base} {table : Table}
    {layout : SourceCoreCallableIndexedFrames.Layout} {mapping : LocationMap} {before after : Store} {record : Record}
    (snapshot : Holds inputs table layout mapping before record) {location : Location} {value : Value}
    (different : record.location ≠ location) (written : before.write? location value = some after) :
    Holds inputs table layout mapping after record :=
  ⟨(Store.write?_preserves_other written different).trans snapshot.read, snapshot.administrative, snapshot.history⟩

/-- Fresh helper references are disjoint from every snapshot already present
in the original store, even after that store receives additional cells. -/
theorem Holds.fresh_write {checked : Checked} {base : Base checked} {inputs : Inputs base} {table : Table}
    {layout : SourceCoreCallableIndexedFrames.Layout} {mapping : LocationMap} {before after : Store} {record : Record}
    (snapshot : Holds inputs table layout mapping before record) {suffix : Store} {offset : Nat} {value : Value}
    (written : (before ++ suffix).write? (before.length + offset) value = some after) :
    Holds inputs table layout mapping after record := by
  apply (snapshot.append suffix).other_write _ written
  have bound := (List.getElem?_eq_some_iff.mp snapshot.read).1
  exact Nat.ne_of_lt (Nat.lt_of_lt_of_le bound (Nat.le_add_right _ _))

/-- The map extension for a completed marker/payload pair cannot capture the
preceding administrative snapshot index. The initial map must already refer
to actual cells in the initial store. -/
theorem completed {checked : Checked} {base : Base checked} {inputs : Inputs base} {table : Table}
    {layout : SourceCoreCallableIndexedFrames.Layout} {mapping : LocationMap} {before : Store}
    {native : NativeFrame} {ghost : GhostFrame} {metadata : Option MetadataState}
    (history : Carries inputs table native ghost metadata)
    (bounded : ∀ location ∈ mapping, location < before.length) (marker payload : Value) :
    Holds inputs table layout (mapping ++ [before.length + 2])
      (before ++ [SourceCoreCallableIndexedFrames.encode layout native, marker, payload])
      ⟨before.length, native, ghost, metadata⟩ := by
  refine ⟨by simp [Store.read?], ?_, history⟩
  simp only [List.mem_append, List.mem_singleton, not_or]
  exact ⟨fun member => Nat.lt_irrefl _ (bounded _ member), by change before.length ≠ before.length + 2; omega⟩

def All {checked : Checked} {base : Base checked} (inputs : Inputs base) (table : Table)
    (layout : SourceCoreCallableIndexedFrames.Layout) (mapping : LocationMap) (store : Store) (records : List Record) : Prop :=
  ∀ record ∈ records, Holds inputs table layout mapping store record

theorem All.transport {checked : Checked} {base : Base checked} {inputs : Inputs base} {table : Table}
    {layout : SourceCoreCallableIndexedFrames.Layout} {mapping futureMapping : LocationMap} {before after : Store} {records : List Record}
    (snapshots : All inputs table layout mapping before records)
    (frame : AdministrativePreserved mapping before futureMapping after) :
    All inputs table layout futureMapping after records :=
  fun record member => (snapshots record member).transport frame

end Solcore.SourceSemantics.CoreLowering.CallableIndexedSnapshots
