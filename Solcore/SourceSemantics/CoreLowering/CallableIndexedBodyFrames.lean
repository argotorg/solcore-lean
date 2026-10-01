import Solcore.SourceSemantics.CoreLowering.CallableIndexedSnapshots
import Solcore.SourceSemantics.CoreLowering.GenericHeap

/-! Heap correspondence across the temporary callable-context write. The
context cell is source-unmapped and has a registered native frame type. A child
semantic frame is applied to the installed store; restoring the caller then
recovers preservation of every original administrative location. This uses a
semantic child contract, not a claim that arbitrary typed code avoids writes. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedBodyFrames
open Core Frontend GeneralHeap CallableAncestryPairedLookup CallableIndexedHistory
open SourceCoreCallableIndexedFrames

variable {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
  {model : GenericHeap.PayloadModel catalog projects}

/-- Installing a related callable frame changes no represented source cell.
The new native carrier is typed by its registered definition independently of
the metadata-history witness carried alongside it. -/
theorem install {checked : Checked} {base : Base checked} {inputs : Inputs base} {table : Table}
    {layout : Layout} {mapping : LocationMap} {world : StoreTyping}
    {heap : Dynamic.Heap} {store : Store} {location : Location}
    {current next : NativeFrame} {currentGhost nextGhost : GhostFrame}
    (registered : layout.Registered catalog.definitions)
    (heaps : GenericHeap.HeapRepresents model mapping world heap store)
    (unmapped : location ∉ mapping) (typed : world[location]? = some layout.type)
    (caller : CellState inputs table layout location current currentGhost store)
    (nextHistory : Current inputs table next nextGhost) :
    GenericHeap.HeapRepresents model mapping world heap (store.set location (encode layout next)) ∧
      CellState inputs table layout location next nextGhost (store.set location (encode layout next)) := by
  have written : store.write? location (encode layout next) = some (store.set location (encode layout next)) :=
    Store.write?_eq_some_iff.mpr ⟨(List.getElem?_eq_some_iff.mp caller.read).1, rfl⟩
  exact ⟨heaps.write_administrative (fun found => unmapped (List.mem_of_getElem? found)) typed
    (encode_runtime_typed world registered next) written, ⟨Store.write?_reads_written written, nextHistory⟩⟩

/-- A completed nested source body keeps the installed current token. Its
history is carried from entry and its value is preserved by the semantic frame. -/
theorem body_current {checked : Checked} {base : Base checked} {inputs : Inputs base} {table : Table}
    {layout : Layout} {mapping finalMap : LocationMap} {before after : Store} {location : Location}
    {native : NativeFrame} {ghost : GhostFrame}
    (unmapped : location ∉ mapping)
    (current : CellState inputs table layout location native ghost before)
    (frame : AdministrativePreserved mapping before finalMap after) :
    CellState inputs table layout location native ghost after := by
  have unchanged := (frame location unmapped (List.getElem?_eq_some_iff.mp current.read).1).2
  exact ⟨unchanged.trans current.read, current.history⟩

/-- The completed child semantic frame prevents the context cell from becoming
a source alias. Restoration preserves the represented final heap and recovers
the original caller token and the complete original administrative frame. -/
theorem restore {checked : Checked} {base : Base checked} {inputs : Inputs base} {table : Table}
    {layout : Layout} {mapping finalMap : LocationMap} {world finalWorld : StoreTyping}
    {after : Dynamic.Heap} {before bodyStore : Store} {location : Location}
    {current next : NativeFrame} {currentGhost : GhostFrame}
    (registered : layout.Registered catalog.definitions)
    (unmapped : location ∉ mapping) (typed : world[location]? = some layout.type)
    (caller : CellState inputs table layout location current currentGhost before)
    (heaps : GenericHeap.HeapRepresents model finalMap finalWorld after bodyStore)
    (worlds : WorldExtends world finalWorld)
    (frame : AdministrativePreserved mapping (before.set location (encode layout next)) finalMap bodyStore) :
    GenericHeap.HeapRepresents model finalMap finalWorld after (bodyStore.set location (encode layout current)) ∧
      AdministrativePreserved mapping before finalMap (bodyStore.set location (encode layout current)) ∧
      CellState inputs table layout location current currentGhost (bodyStore.set location (encode layout current)) := by
  have bound := (List.getElem?_eq_some_iff.mp caller.read).1
  have installed : before.write? location (encode layout next) = some (before.set location (encode layout next)) :=
    Store.write?_eq_some_iff.mpr ⟨bound, rfl⟩
  have finalTyped := worlds.lookup typed
  have written : bodyStore.write? location (encode layout current) = some (bodyStore.set location (encode layout current)) :=
    Store.write?_eq_some_iff.mpr ⟨heaps.runtime_hasTypes.location_lt finalTyped, rfl⟩
  have finalUnmapped := (frame location unmapped (by simpa using bound)).1
  refine ⟨heaps.write_administrative (fun found => finalUnmapped (List.mem_of_getElem? found)) finalTyped
    (encode_runtime_typed finalWorld registered current) written, ?_,
    ⟨Store.write?_reads_written written, caller.history⟩⟩
  intro other absent oldBound
  obtain ⟨stillAbsent, unchanged⟩ := frame other absent (by simpa using oldBound)
  refine ⟨stillAbsent, ?_⟩
  by_cases same : other = location
  · subst other
    exact (Store.write?_reads_written written).trans caller.read.symm
  · exact (Store.write?_preserves_other written same).trans
      (unchanged.trans (Store.write?_preserves_other installed same))

/-- Protected snapshots remain valid while the temporary context is installed
when their actual locations are distinct. Full closure environments may still
retain unused references; this is a store contract over selected locations. -/
theorem install_snapshots {checked : Checked} {base : Base checked} {inputs : Inputs base} {table : Table}
    {layout : Layout} {mapping : LocationMap} {store : Store} {location : Location}
    {current next : NativeFrame} {currentGhost : GhostFrame} {records : List CallableIndexedSnapshots.Record}
    (caller : CellState inputs table layout location current currentGhost store)
    (snapshots : CallableIndexedSnapshots.All inputs table layout mapping store records)
    (distinct : ∀ record ∈ records, record.location ≠ location) :
    CallableIndexedSnapshots.All inputs table layout mapping (store.set location (encode layout next)) records := by
  intro record member
  exact (snapshots record member).other_write (distinct record member)
    (Store.write?_eq_some_iff.mpr ⟨(List.getElem?_eq_some_iff.mp caller.read).1, rfl⟩)

end Solcore.SourceSemantics.CoreLowering.CallableIndexedBodyFrames
