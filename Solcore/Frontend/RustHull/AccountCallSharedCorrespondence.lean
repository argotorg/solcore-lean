import Solcore.Frontend.RustHull.AccountCallTransferCorrespondence
import Solcore.Frontend.RustHull.RuntimeLinkedWorldCorrespondence

/-! A child may change all four shared resources. The caller's other cells and
catalog identities survive dispatch, including restoration after a failed child. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.AccountCallCorrespondence
open Core Correspondence ScalarExecution CodeBuilder

def SharedLocations.mutable (locations : SharedLocations) : List Nat :=
  [locations.world, locations.logs, locations.logSize, locations.balances]

structure SharedFrame (locations : SharedLocations) (initial final : Core.Store) : Prop where
  length_le : initial.length ≤ final.length
  read : ∀ location value, location ∉ locations.mutable →
    initial.read? location = some value → final.read? location = some value

theorem SharedFrame.refl (locations : SharedLocations) (store : Core.Store) : SharedFrame locations store store :=
  ⟨Nat.le_refl _, fun _ _ _ found => found⟩

theorem SharedFrame.trans {locations : SharedLocations} {initial middle final : Core.Store}
    (first : SharedFrame locations initial middle) (second : SharedFrame locations middle final) :
    SharedFrame locations initial final :=
  ⟨Nat.le_trans first.length_le second.length_le,
    fun index value outside found => second.read index value outside (first.read index value outside found)⟩

theorem SharedFrame.ofRetains {locations : SharedLocations} {initial final : Core.Store}
    (retained : StoreRetains initial final) : SharedFrame locations initial final :=
  ⟨retained.length_le, fun _ _ _ found => retained_read retained found⟩

theorem SharedFrame.ofBalance {locations : SharedLocations} {initial final : Core.Store}
    (frame : BalanceFrame locations.balances initial final) : SharedFrame locations initial final := by
  refine ⟨frame.length_le, ?_⟩
  intro index value outside found
  exact (frame.other index (fun same => outside (by simp [SharedLocations.mutable, same]))
    (List.getElem?_eq_some_iff.mp found).1).trans found

theorem SharedFrame.write {locations : SharedLocations} {location : Nat}
    (member : location ∈ locations.mutable) (store : Core.Store) (value : Core.Value) :
    SharedFrame locations store (store.set location value) := by
  refine ⟨by simp, ?_⟩
  intro index old outside found
  have different : location ≠ index := fun same => outside (same ▸ member)
  exact (List.getElem?_set_ne different).trans found

structure LinkedSharedStateRel (anchors : List CatalogWorldCorrespondence.Anchor)
    (locations : SharedLocations) (state : AccountCallSemantics.Shared) (store : Core.Store) : Prop where
  shared : SharedStateRel locations state store
  linked : RuntimeLinkedWorldCorrespondence.StateRel anchors state.world locations.world store

theorem LinkedSharedStateRel.retained {anchors : List CatalogWorldCorrespondence.Anchor}
    {locations : SharedLocations} {state : AccountCallSemantics.Shared} {initial final : Core.Store}
    (related : LinkedSharedStateRel anchors locations state initial) (retained : StoreRetains initial final) :
    LinkedSharedStateRel anchors locations state final :=
  ⟨related.shared.retained retained, related.linked.retained retained⟩

theorem LinkedSharedStateRel.balances_updated {anchors : List CatalogWorldCorrespondence.Anchor}
    {locations : SharedLocations} {state : AccountCallSemantics.Shared} {initial final : Core.Store}
    {balances : StorageSemantics.Words} (related : LinkedSharedStateRel anchors locations state initial)
    (frame : BalanceFrame locations.balances initial final)
    (read : final.read? locations.balances = some (WordMapping.encode balances)) :
    LinkedSharedStateRel anchors locations {state with balances := balances} final := by
  refine ⟨related.shared.balances_updated frame read, related.linked.read_preserved ?_⟩
  intro value found
  have distinct := related.shared.distinct
  simp only [SharedLocations.all, List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
    not_or, List.nodup_nil, and_true] at distinct
  exact (frame.other locations.world distinct.1.2.2.1 (List.getElem?_eq_some_iff.mp found).1).trans found

def checkpointStore (locations : SharedLocations) (world logs logSize balances : Core.Value)
    (store : Core.Store) : Core.Store :=
  (((store.set locations.balances balances).set locations.logSize logSize).set locations.logs logs).set locations.world world

theorem checkpointStore_frame (locations : SharedLocations) (world logs logSize balances : Core.Value)
    (store : Core.Store) : SharedFrame locations store (checkpointStore locations world logs logSize balances store) :=
  (((SharedFrame.write (by simp [SharedLocations.mutable]) store balances).trans
    (.write (by simp [SharedLocations.mutable]) _ logSize)).trans
    (.write (by simp [SharedLocations.mutable]) _ logs)).trans
    (.write (by simp [SharedLocations.mutable]) _ world)

theorem checkpointRestore_all_evaluates {depth : Nat} {environment : Core.Environment} {initial : Core.Store}
    {shared : AccountRuntime.References} {locations : SharedLocations}
    (world logs logSize balances : Core.Value)
    (references : SharedReferences depth environment shared locations) (extra : Core.Environment)
    (bounded : ∀ location ∈ locations.mutable, location < initial.length) :
    Core.Evaluates (extra ++ [balances, logSize, logs, world] ++ environment) initial
      (checkpointRestore shared depth (depth + 4 + extra.length)) .unit
      (checkpointStore locations world logs logSize balances initial) := by
  have balanceValue := (CodeValue.bound (depth + 3) (logSize :: logs :: world :: environment) balances).prepend extra
  have sizeValue := ((CodeValue.bound (depth + 2) (logs :: world :: environment) logSize).prepend [balances]).prepend extra
  have logsValue := ((CodeValue.bound (depth + 1) (world :: environment) logs).prepend [balances, logSize]).prepend extra
  have worldValue := ((CodeValue.bound depth environment world).prepend [balances, logSize, logs]).prepend extra
  have refs := references.prepend (extra ++ [balances, logSize, logs, world])
  have refsDepth : depth + (extra ++ [balances, logSize, logs, world]).length = depth + 4 + extra.length := by simp; omega
  rw [refsDepth] at refs
  simp only [List.append_assoc, List.cons_append, List.nil_append] at refs ⊢
  have balanceBound := bounded locations.balances (by simp [SharedLocations.mutable])
  have sizeBound : locations.logSize < (initial.set locations.balances balances).length := by
    simpa only [List.length_set] using bounded locations.logSize (by simp [SharedLocations.mutable])
  have logsBound : locations.logs < ((initial.set locations.balances balances).set locations.logSize logSize).length := by
    simpa only [List.length_set] using bounded locations.logs (by simp [SharedLocations.mutable])
  have worldBound : locations.world < (((initial.set locations.balances balances).set locations.logSize logSize).set locations.logs logs).length := by
    simpa only [List.length_set] using bounded locations.world (by simp [SharedLocations.mutable])
  apply Core.Evaluates.letE (.storeCell (refs.balances.evaluates initial) (List.getElem?_eq_getElem balanceBound)
    (balanceValue.evaluates initial) (Store.write?_eq_some_iff.mpr ⟨balanceBound, rfl⟩))
  apply Core.Evaluates.letE (.storeCell ((refs.logSize.prepend [.unit]).evaluates _) (List.getElem?_eq_getElem sizeBound)
    ((sizeValue.prepend [.unit]).evaluates _) (Store.write?_eq_some_iff.mpr ⟨sizeBound, rfl⟩))
  apply Core.Evaluates.letE (.storeCell ((refs.logs.prepend [.unit, .unit]).evaluates _) (List.getElem?_eq_getElem logsBound)
    ((logsValue.prepend [.unit, .unit]).evaluates _) (Store.write?_eq_some_iff.mpr ⟨logsBound, rfl⟩))
  apply Core.Evaluates.letE (.storeCell ((refs.world.prepend [.unit, .unit, .unit]).evaluates _) (List.getElem?_eq_getElem worldBound)
    ((worldValue.prepend [.unit, .unit, .unit]).evaluates _) (Store.write?_eq_some_iff.mpr ⟨worldBound, rfl⟩))
  exact .unit

theorem SharedStateRel.mutable_bounded {locations : SharedLocations} {state : AccountCallSemantics.Shared}
    {store : Core.Store} (related : SharedStateRel locations state store) :
    ∀ location ∈ locations.mutable, location < store.length := by
  intro location member
  simp only [SharedLocations.mutable, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · obtain ⟨_, _, read⟩ := related.world; exact (List.getElem?_eq_some_iff.mp read).1
  · exact (List.getElem?_eq_some_iff.mp related.logs).1
  · exact (List.getElem?_eq_some_iff.mp related.logSize).1
  · exact (List.getElem?_eq_some_iff.mp related.balances).1

theorem checkpointStore_restores {anchors : List CatalogWorldCorrespondence.Anchor}
    {locations : SharedLocations} {state : AccountCallSemantics.Shared} {initial current : Core.Store}
    {accounts : StorageCorrespondence.Accounts}
    (related : SharedStateRel locations state initial)
    (same : accounts.map Prod.fst = state.world) (links : CatalogWorldCorrespondence.Links anchors accounts)
    (frame : SharedFrame locations initial current) :
    LinkedSharedStateRel anchors locations state
      (checkpointStore locations (StorageCorrespondence.world accounts) (WordMapping.encode state.logs)
        (.word state.logSize) (WordMapping.encode state.balances) current) := by
  have bounds : ∀ location ∈ locations.mutable, location < current.length :=
    fun location member => Nat.lt_of_lt_of_le (related.mutable_bounded location member) frame.length_le
  have distinct := related.distinct
  simp only [SharedLocations.all, List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
    not_or, List.nodup_nil, and_true] at distinct
  have readWorld : (checkpointStore locations (StorageCorrespondence.world accounts) (WordMapping.encode state.logs)
      (.word state.logSize) (WordMapping.encode state.balances) current).read? locations.world = some (StorageCorrespondence.world accounts) := by
    apply List.getElem?_set_self
    simpa only [List.length_set] using bounds locations.world (by simp [SharedLocations.mutable])
  have readLogs : (checkpointStore locations (StorageCorrespondence.world accounts) (WordMapping.encode state.logs)
      (.word state.logSize) (WordMapping.encode state.balances) current).read? locations.logs = some (WordMapping.encode state.logs) := by
    unfold checkpointStore Store.read?
    rw [List.getElem?_set_ne distinct.1.1]
    apply List.getElem?_set_self
    simpa only [List.length_set] using bounds locations.logs (by simp [SharedLocations.mutable])
  have readSize : (checkpointStore locations (StorageCorrespondence.world accounts) (WordMapping.encode state.logs)
      (.word state.logSize) (WordMapping.encode state.balances) current).read? locations.logSize = some (.word state.logSize) := by
    unfold checkpointStore Store.read?
    rw [List.getElem?_set_ne distinct.1.2.1, List.getElem?_set_ne distinct.2.1.1]
    apply List.getElem?_set_self
    simpa only [List.length_set] using bounds locations.logSize (by simp [SharedLocations.mutable])
  have readBalances : (checkpointStore locations (StorageCorrespondence.world accounts) (WordMapping.encode state.logs)
      (.word state.logSize) (WordMapping.encode state.balances) current).read? locations.balances = some (WordMapping.encode state.balances) := by
    unfold checkpointStore Store.read?
    rw [List.getElem?_set_ne distinct.1.2.2.1, List.getElem?_set_ne distinct.2.1.2.1,
      List.getElem?_set_ne distinct.2.2.1.1]
    exact List.getElem?_set_self (bounds locations.balances (by simp [SharedLocations.mutable]))
  have outside : locations.complete ∉ locations.mutable := by
    simp only [SharedLocations.mutable, List.mem_cons, List.not_mem_nil, or_false, not_or]
    exact ⟨Ne.symm distinct.1.2.2.2, Ne.symm distinct.2.1.2.2,
      Ne.symm distinct.2.2.1.2, Ne.symm distinct.2.2.2.1⟩
  have complete := (frame.trans (checkpointStore_frame locations (StorageCorrespondence.world accounts) (WordMapping.encode state.logs) (.word state.logSize) (WordMapping.encode state.balances) current)).read
    locations.complete _ outside related.complete
  exact ⟨⟨⟨accounts, same, readWorld⟩, readLogs, readSize, readBalances, complete, related.distinct⟩,
    accounts, same, links, readWorld⟩

end Solcore.Frontend.RustHull.AccountCallCorrespondence
