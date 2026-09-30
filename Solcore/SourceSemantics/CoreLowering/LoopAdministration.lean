import Solcore.SourceSemantics.CoreLowering.GeneralHeapFrame
import Solcore.Core.LocalLoop

/-! Install the actual generated loop closure in an administrative optional
cell. Captured environments and generated bodies are supplied concretely;
there is no assertion that renamed closure captures are equal. The source
heap and source-to-Core location map remain unchanged. -/

set_option autoImplicit false

namespace Solcore.SourceSemantics.CoreLowering.LoopAdministration

open GeneralHeap

def installedStore (store : Core.Store) (type : Core.Ty) (condition body post : Core.Expr)
    (reason : Core.Word) (environment : Core.Environment) : Core.Store :=
  store ++ [.inRight .unit (Core.LocalLoop.installedClosure type condition body post reason store.length environment)]

def installedWorld (world : Core.StoreTyping) (type : Core.Ty) : Core.StoreTyping :=
  world ++ [Core.OptionalCell.cellType (Core.LocalLoop.functionType type)]

/-- Ordinary finite-world typing validates a self-referential closure after
allocating its absent optional cell. Filling that cell leaves all source cells
and every earlier administrative cell unchanged. -/
theorem install
    {mapping : LocationMap} {world : Core.StoreTyping} {heap : Dynamic.Heap} {store : Core.Store}
    {environment : Core.Environment} {context : Core.Context} {type : Core.Ty}
    {condition body post : Core.Expr} (reason : Core.Word)
    (heaps : HeapRepresents mapping world heap store)
    (environmentTyped : Core.RuntimeEnvironmentHasTypes world environment context)
    (wellFormed : Core.Ty.WellFormed [] type)
    (conditionTyped : Core.HasType context condition (Core.LanguageResult.resultType .bool))
    (bodyTyped : Core.HasType context body (Core.LocalLoop.resultType type))
    (postTyped : Core.HasType context post (Core.LocalLoop.resultType type)) :
    HeapRepresents mapping (installedWorld world type) heap (installedStore store type condition body post reason environment) ∧
    Core.WorldExtends world (installedWorld world type) ∧
    store.length ∉ mapping ∧
    (installedWorld world type)[store.length]? = some (Core.OptionalCell.cellType (Core.LocalLoop.functionType type)) ∧
    (installedStore store type condition body post reason environment).read? store.length =
      some (.inRight .unit (Core.LocalLoop.installedClosure type condition body post reason store.length environment)) ∧
    AdministrativePreserved mapping store mapping (installedStore store type condition body post reason environment) := by
  have worldExtension : Core.WorldExtends world (installedWorld world type) := ⟨_, rfl⟩
  have found : (installedWorld world type)[store.length]? =
      some (Core.OptionalCell.cellType (Core.LocalLoop.functionType type)) := by
    rw [← heaps.runtime_hasTypes.length_eq]
    simp [installedWorld]
  have typed : Core.RuntimeValueHasType (installedWorld world type)
      (Core.LocalLoop.installedClosure type condition body post reason store.length environment)
      (Core.LocalLoop.functionType type) :=
    .closure (.cons (.cellRef found) (Core.RuntimeEnvironmentHasTypes.weaken worldExtension environmentTyped))
      (Core.LocalLoop.loopBody_hasType reason wellFormed conditionTyped bodyTyped postTyped)
  have absentTyped : Core.RuntimeValueHasType world (.inLeft (Core.LocalLoop.functionType type) .unit)
      (Core.OptionalCell.cellType (Core.LocalLoop.functionType type)) :=
    .inLeft .unit
  have allocated := heaps.allocate_administrative absentTyped
  have written : (store.allocate (.inLeft (Core.LocalLoop.functionType type) .unit)).1.write? store.length
      (.inRight .unit (Core.LocalLoop.installedClosure type condition body post reason store.length environment)) =
      some (installedStore store type condition body post reason environment) := by
    simp [Core.Store.allocate, Core.Store.write?, installedStore]
  have filled := allocated.write_administrative heaps.fresh_unmapped found (.inRight typed) written
  refine ⟨filled, worldExtension, ?_, found, ?_, ?_⟩
  · intro member
    obtain ⟨index, lookup⟩ := List.mem_iff_getElem?.mp member
    exact heaps.fresh_unmapped lookup
  · simp [installedStore, Core.Store.read?]
  · exact AdministrativePreserved.allocate_administrative _ _ _

/-- Any later represented source computation preserves this installed loop
code whenever it supplies the administrative frame property. -/
theorem retained
    {mapping futureMapping : LocationMap} {world : Core.StoreTyping} {heap : Dynamic.Heap} {store futureStore : Core.Store}
    {environment : Core.Environment} {type : Core.Ty} {condition body post : Core.Expr} {reason : Core.Word}
    (heaps : HeapRepresents mapping world heap store)
    (frame : AdministrativePreserved mapping (installedStore store type condition body post reason environment)
      futureMapping futureStore) :
    store.length ∉ futureMapping ∧ futureStore.read? store.length =
      some (.inRight .unit (Core.LocalLoop.installedClosure type condition body post reason store.length environment)) := by
  have unmapped : store.length ∉ mapping := by
    intro member
    obtain ⟨index, lookup⟩ := List.mem_iff_getElem?.mp member
    exact heaps.fresh_unmapped lookup
  obtain ⟨futureUnmapped, same⟩ := frame store.length unmapped (by simp [installedStore])
  exact ⟨futureUnmapped, same.trans (by simp [installedStore, Core.Store.read?])⟩

end Solcore.SourceSemantics.CoreLowering.LoopAdministration
