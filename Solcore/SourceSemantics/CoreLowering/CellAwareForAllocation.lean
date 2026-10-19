import Solcore.SourceSemantics.CoreLowering.TypedImperativeForNative
import Solcore.SourceSemantics.CoreLowering.TypedLexicalWhileAllocation
import Solcore.SourceSemantics.CoreLowering.GenericCellHeapOperations
import Solcore.SourceSemantics.CoreLowering.CellAwareScopeAuthority

/-! The real for prelude installs its recursive Core closure while retaining
all ordinary cells and exact generalized bundles. Source allocation and lexical
scope are unchanged by this administrative self cell. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareForAllocation
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open TypedLexicalWhile (installedStore installedWorld)

theorem install {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
    {definitions : DataEnvironment} {model : GenericHeap.PayloadModel catalog projects definitions}
    {instances : GeneralizedLocalDescriptorHeap.InstanceModel definitions}
    {mapping : LocationMap} {world : StoreTyping} {heap : Dynamic.Heap} {store : Store}
    {environment : Environment} {context : Core.Context} {type : Ty} {condition body post : Expr}
    (reason : Word)
    (heaps : GenericHeap.CellHeapRepresents (GeneralizedLocalDescriptorHeap.cellModel model instances) mapping world heap store)
    (environmentTyped : RuntimeEnvironmentHasTypes world environment context definitions)
    (typed : HasType context (LocalLoop.iterate type condition body post reason) (LocalLoop.resultType type) definitions) :
    GenericHeap.CellHeapRepresents (GeneralizedLocalDescriptorHeap.cellModel model instances) mapping (installedWorld world type) heap
      (installedStore store type condition body post reason environment) ∧
    WorldExtends world (installedWorld world type) ∧ store.length ∉ mapping ∧
    (installedWorld world type)[store.length]? = some (OptionalCell.cellType (LocalLoop.functionType type)) ∧
    (installedStore store type condition body post reason environment).read? store.length =
      some (.inRight .unit (LocalLoop.installedClosure type condition body post reason store.length environment)) ∧
    AdministrativePreserved mapping store mapping (installedStore store type condition body post reason environment) ∧
    CellAwareScopeAuthority.Effect instances mapping world heap store mapping (installedWorld world type) heap
      (installedStore store type condition body post reason environment) := by
  have worlds : WorldExtends world (installedWorld world type) := ⟨_, rfl⟩
  have found : (installedWorld world type)[store.length]? = some (OptionalCell.cellType (LocalLoop.functionType type)) := by
    rw [← heaps.runtime_hasTypes.length_eq]
    simp [installedWorld, LoopAdministration.installedWorld]
  have closureTyped : RuntimeValueHasType (installedWorld world type)
      (LocalLoop.installedClosure type condition body post reason store.length environment)
      (LocalLoop.functionType type) definitions :=
    .closure (.cons (.cellRef found) (environmentTyped.weaken worlds)) (TypedImperativeFor.Native.installed_body typed)
  have absentTyped : RuntimeValueHasType world (.inLeft (LocalLoop.functionType type) .unit)
      (OptionalCell.cellType (LocalLoop.functionType type)) definitions := .inLeft .unit
  have allocated := heaps.allocate_administrative absentTyped
  have written : (store.allocate (.inLeft (LocalLoop.functionType type) .unit)).1.write? store.length
      (.inRight .unit (LocalLoop.installedClosure type condition body post reason store.length environment)) =
      some (installedStore store type condition body post reason environment) := by
    simp [Store.allocate, Store.write?, installedStore, LoopAdministration.installedStore]
  have filled := allocated.write_administrative heaps.fresh_unmapped found (.inRight closureTyped) written
  refine ⟨filled, worlds, ?_, found, ?_, AdministrativePreserved.allocate_administrative _ _ _, ?_⟩
  · intro member
    obtain ⟨index, lookup⟩ := List.mem_iff_getElem?.mp member
    exact heaps.fresh_unmapped lookup
  · simp [installedStore, LoopAdministration.installedStore, Store.read?]

  · exact CellAwareScopeAuthority.Effect.append store _ (.refl heap) (.refl mapping) worlds

end Solcore.SourceSemantics.CoreLowering.CellAwareForAllocation
