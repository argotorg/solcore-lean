import Solcore.SourceSemantics.CoreLowering.CellAwareLoopState

/-! The progress of an actual loop child keeps generalized descriptor bundles
alongside ordinary cells. Composition retains the concrete intermediate heaps. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareLoopState
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload

variable {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
  {definitions : DataEnvironment} (model : GenericHeap.PayloadModel catalog projects definitions)
  (instances : GeneralizedLocalDescriptorHeap.InstanceModel definitions)

structure Progress (before after : Dynamic.Heap) (mapping nextMap : LocationMap)
    (world nextWorld : StoreTyping) (store finalStore : Store) : Prop where
  heaps : GenericHeap.CellHeapRepresents (GeneralizedLocalDescriptorHeap.cellModel model instances)
    nextMap nextWorld after finalStore
  maps : LocationMap.Extends mapping nextMap
  worlds : WorldExtends world nextWorld
  preserved : AdministrativePreserved mapping store nextMap finalStore
  metadata : Dynamic.HeapMetadataExtend before after
  effect : CellAwareScopeAuthority.Effect instances mapping world before store nextMap nextWorld after finalStore

variable {model instances}
  {before middle after : Dynamic.Heap} {mapping middleMap finalMap : LocationMap}
  {world middleWorld finalWorld : StoreTyping} {store middleStore finalStore : Store}

theorem Progress.trans
    (first : Progress model instances before middle mapping middleMap world middleWorld store middleStore)
    (last : Progress model instances middle after middleMap finalMap middleWorld finalWorld middleStore finalStore) :
    Progress model instances before after mapping finalMap world finalWorld store finalStore :=
  ⟨last.heaps, first.maps.trans last.maps, first.worlds.trans last.worlds,
    first.preserved.trans last.preserved, first.metadata.trans last.metadata, first.effect.trans last.effect⟩

end Solcore.SourceSemantics.CoreLowering.CellAwareLoopState
