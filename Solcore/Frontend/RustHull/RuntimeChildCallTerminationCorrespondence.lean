import Solcore.Frontend.RustHull.RuntimeChildCallStateCorrespondence
import Solcore.Frontend.RustHull.TerminationBuiltinCorrespondence

/-! The ordinary-call static guard changes termination registers, retaining
all account code identities in the unchanged world cell. -/
set_option autoImplicit false
set_option linter.unusedSimpArgs false
namespace Solcore.Frontend.RustHull.RuntimeChildCallEffectsCorrespondence
open Core Correspondence
open RuntimeCallEffectsCorrespondence (Layout Handlers)

theorem invalid_linked {layout : Layout} {baseline : Nat → Option Core.Value} {slots : List EffectSlot}
    {image : Option (List UInt8)} {handlers : Handlers layout} {anchors : Anchors} {context : RuntimeChildCallEffectsCorrespondence.Context layout} {world : World}
    {state : Semantics.State RuntimeCallEffectsSemantics.State} {store : Store}
    (related : StateRel (model layout baseline slots image handlers anchors context) world state store) :
    RuntimeLinkedWorldCorrespondence.StateRel anchors (sourceWorld (RuntimeCallEffectsSemantics.invalid state.external).2)
      layout.storage.world
      (TerminationBuiltinCorrespondence.finalStore layout.storage state.external.runtime.runtime.runtime.runtime.runtime 3 Word.zero Word.zero store) := by
  have linked := linked_related related
  change RuntimeLinkedWorldCorrespondence.StateRel anchors (sourceWorld state.external) layout.storage.world _
  apply linked.read_preserved
  intro value found
  have distinct := layout.distinct
  simp only [StorageBuiltinCorrespondence.Locations.all, List.nodup_cons, List.mem_cons,
    List.not_mem_nil, or_false, not_or] at distinct
  have notExit : layout.storage.exit ≠ layout.storage.world := by simp_all [ne_comm]
  have notOffset : layout.storage.returnOffset ≠ layout.storage.world := by simp_all [ne_comm]
  have notSize : layout.storage.returnSize ≠ layout.storage.world := by simp_all [ne_comm]
  have notMemorySize : layout.storage.world ≠ layout.storage.memorySize := by simp_all [ne_comm]
  change ((((MemoryCorrespondence.touchStore store layout.storage.memorySize
      state.external.runtime.runtime.runtime.runtime.runtime.memory.size Word.zero Word.zero).set layout.storage.returnOffset (.word Word.zero)).set
      layout.storage.returnSize (.word Word.zero)).set layout.storage.exit (.word (Word.ofNatModulo 3)))[layout.storage.world]? = some value
  rw [List.getElem?_set_ne notExit, List.getElem?_set_ne notSize, List.getElem?_set_ne notOffset]
  exact (MemoryCorrespondence.touchStore_other store notMemorySize _ _ _).trans found

end Solcore.Frontend.RustHull.RuntimeChildCallEffectsCorrespondence
