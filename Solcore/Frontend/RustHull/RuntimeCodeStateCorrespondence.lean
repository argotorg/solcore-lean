import Solcore.Frontend.RustHull.RuntimeAccountEffectsCorrespondence

/-! The immutable code bytes and availability flag extend the existing
runtime representation without adding another source state wrapper. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.RuntimeCodeEffectsCorrespondence
open Correspondence

structure Layout extends toAccountLayout : RuntimeAccountEffectsCorrespondence.Layout where
  code : Nat
  known : Nat
  codeBelow : code < boundary
  knownBelow : known < boundary
  codeOutside : code ∉ RuntimeLogEffectsCorrespondence.mutable toLogLayout
  knownOutside : known ∉ RuntimeLogEffectsCorrespondence.mutable toLogLayout

def Resources (layout : Layout) (baseline : Nat → Option Core.Value) (slots : List EffectSlot)
    (image : Option (List UInt8)) (state : RuntimeAccountEffectsSemantics.State)
    (read : Nat → Option Core.Value) : Prop :=
  RuntimeAccountEffectsCorrespondence.Resources layout.toAccountLayout baseline slots state read ∧
  read layout.code = some (Core.WordMapping.encode (Memory.packBytes (image.getD []))) ∧
  read layout.known = some (.bool image.isSome)

def model (layout : Layout) (baseline : Nat → Option Core.Value) (slots : List EffectSlot)
    (image : Option (List UInt8)) : StateModel RuntimeAccountEffectsSemantics.State :=
  StateModel.cutoff layout.boundary (Resources layout baseline slots image)

theorem account_related {layout : Layout} {baseline : Nat → Option Core.Value} {slots : List EffectSlot}
    {image : Option (List UInt8)} {world : World} {state : Semantics.State RuntimeAccountEffectsSemantics.State}
    {store : Core.Store} (related : StateRel (model layout baseline slots image) world state store) :
    StateRel (RuntimeAccountEffectsCorrespondence.model layout.toAccountLayout baseline slots) world state store :=
  ⟨related.toHeapRel, related.external.1, related.external.2.1, related.external.2.2.1⟩

theorem code_related {layout : Layout} {baseline : Nat → Option Core.Value} {slots : List EffectSlot}
    {image : Option (List UInt8)} {world : World} {state : Semantics.State RuntimeAccountEffectsSemantics.State}
    {store : Core.Store} (related : StateRel (model layout baseline slots image) world state store) :
    store.read? layout.code = some (Core.WordMapping.encode (Memory.packBytes (image.getD []))) := by
  simpa only [prefixRead, layout.codeBelow, ↓reduceIte] using related.external.2.2.2.1

theorem known_related {layout : Layout} {baseline : Nat → Option Core.Value} {slots : List EffectSlot}
    {image : Option (List UInt8)} {world : World} {state : Semantics.State RuntimeAccountEffectsSemantics.State}
    {store : Core.Store} (related : StateRel (model layout baseline slots image) world state store) :
    store.read? layout.known = some (.bool image.isSome) := by
  simpa only [prefixRead, layout.knownBelow, ↓reduceIte] using related.external.2.2.2.2

theorem account_updated {layout : Layout} {baseline : Nat → Option Core.Value} {slots : List EffectSlot}
    {image : Option (List UInt8)} {world : World} {beforeState afterState : Semantics.State RuntimeAccountEffectsSemantics.State}
    {initial final : Core.Store}
    (before : StateRel (model layout baseline slots image) world beforeState initial)
    (after : StateRel (RuntimeAccountEffectsCorrespondence.model layout.toAccountLayout baseline slots) world afterState final) :
    StateRel (model layout baseline slots image) world afterState final := by
  refine ⟨after.toHeapRel, after.external.1, after.external.2.1, after.external.2.2, ?_, ?_⟩
  · rw [RuntimeLogEffectsCorrespondence.other_related
      (RuntimeAccountEffectsCorrespondence.runtime_related after) layout.codeOutside,
      ← RuntimeLogEffectsCorrespondence.other_related
        (RuntimeAccountEffectsCorrespondence.runtime_related (account_related before)) layout.codeOutside]
    exact before.external.2.2.2.1
  · rw [RuntimeLogEffectsCorrespondence.other_related
      (RuntimeAccountEffectsCorrespondence.runtime_related after) layout.knownOutside,
      ← RuntimeLogEffectsCorrespondence.other_related
        (RuntimeAccountEffectsCorrespondence.runtime_related (account_related before)) layout.knownOutside]
    exact before.external.2.2.2.2

theorem memory_updated {layout : Layout} {baseline : Nat → Option Core.Value} {slots : List EffectSlot}
    (passive : RuntimeLogEffectsCorrespondence.Passive layout.toLogLayout slots)
    {image : Option (List UInt8)} {world : World} {state : Semantics.State RuntimeAccountEffectsSemantics.State}
    {initial final : Core.Store} {memory : MemorySemantics.State}
    (before : StateRel (model layout baseline slots image) world state initial)
    (memoryAfter : MemoryCorrespondence.StateRel layout.memory layout.storage.memorySize memory final)
    (frame : MemoryCorrespondence.Frame layout.memory layout.storage.memorySize initial final) :
    StateRel (model layout baseline slots image) world
      {state with external := RuntimeAccountEffectsSemantics.withMemory state.external memory} final :=
  account_updated before (RuntimeAccountEffectsCorrespondence.memory_updated passive (account_related before) memoryAfter frame)

theorem initial_state {layout : Layout} {slots : List EffectSlot} {state : RuntimeAccountEffectsSemantics.State}
    {store : Core.Store} {image : Option (List UInt8)}
    (runtime : StateRel (RuntimeAccountEffectsCorrespondence.model layout.toAccountLayout
      (prefixRead layout.boundary store) slots) [] ⟨[], state⟩ store)
    (code : store.read? layout.code = some (Core.WordMapping.encode (Memory.packBytes (image.getD []))))
    (known : store.read? layout.known = some (.bool image.isSome)) :
    StateRel (model layout (prefixRead layout.boundary store) slots image) [] ⟨[], state⟩ store :=
  ⟨runtime.toHeapRel, runtime.external.1, runtime.external.2.1, runtime.external.2.2,
    by simpa only [prefixRead, layout.codeBelow, ↓reduceIte] using code,
    by simpa only [prefixRead, layout.knownBelow, ↓reduceIte] using known⟩

end Solcore.Frontend.RustHull.RuntimeCodeEffectsCorrespondence
