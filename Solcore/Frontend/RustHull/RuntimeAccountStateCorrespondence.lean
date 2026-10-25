import Solcore.Frontend.RustHull.RuntimeAccountEffectsSemantics
import Solcore.Frontend.RustHull.RuntimeHashEffectsCorrespondence

/-! The concrete balance cell extends the established runtime model. Its
contents are derived from initialization and retained by current operations. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.RuntimeAccountEffectsCorrespondence
open Correspondence

structure Layout extends toLogLayout : RuntimeLogEffectsCorrespondence.Layout where
  balances : Nat
  balancesBelow : balances < boundary
  balancesOutside : balances ∉ RuntimeLogEffectsCorrespondence.mutable toLogLayout

def Resources (layout : Layout) (baseline : Nat → Option Core.Value) (slots : List EffectSlot)
    (state : RuntimeAccountEffectsSemantics.State) (read : Nat → Option Core.Value) : Prop :=
  RuntimeLogEffectsCorrespondence.Resources layout.toLogLayout baseline slots state.runtime read ∧
  read layout.balances = some (Core.WordMapping.encode state.balances)

def model (layout : Layout) (baseline : Nat → Option Core.Value) (slots : List EffectSlot) :
    StateModel RuntimeAccountEffectsSemantics.State :=
  StateModel.cutoff layout.boundary (Resources layout baseline slots)

def sourceRuntime (state : Semantics.State RuntimeAccountEffectsSemantics.State) :
    Semantics.State RuntimeHashEffectsSemantics.State := ⟨state.heap, state.external.runtime⟩

theorem runtime_related {layout : Layout} {baseline : Nat → Option Core.Value} {slots : List EffectSlot}
    {world : World} {state : Semantics.State RuntimeAccountEffectsSemantics.State} {store : Core.Store}
    (related : StateRel (model layout baseline slots) world state store) :
    StateRel (RuntimeLogEffectsCorrespondence.model layout.toLogLayout baseline slots) world (sourceRuntime state) store :=
  ⟨related.toHeapRel, related.external.1, related.external.2.1, related.external.2.2.1⟩

theorem balances_related {layout : Layout} {baseline : Nat → Option Core.Value} {slots : List EffectSlot}
    {world : World} {state : Semantics.State RuntimeAccountEffectsSemantics.State} {store : Core.Store}
    (related : StateRel (model layout baseline slots) world state store) :
    store.read? layout.balances = some (Core.WordMapping.encode state.external.balances) := by
  simpa only [prefixRead, layout.balancesBelow, ↓reduceIte] using related.external.2.2.2

theorem runtime_updated {layout : Layout} {baseline : Nat → Option Core.Value} {slots : List EffectSlot}
    {world : World} {state : Semantics.State RuntimeAccountEffectsSemantics.State}
    {initial final : Core.Store} {runtime : RuntimeHashEffectsSemantics.State}
    (before : StateRel (model layout baseline slots) world state initial)
    (after : StateRel (RuntimeLogEffectsCorrespondence.model layout.toLogLayout baseline slots) world
      {sourceRuntime state with external := runtime} final) :
    StateRel (model layout baseline slots) world {state with external := {state.external with runtime := runtime}} final := by
  refine ⟨after.toHeapRel, after.external.1, after.external.2.1, after.external.2.2, ?_⟩
  rw [RuntimeLogEffectsCorrespondence.other_related after layout.balancesOutside,
    ← RuntimeLogEffectsCorrespondence.other_related (runtime_related before) layout.balancesOutside]
  exact before.external.2.2.2

theorem memory_updated {layout : Layout} {baseline : Nat → Option Core.Value} {slots : List EffectSlot}
    (passive : RuntimeLogEffectsCorrespondence.Passive layout.toLogLayout slots)
    {world : World} {state : Semantics.State RuntimeAccountEffectsSemantics.State}
    {initial final : Core.Store} {memory : MemorySemantics.State}
    (before : StateRel (model layout baseline slots) world state initial)
    (memoryAfter : MemoryCorrespondence.StateRel layout.memory layout.storage.memorySize memory final)
    (frame : MemoryCorrespondence.Frame layout.memory layout.storage.memorySize initial final) :
    StateRel (model layout baseline slots) world
      {state with external := RuntimeAccountEffectsSemantics.withMemory state.external memory} final :=
  runtime_updated before (RuntimeCopyEffectsCorrespondence.memory_updated passive (runtime_related before) memoryAfter frame)

theorem initial_state {layout : Layout} {slots : List EffectSlot} {state : RuntimeAccountEffectsSemantics.State}
    {store : Core.Store}
    (runtime : StateRel (RuntimeLogEffectsCorrespondence.model layout.toLogLayout
      (prefixRead layout.boundary store) slots) [] ⟨[], state.runtime⟩ store)
    (balances : store.read? layout.balances = some (Core.WordMapping.encode state.balances)) :
    StateRel (model layout (prefixRead layout.boundary store) slots) [] ⟨[], state⟩ store :=
  ⟨runtime.toHeapRel, runtime.external.1, runtime.external.2.1, runtime.external.2.2,
    by simpa only [prefixRead, layout.balancesBelow, ↓reduceIte] using balances⟩

end Solcore.Frontend.RustHull.RuntimeAccountEffectsCorrespondence
