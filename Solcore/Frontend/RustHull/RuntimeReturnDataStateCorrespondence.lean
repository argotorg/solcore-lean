import Solcore.Frontend.RustHull.RuntimeReturnDataEffectsSemantics
import Solcore.Frontend.RustHull.RuntimeCodeStateCorrespondence

/-! Return-data cells are caller resources. The baseline supplied to the older
runtime models observes their current source contents, and optional code cells
allow the same relation to cover frames without a linked code image. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.RuntimeReturnDataEffectsCorrespondence
open Correspondence

structure CodeCells (base : RuntimeAccountEffectsCorrespondence.Layout) where
  code : Nat
  known : Nat
  codeBelow : code < base.boundary
  knownBelow : known < base.boundary
  codeOutside : code ∉ RuntimeLogEffectsCorrespondence.mutable base.toLogLayout
  knownOutside : known ∉ RuntimeLogEffectsCorrespondence.mutable base.toLogLayout

structure Layout extends toAccountLayout : RuntimeAccountEffectsCorrespondence.Layout where
  codeCells : Option (CodeCells toAccountLayout)
  returnData : Nat
  returnDataSize : Nat
  dataBelow : returnData < boundary
  sizeBelow : returnDataSize < boundary
  dataOutside : returnData ∉ RuntimeLogEffectsCorrespondence.mutable toLogLayout
  sizeOutside : returnDataSize ∉ RuntimeLogEffectsCorrespondence.mutable toLogLayout
  dataDistinct : returnData ≠ returnDataSize

def patched (layout : Layout) (baseline : Nat → Option Core.Value)
    (state : RuntimeReturnDataEffectsSemantics.State) (location : Nat) : Option Core.Value :=
  if location = layout.returnData then some (Core.WordMapping.encode state.returnData)
  else if location = layout.returnDataSize then some (.word (RuntimeReturnDataEffectsSemantics.size state))
  else baseline location

def CodeResources (layout : Layout) (image : Option (List UInt8)) (read : Nat → Option Core.Value) : Prop :=
  ∀ cells, layout.codeCells = some cells →
    read cells.code = some (Core.WordMapping.encode (Memory.packBytes (image.getD []))) ∧
    read cells.known = some (.bool image.isSome)

def Resources (layout : Layout) (baseline : Nat → Option Core.Value) (slots : List EffectSlot)
    (image : Option (List UInt8)) (state : RuntimeReturnDataEffectsSemantics.State)
    (read : Nat → Option Core.Value) : Prop :=
  RuntimeAccountEffectsCorrespondence.Resources layout.toAccountLayout (patched layout baseline state) slots state.runtime read ∧
  read layout.returnData = some (Core.WordMapping.encode state.returnData) ∧
  read layout.returnDataSize = some (.word (RuntimeReturnDataEffectsSemantics.size state)) ∧
  CodeResources layout image read

def model (layout : Layout) (baseline : Nat → Option Core.Value) (slots : List EffectSlot)
    (image : Option (List UInt8)) : StateModel RuntimeReturnDataEffectsSemantics.State :=
  StateModel.cutoff layout.boundary (Resources layout baseline slots image)

def sourceRuntime (state : Semantics.State RuntimeReturnDataEffectsSemantics.State) :
    Semantics.State RuntimeAccountEffectsSemantics.State := ⟨state.heap, state.external.runtime⟩

theorem account_related {layout : Layout} {baseline : Nat → Option Core.Value} {slots : List EffectSlot}
    {image : Option (List UInt8)} {world : World} {state : Semantics.State RuntimeReturnDataEffectsSemantics.State}
    {store : Core.Store} (related : StateRel (model layout baseline slots image) world state store) :
    StateRel (RuntimeAccountEffectsCorrespondence.model layout.toAccountLayout (patched layout baseline state.external) slots)
      world (sourceRuntime state) store :=
  ⟨related.toHeapRel, related.external.1, related.external.2.1, related.external.2.2.1⟩

theorem data_related {layout : Layout} {baseline : Nat → Option Core.Value} {slots : List EffectSlot}
    {image : Option (List UInt8)} {world : World} {state : Semantics.State RuntimeReturnDataEffectsSemantics.State}
    {store : Core.Store} (related : StateRel (model layout baseline slots image) world state store) :
    store.read? layout.returnData = some (Core.WordMapping.encode state.external.returnData) := by
  simpa only [prefixRead, layout.dataBelow, ↓reduceIte] using related.external.2.2.2.1

theorem size_related {layout : Layout} {baseline : Nat → Option Core.Value} {slots : List EffectSlot}
    {image : Option (List UInt8)} {world : World} {state : Semantics.State RuntimeReturnDataEffectsSemantics.State}
    {store : Core.Store} (related : StateRel (model layout baseline slots image) world state store) :
    store.read? layout.returnDataSize = some (.word (RuntimeReturnDataEffectsSemantics.size state.external)) := by
  simpa only [prefixRead, layout.sizeBelow, ↓reduceIte] using related.external.2.2.2.2.1

theorem code_related {layout : Layout} {baseline : Nat → Option Core.Value} {slots : List EffectSlot}
    {image : Option (List UInt8)} {world : World} {state : Semantics.State RuntimeReturnDataEffectsSemantics.State}
    {store : Core.Store} (related : StateRel (model layout baseline slots image) world state store)
    {cells : CodeCells layout.toAccountLayout} (present : layout.codeCells = some cells) :
    store.read? cells.code = some (Core.WordMapping.encode (Memory.packBytes (image.getD []))) ∧
    store.read? cells.known = some (.bool image.isSome) := by
  simpa only [prefixRead, cells.codeBelow, cells.knownBelow, ↓reduceIte]
    using related.external.2.2.2.2.2 cells present

theorem account_updated {layout : Layout} {baseline : Nat → Option Core.Value} {slots : List EffectSlot}
    {image : Option (List UInt8)} {world : World} {state : Semantics.State RuntimeReturnDataEffectsSemantics.State}
    {initial final : Core.Store} {runtime : RuntimeAccountEffectsSemantics.State}
    (before : StateRel (model layout baseline slots image) world state initial)
    (after : StateRel (RuntimeAccountEffectsCorrespondence.model layout.toAccountLayout
      (patched layout baseline state.external) slots) world {sourceRuntime state with external := runtime} final)
    (sizeEqual : runtime.runtime.runtime.environment.direct .returnDataSize =
      state.external.runtime.runtime.runtime.environment.direct .returnDataSize) :
    StateRel (model layout baseline slots image) world {state with external := {state.external with runtime := runtime}} final := by
  have patchEqual : patched layout baseline {state.external with runtime := runtime} = patched layout baseline state.external := by
    funext location
    simp only [patched, RuntimeReturnDataEffectsSemantics.size, sizeEqual]
  refine ⟨after.toHeapRel, after.external.1, after.external.2.1, ?_, ?_, ?_, ?_⟩
  · rw [patchEqual]
    exact after.external.2.2
  · rw [RuntimeLogEffectsCorrespondence.other_related
      (RuntimeAccountEffectsCorrespondence.runtime_related after) layout.dataOutside]
    simp [patched]
  · rw [RuntimeLogEffectsCorrespondence.other_related
      (RuntimeAccountEffectsCorrespondence.runtime_related after) layout.sizeOutside]
    simp [patched, Ne.symm layout.dataDistinct, RuntimeReturnDataEffectsSemantics.size, sizeEqual]
  · intro cells present
    rw [RuntimeLogEffectsCorrespondence.other_related
      (RuntimeAccountEffectsCorrespondence.runtime_related after) cells.codeOutside,
      RuntimeLogEffectsCorrespondence.other_related
      (RuntimeAccountEffectsCorrespondence.runtime_related after) cells.knownOutside,
      ← RuntimeLogEffectsCorrespondence.other_related
      (RuntimeAccountEffectsCorrespondence.runtime_related (account_related before)) cells.codeOutside,
      ← RuntimeLogEffectsCorrespondence.other_related
      (RuntimeAccountEffectsCorrespondence.runtime_related (account_related before)) cells.knownOutside]
    exact before.external.2.2.2.2.2 cells present

theorem memory_updated {layout : Layout} {baseline : Nat → Option Core.Value} {slots : List EffectSlot}
    (passive : RuntimeLogEffectsCorrespondence.Passive layout.toLogLayout slots)
    {image : Option (List UInt8)} {world : World} {state : Semantics.State RuntimeReturnDataEffectsSemantics.State}
    {initial final : Core.Store} {memory : MemorySemantics.State}
    (before : StateRel (model layout baseline slots image) world state initial)
    (memoryAfter : MemoryCorrespondence.StateRel layout.memory layout.storage.memorySize memory final)
    (frame : MemoryCorrespondence.Frame layout.memory layout.storage.memorySize initial final) :
    StateRel (model layout baseline slots image) world
      {state with external := {state.external with runtime := RuntimeAccountEffectsSemantics.withMemory state.external.runtime memory}} final :=
  account_updated before (RuntimeAccountEffectsCorrespondence.memory_updated passive (account_related before) memoryAfter frame) rfl

theorem runtime_updated {layout : Layout} {baseline : Nat → Option Core.Value} {slots : List EffectSlot}
    (passive : RuntimeLogEffectsCorrespondence.Passive layout.toLogLayout slots)
    {image : Option (List UInt8)} {world : World} {state : Semantics.State RuntimeReturnDataEffectsSemantics.State}
    {initial final : Core.Store} {runtime : RuntimeEffectsSemantics.State}
    (before : StateRel (model layout baseline slots image) world state initial)
    (memoryAfter : MemoryCorrespondence.StateRel layout.memory layout.storage.memorySize runtime.memory final)
    (storageAfter : StorageBuiltinCorrespondence.StateRel layout.storage runtime.storage final)
    (frame : RuntimeEffectsCorrespondence.Frame layout.toLayout initial final) :
    StateRel (model layout baseline slots image) world
      {state with external := RuntimeReturnDataEffectsSemantics.withRuntime state.external runtime} final := by
  have accountBefore := account_related before
  have logBefore := RuntimeAccountEffectsCorrespondence.runtime_related accountBefore
  have environmentBefore := RuntimeLogEffectsCorrespondence.runtime_related logBefore
  have runtimeBefore := RuntimeEnvironmentEffectsCorrespondence.runtime_related environmentBefore
  have runtimeAfter := runtimeBefore.cutoff_effect (RuntimeEffectsCorrespondence.frame_above frame)
    (RuntimeEffectsCorrespondence.resources_preserved runtimeBefore.external.1 runtimeBefore.external.2.2 memoryAfter storageAfter frame)
  have environmentAfter := RuntimeEnvironmentEffectsCorrespondence.runtime_updated
    (RuntimeLogEffectsCorrespondence.passive_runtime passive) environmentBefore runtimeAfter
  have logAfter := RuntimeLogEffectsCorrespondence.runtime_updated environmentAfter
  exact account_updated before (RuntimeAccountEffectsCorrespondence.runtime_updated accountBefore logAfter) rfl

theorem initial_state {layout : Layout} {slots : List EffectSlot} {state : RuntimeReturnDataEffectsSemantics.State}
    {store : Core.Store} {image : Option (List UInt8)}
    (runtime : StateRel (RuntimeAccountEffectsCorrespondence.model layout.toAccountLayout
      (prefixRead layout.boundary store) slots) [] ⟨[], state.runtime⟩ store)
    (data : store.read? layout.returnData = some (Core.WordMapping.encode state.returnData))
    (size : store.read? layout.returnDataSize = some (.word (RuntimeReturnDataEffectsSemantics.size state)))
    (code : ∀ cells, layout.codeCells = some cells →
      store.read? cells.code = some (Core.WordMapping.encode (Memory.packBytes (image.getD []))) ∧
      store.read? cells.known = some (.bool image.isSome)) :
    StateRel (model layout (prefixRead layout.boundary store) slots image) [] ⟨[], state⟩ store := by
  have patchEqual : patched layout (prefixRead layout.boundary store) state = prefixRead layout.boundary store := by
    funext location
    unfold patched
    split
    · subst location
      simpa only [prefixRead, layout.dataBelow, ↓reduceIte] using data.symm
    · split
      · subst location
        simpa only [prefixRead, layout.sizeBelow, ↓reduceIte] using size.symm
      · rfl
  refine ⟨runtime.toHeapRel, runtime.external.1, runtime.external.2.1, ?_, ?_, ?_, ?_⟩
  · rw [patchEqual]
    exact runtime.external.2.2
  · simpa only [prefixRead, layout.dataBelow, ↓reduceIte] using data
  · simpa only [prefixRead, layout.sizeBelow, ↓reduceIte] using size
  · intro cells present
    simpa only [prefixRead, cells.codeBelow, cells.knownBelow, ↓reduceIte] using code cells present

end Solcore.Frontend.RustHull.RuntimeReturnDataEffectsCorrespondence
