import Solcore.Frontend.RustHull.RuntimeCallEffectsSemantics
import Solcore.Frontend.RustHull.RuntimeReturnDataEffectsCorrespondence
import Solcore.Frontend.RustHull.AccountCallHandlersCorrespondence

/-! Calls can change balances and caller return data while retaining their
installed closures. The resource relation records concrete optional-cell
contents and captured runtime handlers, rather than assuming callback execution. -/
set_option autoImplicit false
set_option linter.unusedSimpArgs false
namespace Solcore.Frontend.RustHull.RuntimeCallEffectsCorrespondence
open Correspondence

structure Layout extends toReturnDataLayout : RuntimeReturnDataEffectsCorrespondence.Layout where
  callDepth : Nat
  callHandler : Nat
  dispatcher : Nat
  depthBelow : callDepth < boundary
  handlerBelow : callHandler < boundary
  dispatcherBelow : dispatcher < boundary
  callDistinct : (balances :: returnData :: returnDataSize :: callDepth :: callHandler :: dispatcher ::
    logs :: logSize :: memory :: storage.all).Nodup

def sharedLocations (layout : Layout) : AccountCallCorrespondence.SharedLocations :=
  ⟨layout.storage.world, layout.logs, layout.logSize, layout.balances, layout.storage.complete⟩

structure Handlers (layout : Layout) where
  source : Core.Word
  dispatchValue : Core.Value
  handlerValue : Core.Value
  dispatch : AccountCallCorrespondence.DispatcherClosure (sharedLocations layout) dispatchValue
  handler : AccountCallCorrespondence.CallHandlerClosure source layout.dispatcher handlerValue

def patched (layout : Layout) (baseline : Nat → Option Core.Value)
    (state : RuntimeCallEffectsSemantics.State) (location : Nat) : Option Core.Value :=
  if location = layout.balances then some (Core.WordMapping.encode state.runtime.runtime.balances) else baseline location

def mutable (layout : Layout) : List Nat :=
  layout.balances :: layout.returnData :: layout.returnDataSize :: RuntimeLogEffectsCorrespondence.mutable layout.toLogLayout

structure Resources (layout : Layout) (baseline : Nat → Option Core.Value) (slots : List EffectSlot)
    (image : Option (List UInt8)) (handlers : Handlers layout) (state : RuntimeCallEffectsSemantics.State)
    (read : Nat → Option Core.Value) : Prop where
  runtime : RuntimeReturnDataEffectsCorrespondence.Resources layout.toReturnDataLayout (patched layout baseline state) slots image state.runtime read
  depth : read layout.callDepth = some (.word state.callDepth)
  handler : read layout.callHandler = some (.inRight .unit handlers.handlerValue)
  dispatcher : read layout.dispatcher = some (.inRight .unit handlers.dispatchValue)
  source : read layout.storage.address = some (.word handlers.source)

def model (layout : Layout) (baseline : Nat → Option Core.Value) (slots : List EffectSlot)
    (image : Option (List UInt8)) (handlers : Handlers layout) : StateModel RuntimeCallEffectsSemantics.State :=
  StateModel.cutoff layout.boundary (Resources layout baseline slots image handlers)

def sourceRuntime (state : Semantics.State RuntimeCallEffectsSemantics.State) :
    Semantics.State RuntimeReturnDataEffectsSemantics.State := ⟨state.heap, state.external.runtime⟩

theorem runtime_related {layout : Layout} {baseline : Nat → Option Core.Value} {slots : List EffectSlot}
    {image : Option (List UInt8)} {handlers : Handlers layout} {world : World}
    {state : Semantics.State RuntimeCallEffectsSemantics.State} {store : Core.Store}
    (related : StateRel (model layout baseline slots image handlers) world state store) :
    StateRel (RuntimeReturnDataEffectsCorrespondence.model layout.toReturnDataLayout (patched layout baseline state.external) slots image)
      world (sourceRuntime state) store :=
  ⟨related.toHeapRel, related.external.1, related.external.2.1, related.external.2.2.runtime⟩

theorem account_related {layout : Layout} {baseline : Nat → Option Core.Value} {slots : List EffectSlot}
    {image : Option (List UInt8)} {handlers : Handlers layout} {world : World}
    {state : Semantics.State RuntimeCallEffectsSemantics.State} {store : Core.Store}
    (related : StateRel (model layout baseline slots image handlers) world state store) :
    StateRel (RuntimeAccountEffectsCorrespondence.model layout.toAccountLayout
      (RuntimeReturnDataEffectsCorrespondence.patched layout.toReturnDataLayout
        (patched layout baseline state.external) state.external.runtime) slots)
      world (RuntimeReturnDataEffectsCorrespondence.sourceRuntime (sourceRuntime state)) store :=
  RuntimeReturnDataEffectsCorrespondence.account_related (runtime_related related)

theorem call_separation (layout : Layout) :
    ∀ location ∈ [layout.callDepth, layout.callHandler, layout.dispatcher, layout.storage.address], location ∉ mutable layout := by
  have distinct := layout.callDistinct
  simp only [StorageBuiltinCorrespondence.Locations.all, List.nodup_cons, List.mem_cons, List.mem_singleton,
    List.not_mem_nil, or_false, not_or] at distinct
  intro location member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  all_goals simp only [mutable, RuntimeLogEffectsCorrespondence.mutable, RuntimeEffectsCorrespondence.mutable,
    StorageBuiltinCorrespondence.Locations.mutable, List.mem_cons, List.mem_append, List.not_mem_nil,
    or_false, not_or]
  all_goals simp_all [ne_comm]

theorem returnData_other {layout : Layout} {baseline : Nat → Option Core.Value} {slots : List EffectSlot}
    {image : Option (List UInt8)} {world : World} {state : Semantics.State RuntimeReturnDataEffectsSemantics.State}
    {store : Core.Store}
    (related : StateRel (RuntimeReturnDataEffectsCorrespondence.model layout.toReturnDataLayout baseline slots image) world state store)
    {location : Nat} (outside : location ∉ layout.returnData :: layout.returnDataSize :: RuntimeLogEffectsCorrespondence.mutable layout.toLogLayout) :
    prefixRead layout.boundary store location = baseline location := by
  have separate : location ≠ layout.returnData ∧ location ≠ layout.returnDataSize ∧ location ∉ RuntimeLogEffectsCorrespondence.mutable layout.toLogLayout := by
    simpa only [List.mem_cons, not_or] using outside
  have separateSize := separate.2
  simpa only [RuntimeReturnDataEffectsCorrespondence.patched, separate.1, separateSize.1, ↓reduceIte]
    using RuntimeLogEffectsCorrespondence.other_related
      (RuntimeAccountEffectsCorrespondence.runtime_related (RuntimeReturnDataEffectsCorrespondence.account_related related)) separateSize.2

theorem other_related {layout : Layout} {baseline : Nat → Option Core.Value} {slots : List EffectSlot}
    {image : Option (List UInt8)} {handlers : Handlers layout} {world : World}
    {state : Semantics.State RuntimeCallEffectsSemantics.State} {store : Core.Store}
    (related : StateRel (model layout baseline slots image handlers) world state store)
    {location : Nat} (outside : location ∉ mutable layout) :
    prefixRead layout.boundary store location = baseline location := by
  have separate : location ≠ layout.balances ∧ location ∉ layout.returnData :: layout.returnDataSize :: RuntimeLogEffectsCorrespondence.mutable layout.toLogLayout := by
    simpa only [mutable, List.mem_cons, not_or] using outside
  simpa only [patched, separate.1, ↓reduceIte] using returnData_other (runtime_related related) separate.2

theorem runtime_updated {layout : Layout} {baseline : Nat → Option Core.Value} {slots : List EffectSlot}
    {image : Option (List UInt8)} {handlers : Handlers layout} {world : World}
    {state : Semantics.State RuntimeCallEffectsSemantics.State} {initial final : Core.Store}
    {runtime : RuntimeReturnDataEffectsSemantics.State}
    (before : StateRel (model layout baseline slots image handlers) world state initial)
    (after : StateRel (RuntimeReturnDataEffectsCorrespondence.model layout.toReturnDataLayout
      (patched layout baseline state.external) slots image) world {sourceRuntime state with external := runtime} final)
    (balances : runtime.runtime.balances = state.external.runtime.runtime.balances) :
    StateRel (model layout baseline slots image handlers) world {state with external := {state.external with runtime := runtime}} final := by
  have patchEqual : patched layout baseline {state.external with runtime := runtime} = patched layout baseline state.external := by
    funext location
    simp only [patched, balances]
  have retained (location : Nat) (member : location ∈ [layout.callDepth, layout.callHandler, layout.dispatcher, layout.storage.address]) :
      prefixRead layout.boundary final location = prefixRead layout.boundary initial location := by
    have separated : location ≠ layout.balances ∧ location ∉ layout.returnData :: layout.returnDataSize :: RuntimeLogEffectsCorrespondence.mutable layout.toLogLayout := by
      simpa only [mutable, List.mem_cons, not_or] using call_separation layout location member
    rw [returnData_other after separated.2, other_related before (call_separation layout location member)]
    simp only [patched, separated.1, ↓reduceIte]
  refine ⟨after.toHeapRel, after.external.1, after.external.2.1, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [patchEqual]
    exact after.external.2.2
  · rw [retained _ (by simp)]
    exact before.external.2.2.depth
  · rw [retained _ (by simp)]
    exact before.external.2.2.handler
  · rw [retained _ (by simp)]
    exact before.external.2.2.dispatcher
  · rw [retained _ (by simp)]
    exact before.external.2.2.source

theorem depth_related {layout : Layout} {baseline : Nat → Option Core.Value} {slots : List EffectSlot}
    {image : Option (List UInt8)} {handlers : Handlers layout} {world : World}
    {state : Semantics.State RuntimeCallEffectsSemantics.State} {store : Core.Store}
    (related : StateRel (model layout baseline slots image handlers) world state store) :
    store.read? layout.callDepth = some (.word state.external.callDepth) := by
  simpa only [prefixRead, layout.depthBelow, ↓reduceIte] using related.external.2.2.depth

theorem installed {layout : Layout} {baseline : Nat → Option Core.Value} {slots : List EffectSlot}
    {image : Option (List UInt8)} {handlers : Handlers layout} {world : World}
    {state : Semantics.State RuntimeCallEffectsSemantics.State} {store : Core.Store}
    (related : StateRel (model layout baseline slots image handlers) world state store) :
    Nonempty (AccountCallCorrespondence.InstalledHandlers (sharedLocations layout)
      state.external.runtime.runtime.runtime.runtime.runtime.storage.address layout.callHandler layout.dispatcher store) := by
  have old := RuntimeEffectsCorrespondence.storage_related
    (RuntimeEnvironmentEffectsCorrespondence.runtime_related
    (RuntimeLogEffectsCorrespondence.runtime_related
    (RuntimeAccountEffectsCorrespondence.runtime_related (account_related related))))
  have sourceRead : store.read? layout.storage.address = some (.word handlers.source) := by
    simpa only [prefixRead, layout.below layout.storage.address (by simp [StorageBuiltinCorrespondence.Locations.all]), ↓reduceIte]
      using related.external.2.2.source
  have sourceEqual : state.external.runtime.runtime.runtime.runtime.runtime.storage.address = handlers.source :=
    Core.Value.word.inj (Option.some.inj (old.address.symm.trans sourceRead))
  rw [sourceEqual]
  refine ⟨⟨handlers.dispatchValue, handlers.handlerValue, handlers.dispatch, handlers.handler, ?_, ?_⟩⟩
  · simpa only [prefixRead, layout.dispatcherBelow, ↓reduceIte] using related.external.2.2.dispatcher
  · simpa only [prefixRead, layout.handlerBelow, ↓reduceIte] using related.external.2.2.handler

theorem initial_state {layout : Layout} {slots : List EffectSlot} {state : RuntimeCallEffectsSemantics.State}
    {store : Core.Store} {image : Option (List UInt8)} {handlers : Handlers layout}
    (runtime : StateRel (RuntimeReturnDataEffectsCorrespondence.model layout.toReturnDataLayout
      (prefixRead layout.boundary store) slots image) [] ⟨[], state.runtime⟩ store)
    (depth : store.read? layout.callDepth = some (.word state.callDepth))
    (dispatchRead : store.read? layout.dispatcher = some (.inRight .unit handlers.dispatchValue))
    (handlerRead : store.read? layout.callHandler = some (.inRight .unit handlers.handlerValue))
    (source : state.runtime.runtime.runtime.runtime.runtime.storage.address = handlers.source) :
    StateRel (model layout (prefixRead layout.boundary store) slots image handlers) [] ⟨[], state⟩ store := by
  have account := RuntimeReturnDataEffectsCorrespondence.account_related runtime
  have balances := RuntimeAccountEffectsCorrespondence.balances_related account
  change store.read? layout.balances = some (Core.WordMapping.encode state.runtime.runtime.balances) at balances
  have patchEqual : patched layout (prefixRead layout.boundary store) state = prefixRead layout.boundary store := by
    funext location
    unfold patched
    split
    · subst location
      simpa only [prefixRead, layout.balancesBelow, ↓reduceIte] using balances.symm
    · rfl
  refine ⟨runtime.toHeapRel, runtime.external.1, runtime.external.2.1, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [patchEqual]
    exact runtime.external.2.2
  · simpa only [prefixRead, layout.depthBelow, ↓reduceIte] using depth
  · simpa only [prefixRead, layout.handlerBelow, ↓reduceIte] using handlerRead
  · simpa only [prefixRead, layout.dispatcherBelow, ↓reduceIte] using dispatchRead
  · have storage := RuntimeEffectsCorrespondence.storage_related
      (RuntimeEnvironmentEffectsCorrespondence.runtime_related
      (RuntimeLogEffectsCorrespondence.runtime_related (RuntimeAccountEffectsCorrespondence.runtime_related account)))
    have found := storage.address
    change store.read? layout.storage.address = some (.word state.runtime.runtime.runtime.runtime.runtime.storage.address) at found
    simpa only [prefixRead, layout.below layout.storage.address (by simp [StorageBuiltinCorrespondence.Locations.all]), ↓reduceIte, source] using found

end Solcore.Frontend.RustHull.RuntimeCallEffectsCorrespondence
