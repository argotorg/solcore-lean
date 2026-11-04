import Solcore.Frontend.RustHull.Internal.CallLayout
import Solcore.Frontend.RustHull.Internal.CallTransport
import Solcore.Frontend.RustHull.Internal.AccountCalls
import Solcore.Frontend.RustHull.ContractCodeTheorems
import Solcore.Frontend.RustHull.Internal.LinkedWorld
import Solcore.Frontend.RustHull.Semantics.Frames
import Solcore.Frontend.RustHull.Internal.Creation
import Solcore.Frontend.RustHull.Internal.TerminationLayers

/-!
# Call states

The resources and updates of the call layers, and their installed callbacks.
-/

section
-- leanmerge: from Solcore.Frontend.RustHull.RuntimeCallResourcesCorrespondence
/-! The caller's four writable cells and the shared account cells are extracted
from the full runtime model. Frame rules retain everything outside those cells. -/
set_option autoImplicit false
set_option linter.unusedSimpArgs false
namespace Solcore.Frontend.RustHull.RuntimeCallEffectsCorrespondence
open Correspondence

abbrev LocalLocations := CallTransportCorrespondence.Locations

def localLocations (layout : Layout) : LocalLocations :=
  ⟨layout.memory, layout.storage.memorySize, layout.returnData, layout.returnDataSize⟩

def callMutable (layout : Layout) : List Nat :=
  [layout.memory, layout.storage.memorySize, layout.returnData, layout.returnDataSize,
    layout.storage.world, layout.logs, layout.logSize, layout.balances]

structure CallPassive (layout : Layout) (slots : List EffectSlot) : Prop where
  code : ∀ cells, layout.codeCells = some cells →
    cells.code ∉ callMutable layout ∧ cells.known ∉ callMutable layout
  size : ∀ slot ∈ slots, slot.name = "returnDataSize" → slot.type = .word → slot.location = layout.returnDataSize
  other : ∀ slot ∈ slots, slot.name ≠ "returnDataSize" → ∀ state value,
    EnvironmentBuiltinCorrespondence.observation state slot.name slot.type = some value → slot.location ∉ callMutable layout

theorem local_related {layout : Layout} {baseline : Nat → Option Core.Value} {slots : List EffectSlot}
    {image : Option (List UInt8)} {handlers : Handlers layout} {world : World}
    {state : Semantics.State RuntimeCallEffectsSemantics.State} {store : Core.Store}
    (related : StateRel (model layout baseline slots image handlers) world state store) :
    CallTransportCorrespondence.StateRel (localLocations layout) (RuntimeCallEffectsSemantics.transport state.external) store := by
  have runtime := RuntimeEffectsCorrespondence.memory_related
    (RuntimeEnvironmentEffectsCorrespondence.runtime_related
    (RuntimeLogEffectsCorrespondence.runtime_related
    (RuntimeAccountEffectsCorrespondence.runtime_related (account_related related))))
  refine ⟨?_, runtime.memory, runtime.size,
    RuntimeReturnDataEffectsCorrespondence.data_related (runtime_related related),
    RuntimeReturnDataEffectsCorrespondence.size_related (runtime_related related)⟩
  have distinct := layout.callDistinct
  simp only [StorageBuiltinCorrespondence.Locations.all, List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at distinct
  simp only [localLocations, CallTransportCorrespondence.Locations.resources, LogsCorrespondence.Locations.all,
    List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or]
  simp_all [ne_comm]

theorem shared_related {layout : Layout} {baseline : Nat → Option Core.Value} {slots : List EffectSlot}
    {image : Option (List UInt8)} {handlers : Handlers layout} {world : World}
    {state : Semantics.State RuntimeCallEffectsSemantics.State} {store : Core.Store}
    (related : StateRel (model layout baseline slots image handlers) world state store) :
    AccountCallCorrespondence.SharedStateRel (sharedLocations layout) (RuntimeCallEffectsSemantics.shared state.external) store := by
  have account := account_related related
  have logs := RuntimeAccountEffectsCorrespondence.runtime_related account
  have logState := RuntimeLogEffectsCorrespondence.logs_related logs
  have runtime := RuntimeEffectsCorrespondence.storage_related
    (RuntimeEnvironmentEffectsCorrespondence.runtime_related (RuntimeLogEffectsCorrespondence.runtime_related logs))
  refine ⟨runtime.world, logState.logs.logs, logState.logs.logSize,
    RuntimeAccountEffectsCorrespondence.balances_related account, runtime.complete, ?_⟩
  have distinct := layout.callDistinct
  simp only [StorageBuiltinCorrespondence.Locations.all, List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at distinct
  simp only [sharedLocations, AccountCallCorrespondence.SharedLocations.all,
    List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or]
  simp_all [ne_comm]

structure Frame (layout : Layout) (initial final : Core.Store) : Prop where
  length_le : initial.length ≤ final.length
  read : ∀ location value, location ∉ callMutable layout → initial.read? location = some value → final.read? location = some value

theorem Frame.refl (layout : Layout) (store : Core.Store) : Frame layout store store :=
  ⟨Nat.le_refl _, fun _ _ _ found => found⟩

theorem Frame.trans {layout : Layout} {first second third : Core.Store}
    (left : Frame layout first second) (right : Frame layout second third) : Frame layout first third :=
  ⟨Nat.le_trans left.length_le right.length_le,
    fun location value outside found => right.read location value outside (left.read location value outside found)⟩

theorem Frame.of_local {layout : Layout} {initial final : Core.Store}
    (frame : CallTransportCorrespondence.Frame (localLocations layout) initial final) : Frame layout initial final := by
  refine ⟨frame.length, ?_⟩
  intro location value outside found
  apply frame.read location value _ found
  intro member
  apply outside
  simp only [localLocations, CallTransportCorrespondence.Locations.resources, LogsCorrespondence.Locations.all,
    List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl <;> simp [callMutable]

theorem mutable_below (layout : Layout) {location : Nat} (member : location ∈ callMutable layout) :
    location < layout.boundary := by
  simp only [callMutable, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact layout.below _ (by simp)
  · exact layout.below _ (by simp [StorageBuiltinCorrespondence.Locations.all])
  · exact layout.dataBelow
  · exact layout.sizeBelow
  · exact layout.below _ (by simp [StorageBuiltinCorrespondence.Locations.all])
  · exact layout.logsBelow
  · exact layout.logSizeBelow
  · exact layout.balancesBelow

theorem Frame.above {layout : Layout} {initial final : Core.Store} (frame : Frame layout initial final) :
    StoreRetainsFrom layout.boundary initial final := by
  refine ⟨frame.length_le, ?_⟩
  intro location above below
  have outside : location ∉ callMutable layout := fun member => Nat.not_lt_of_ge above (mutable_below layout member)
  exact (frame.read location _ outside (List.getElem?_eq_getElem below)).trans (List.getElem?_eq_getElem below).symm

theorem call_fixed_separation (layout : Layout) :
    ∀ location ∈ [layout.callDepth, layout.callHandler, layout.dispatcher, layout.storage.address,
      layout.storage.isStatic, layout.storage.exit, layout.storage.returnOffset, layout.storage.returnSize],
      location ∉ callMutable layout := by
  have distinct := layout.callDistinct
  simp only [StorageBuiltinCorrespondence.Locations.all, List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at distinct
  intro location member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp only [callMutable, List.mem_cons, List.not_mem_nil, or_false, not_or]
  all_goals simp_all [ne_comm]

end Solcore.Frontend.RustHull.RuntimeCallEffectsCorrespondence
end

section
-- leanmerge: from Solcore.Frontend.RustHull.RuntimeCallUpdateCorrespondence
/-! Rebuild the full caller model from real transport and shared-state reads.
Only returnDataSize changes among the caller's environment observations. -/
set_option autoImplicit false
set_option linter.unusedSimpArgs false
namespace Solcore.Frontend.RustHull.RuntimeCallEffectsCorrespondence
open Correspondence

private theorem observation_after {state : RuntimeCallEffectsSemantics.State}
    {next : CallTransportSemantics.State} {shared : AccountCallSemantics.Shared}
    {name : String} {type : Core.Ty} (different : name ≠ "returnDataSize") :
    EnvironmentBuiltinCorrespondence.observation
      (RuntimeCallEffectsSemantics.withTransport state next shared).runtime.runtime.runtime.runtime.environment name type =
    EnvironmentBuiltinCorrespondence.observation state.runtime.runtime.runtime.runtime.environment name type := by
  unfold EnvironmentBuiltinCorrespondence.observation
  split <;> simp_all [RuntimeCallEffectsSemantics.withTransport, RuntimeCallEffectsSemantics.withReturned,
    RuntimeCallEffectsSemantics.withShared]

theorem transport_updated {layout : Layout} {baseline : Nat → Option Core.Value} {slots : List EffectSlot}
    {image : Option (List UInt8)} {handlers : Handlers layout} {world : World}
    {state : Semantics.State RuntimeCallEffectsSemantics.State} {initial final : Core.Store}
    {next : CallTransportSemantics.State} {shared : AccountCallSemantics.Shared}
    (passive : CallPassive layout slots)
    (before : StateRel (model layout baseline slots image handlers) world state initial)
    (localAfter : CallTransportCorrespondence.StateRel (localLocations layout) next final)
    (sharedAfter : AccountCallCorrespondence.SharedStateRel (sharedLocations layout) shared final)
    (frame : Frame layout initial final) :
    StateRel (model layout baseline slots image handlers) world
      {state with external := RuntimeCallEffectsSemantics.withTransport state.external next shared} final := by
  have beforeRuntime := runtime_related before
  have beforeAccount := RuntimeReturnDataEffectsCorrespondence.account_related beforeRuntime
  have beforeLog := RuntimeAccountEffectsCorrespondence.runtime_related beforeAccount
  have beforeEnvironment := RuntimeLogEffectsCorrespondence.runtime_related beforeLog
  have beforeCore := RuntimeEnvironmentEffectsCorrespondence.runtime_related beforeEnvironment
  have storageBefore := RuntimeEffectsCorrespondence.storage_related beforeCore
  have pref {location : Nat} {value : Core.Value} (below : location < layout.boundary)
      (found : final.read? location = some value) : prefixRead layout.boundary final location = some value := by
    simpa only [prefixRead, below, ↓reduceIte] using found
  have retained (location : Nat) (outside : location ∉ callMutable layout) :
      prefixRead layout.boundary final location = prefixRead layout.boundary initial location := by
    by_cases below : location < layout.boundary
    · have bounded := Nat.lt_of_lt_of_le below before.external.1
      simpa only [prefixRead, below, ↓reduceIte, Core.Store.read?] using
        (frame.read location _ outside (List.getElem?_eq_getElem bounded)).trans (List.getElem?_eq_getElem bounded).symm
    · simp only [prefixRead, below, ↓reduceIte]
  apply before.cutoff_effect frame.above
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨⟨⟨⟨?_, ?_⟩, ?_, ?_⟩, ?_⟩, ?_, ?_, ?_⟩
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · exact pref (layout.below _ (by simp)) localAfter.memory
      · exact pref (layout.below _ (by simp [StorageBuiltinCorrespondence.Locations.all])) localAfter.memorySize
      · obtain ⟨accounts, same, found⟩ := sharedAfter.world
        exact ⟨accounts, same, pref (layout.below _ (by simp [StorageBuiltinCorrespondence.Locations.all])) found⟩
      · exact pref (layout.below _ (by simp [StorageBuiltinCorrespondence.Locations.all]))
          (frame.read _ _ (call_fixed_separation layout _ (by simp)) storageBefore.address)
      · exact pref (layout.below _ (by simp [StorageBuiltinCorrespondence.Locations.all])) sharedAfter.complete
      · exact pref (layout.below _ (by simp [StorageBuiltinCorrespondence.Locations.all]))
          (frame.read _ _ (call_fixed_separation layout _ (by simp)) storageBefore.isStatic)
      · exact pref (layout.below _ (by simp [StorageBuiltinCorrespondence.Locations.all]))
          (frame.read _ _ (call_fixed_separation layout _ (by simp)) storageBefore.exit)
      · exact pref (layout.below _ (by simp [StorageBuiltinCorrespondence.Locations.all]))
          (frame.read _ _ (call_fixed_separation layout _ (by simp)) storageBefore.returnOffset)
      · exact pref (layout.below _ (by simp [StorageBuiltinCorrespondence.Locations.all]))
          (frame.read _ _ (call_fixed_separation layout _ (by simp)) storageBefore.returnSize)
      · intro location outside
        by_cases atLogs : location = layout.logs
        · subst location
          simpa only [RuntimeCallEffectsSemantics.withTransport, RuntimeCallEffectsSemantics.withReturned,
            RuntimeCallEffectsSemantics.withShared, CallTransportCorrespondence.resources, RuntimeLogEffectsCorrespondence.patched, ↓reduceIte]
            using pref layout.logsBelow sharedAfter.logs
        by_cases atLogSize : location = layout.logSize
        · subst location
          simpa only [RuntimeCallEffectsSemantics.withTransport, RuntimeCallEffectsSemantics.withReturned,
            RuntimeCallEffectsSemantics.withShared, CallTransportCorrespondence.resources, RuntimeLogEffectsCorrespondence.patched, atLogs, ↓reduceIte]
            using pref layout.logSizeBelow sharedAfter.logSize
        by_cases atData : location = layout.returnData
        · subst location
          simpa only [RuntimeCallEffectsSemantics.withTransport, RuntimeCallEffectsSemantics.withReturned,
            RuntimeCallEffectsSemantics.withShared, CallTransportCorrespondence.resources, RuntimeLogEffectsCorrespondence.patched, RuntimeReturnDataEffectsCorrespondence.patched,
            atLogs, atLogSize, ↓reduceIte] using pref layout.dataBelow localAfter.logs
        by_cases atSize : location = layout.returnDataSize
        · subst location
          simpa only [RuntimeCallEffectsSemantics.withTransport, RuntimeCallEffectsSemantics.withReturned,
            RuntimeCallEffectsSemantics.withShared, CallTransportCorrespondence.resources, RuntimeLogEffectsCorrespondence.patched, RuntimeReturnDataEffectsCorrespondence.patched,
            atLogs, atLogSize, atData, ↓reduceIte, RuntimeReturnDataEffectsSemantics.size,
            RuntimeCallEffectsSemantics.withTransport, RuntimeCallEffectsSemantics.withReturned,
            RuntimeCallEffectsSemantics.withShared] using pref layout.sizeBelow localAfter.logSize
        by_cases atBalance : location = layout.balances
        · subst location
          simpa only [RuntimeCallEffectsSemantics.withTransport, RuntimeCallEffectsSemantics.withReturned,
            RuntimeCallEffectsSemantics.withShared, CallTransportCorrespondence.resources, RuntimeLogEffectsCorrespondence.patched, RuntimeReturnDataEffectsCorrespondence.patched, patched,
            atLogs, atLogSize, atData, atSize, ↓reduceIte] using pref layout.balancesBelow sharedAfter.balances
        have oldOutside : location ∉ mutable layout := by
          simpa only [mutable, RuntimeLogEffectsCorrespondence.mutable, List.mem_cons, not_or]
            using And.intro atBalance (And.intro atData (And.intro atSize (And.intro atLogs (And.intro atLogSize outside))))
        have callOutside : location ∉ callMutable layout := by
          simp only [RuntimeEffectsCorrespondence.mutable, StorageBuiltinCorrespondence.Locations.mutable,
            List.mem_append, List.mem_cons, List.not_mem_nil, or_false, not_or] at outside
          simp only [callMutable, List.mem_cons, List.not_mem_nil, or_false, not_or]
          exact ⟨outside.1.1, outside.1.2, atData, atSize, outside.2.1, atLogs, atLogSize, atBalance⟩
        simpa only [RuntimeCallEffectsSemantics.withTransport, RuntimeCallEffectsSemantics.withReturned,
            RuntimeCallEffectsSemantics.withShared, CallTransportCorrespondence.resources, RuntimeLogEffectsCorrespondence.patched, RuntimeReturnDataEffectsCorrespondence.patched, patched,
          atLogs, atLogSize, atData, atSize, atBalance, ↓reduceIte] using
          (retained location callOutside).trans (other_related before oldOutside)
    · intro slot member value observed
      by_cases isSize : slot.name = "returnDataSize"
      · cases typed : slot.type <;> simp only [isSize, typed, EnvironmentBuiltinCorrespondence.observation] at observed
        all_goals try contradiction
        cases Option.some.inj observed
        have located := passive.size slot member isSize typed
        rw [located]
        exact pref layout.sizeBelow localAfter.logSize
      · have oldObservation := (observation_after (state := state.external) (next := next) (shared := shared) isSize).symm.trans observed
        have observedBefore := beforeEnvironment.external.2.2.2 slot member value oldObservation
        rw [retained slot.location (passive.other slot member isSize _ _ oldObservation)]
        exact observedBefore
    · exact pref layout.logsBelow sharedAfter.logs
    · exact pref layout.logSizeBelow sharedAfter.logSize
    · exact pref layout.balancesBelow sharedAfter.balances
    · exact pref layout.dataBelow localAfter.logs
    · simpa only [RuntimeReturnDataEffectsSemantics.size, RuntimeCallEffectsSemantics.withTransport,
        RuntimeCallEffectsSemantics.withReturned, RuntimeCallEffectsSemantics.withShared, CallTransportCorrespondence.resources, ↓reduceIte]
        using pref layout.sizeBelow localAfter.logSize
    · intro cells present
      obtain ⟨code, known⟩ := RuntimeReturnDataEffectsCorrespondence.code_related beforeRuntime present
      exact ⟨pref cells.codeBelow (frame.read _ _ (passive.code cells present).1 code),
        pref cells.knownBelow (frame.read _ _ (passive.code cells present).2 known)⟩
  · rw [retained _ (call_fixed_separation layout _ (by simp))]
    exact before.external.2.2.depth
  · rw [retained _ (call_fixed_separation layout _ (by simp))]
    exact before.external.2.2.handler
  · rw [retained _ (call_fixed_separation layout _ (by simp))]
    exact before.external.2.2.dispatcher
  · rw [retained _ (call_fixed_separation layout _ (by simp))]
    exact before.external.2.2.source

end Solcore.Frontend.RustHull.RuntimeCallEffectsCorrespondence
end

section
-- leanmerge: from Solcore.Frontend.RustHull.RuntimeCallTransportModel
/-! The transport callback model uses actual shared-account reads and installed
optional-cell values. It can be instantiated without assuming callback behavior. -/
set_option autoImplicit false
set_option linter.unusedSimpArgs false
namespace Solcore.Frontend.RustHull.RuntimeCallEffectsCorrespondence
open Correspondence

def SharedResources (layout : Layout) (handlers : Handlers layout)
    (shared : AccountCallSemantics.Shared) (store : Core.Store) : Prop :=
  AccountCallCorrespondence.SharedStateRel (sharedLocations layout) shared store ∧
  store.read? layout.callHandler = some (.inRight .unit handlers.handlerValue) ∧
  store.read? layout.dispatcher = some (.inRight .unit handlers.dispatchValue)

theorem shared_local_separation (layout : Layout) :
    ∀ location ∈ [layout.storage.world, layout.logs, layout.logSize, layout.balances, layout.storage.complete,
      layout.callHandler, layout.dispatcher],
      location ∉ (localLocations layout).resources.all := by
  have distinct := layout.callDistinct
  simp only [StorageBuiltinCorrespondence.Locations.all, List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at distinct
  intro location member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp only [localLocations, CallTransportCorrespondence.Locations.resources,
    LogsCorrespondence.Locations.all, List.mem_cons, List.not_mem_nil, or_false, not_or]
  all_goals simp_all [ne_comm]

def transportModel (layout : Layout) (handlers : Handlers layout) :
    CallTransportCorrespondence.Model AccountCallSemantics.Shared (localLocations layout) where
  related := SharedResources layout handlers
  frame := by
    intro shared initial final frame related
    have preserved (location : Nat) (value : Core.Value)
        (member : location ∈ [layout.storage.world, layout.logs, layout.logSize, layout.balances, layout.storage.complete,
          layout.callHandler, layout.dispatcher]) (found : initial.read? location = some value) :
        final.read? location = some value := frame.read location value (shared_local_separation layout location member) found
    refine ⟨⟨?_, ?_, ?_, ?_, ?_, related.1.distinct⟩, ?_, ?_⟩
    · obtain ⟨accounts, same, found⟩ := related.1.world
      exact ⟨accounts, same, preserved _ _ (by simp [sharedLocations]) found⟩
    · exact preserved _ _ (by simp [sharedLocations]) related.1.logs
    · exact preserved _ _ (by simp [sharedLocations]) related.1.logSize
    · exact preserved _ _ (by simp [sharedLocations]) related.1.balances
    · exact preserved _ _ (by simp [sharedLocations]) related.1.complete
    · exact preserved _ _ (by simp) related.2.1
    · exact preserved _ _ (by simp) related.2.2
  retains := Frame layout
  retainedFrame := Frame.of_local
  retainedTrans := Frame.trans

theorem shared_resources {layout : Layout} {baseline : Nat → Option Core.Value} {slots : List EffectSlot}
    {image : Option (List UInt8)} {handlers : Handlers layout} {world : World}
    {state : Semantics.State RuntimeCallEffectsSemantics.State} {store : Core.Store}
    (related : StateRel (model layout baseline slots image handlers) world state store) :
    SharedResources layout handlers (RuntimeCallEffectsSemantics.shared state.external) store := by
  refine ⟨shared_related related, ?_, ?_⟩
  · simpa only [prefixRead, layout.handlerBelow, ↓reduceIte] using related.external.2.2.handler
  · simpa only [prefixRead, layout.dispatcherBelow, ↓reduceIte] using related.external.2.2.dispatcher

theorem SharedResources.installed {layout : Layout} {handlers : Handlers layout}
    {shared : AccountCallSemantics.Shared} {store : Core.Store}
    (related : SharedResources layout handlers shared store) :
    Nonempty (AccountCallCorrespondence.InstalledHandlers (sharedLocations layout) handlers.source
      layout.callHandler layout.dispatcher store) :=
  ⟨⟨handlers.dispatchValue, handlers.handlerValue, handlers.dispatch, handlers.handler, related.2.2, related.2.1⟩⟩

theorem source_eq {layout : Layout} {baseline : Nat → Option Core.Value} {slots : List EffectSlot}
    {image : Option (List UInt8)} {handlers : Handlers layout} {world : World}
    {state : Semantics.State RuntimeCallEffectsSemantics.State} {store : Core.Store}
    (related : StateRel (model layout baseline slots image handlers) world state store) :
    state.external.runtime.runtime.runtime.runtime.runtime.storage.address = handlers.source := by
  have old := RuntimeEffectsCorrespondence.storage_related
    (RuntimeEnvironmentEffectsCorrespondence.runtime_related
    (RuntimeLogEffectsCorrespondence.runtime_related
    (RuntimeAccountEffectsCorrespondence.runtime_related (account_related related))))
  have sourceRead : store.read? layout.storage.address = some (.word handlers.source) := by
    simpa only [prefixRead, layout.below layout.storage.address (by simp [StorageBuiltinCorrespondence.Locations.all]), ↓reduceIte]
      using related.external.2.2.source
  exact Core.Value.word.inj (Option.some.inj (old.address.symm.trans sourceRead))

end Solcore.Frontend.RustHull.RuntimeCallEffectsCorrespondence
end

section
-- leanmerge: from Solcore.Frontend.RustHull.RuntimeCallCallbackCorrespondence
/-! The caller transport uses the actual installed dispatcher and frame callback.
Their concrete bodies discharge the callback interface at call-tree height zero. -/
set_option autoImplicit false
set_option linter.unusedSimpArgs false
namespace Solcore.Frontend.RustHull.RuntimeCallEffectsCorrespondence
open Core Correspondence

theorem callback_preserves (layout : Layout) (handlers : Handlers layout) :
    CallTransportCorrespondence.CallbackPreservation (transportModel layout handlers)
      (AccountCallSemantics.Dispatch AccountCallSemantics.noChildren .ordinary handlers.source)
      handlers.handlerValue := by
  intro request shared finalShared result computed state environment store function argument sharedRelated localRelated resolved supplied
  obtain ⟨target, final, evaluated, resultRelated, finalSharedRelated, frame⟩ :=
    handlers.handler.apply_preserves handlers.dispatch computed sharedRelated.1 sharedRelated.2.2 resolved supplied
  have different : ∀ location ∈ [layout.memory, layout.storage.memorySize, layout.returnData,
      layout.returnDataSize, layout.callHandler, layout.dispatcher], location ≠ layout.balances := by
    have distinct := layout.callDistinct
    simp only [StorageBuiltinCorrespondence.Locations.all, List.nodup_cons, List.mem_cons,
      List.not_mem_nil, or_false, not_or] at distinct
    intro location member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all [ne_comm]
  have keep {location : Nat} {value : Core.Value}
      (member : location ∈ [layout.memory, layout.storage.memorySize, layout.returnData,
        layout.returnDataSize, layout.callHandler, layout.dispatcher])
      (found : store.read? location = some value) : final.read? location = some value :=
    (frame.other location (different location member) (List.getElem?_eq_some_iff.mp found).1).trans found
  refine ⟨target, final, resultRelated, evaluated,
    ⟨localRelated.distinct, keep (by simp [localLocations, CallTransportCorrespondence.Locations.resources]) localRelated.memory,
      keep (by simp [localLocations, CallTransportCorrespondence.Locations.resources]) localRelated.memorySize,
      keep (by simp [localLocations, CallTransportCorrespondence.Locations.resources]) localRelated.logs,
      keep (by simp [localLocations, CallTransportCorrespondence.Locations.resources]) localRelated.logSize⟩,
    ⟨finalSharedRelated, keep (by simp) sharedRelated.2.1, keep (by simp) sharedRelated.2.2⟩,
    frame.length_le, ?_⟩
  intro location value outside found
  have notBalance : location ≠ layout.balances := fun same => outside (by simp [callMutable, same])
  exact (frame.other location notBalance (List.getElem?_eq_some_iff.mp found).1).trans found

theorem frame_closures {layout : Layout} {baseline : Nat → Option Core.Value} {slots : List EffectSlot}
    {image : Option (List UInt8)} {handlers : Handlers layout} {world : World}
    {state : Semantics.State RuntimeCallEffectsSemantics.State} {initial final : Store}
    (related : StateRel (model layout baseline slots image handlers) world state initial)
    (frame : Frame layout initial final) : ClosuresPreserved initial final := by
  have callerRelated := local_related related
  have shared := shared_related related
  intro location parameter result body captured found
  apply frame.read location _ _ found
  intro member
  simp only [callMutable, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have same := Option.some.inj (callerRelated.memory.symm.trans found)
    cases entries : state.external.runtime.runtime.runtime.runtime.runtime.memory.words <;>
      simp only [localLocations, CallTransportCorrespondence.resources, RuntimeCallEffectsSemantics.transport, entries, WordMapping.encode] at same <;> cases same
  · have same := Option.some.inj (callerRelated.memorySize.symm.trans found); cases same
  · have same := Option.some.inj (callerRelated.logs.symm.trans found)
    cases entries : state.external.runtime.returnData <;>
      simp only [localLocations, CallTransportCorrespondence.resources, RuntimeCallEffectsSemantics.transport, entries, WordMapping.encode] at same <;> cases same
  · have same := Option.some.inj (callerRelated.logSize.symm.trans found); cases same
  · obtain ⟨accounts, _, stored⟩ := shared.world
    have same := Option.some.inj (stored.symm.trans found)
    cases accounts <;> simp only [StorageCorrespondence.world] at same <;> cases same
  · have same := Option.some.inj (shared.logs.symm.trans found)
    cases entries : (RuntimeCallEffectsSemantics.shared state.external).logs <;>
      simp only [entries, WordMapping.encode] at same <;> cases same
  · have same := Option.some.inj (shared.logSize.symm.trans found); cases same
  · have same := Option.some.inj (shared.balances.symm.trans found)
    cases entries : (RuntimeCallEffectsSemantics.shared state.external).balances <;>
      simp only [entries, WordMapping.encode] at same <;> cases same

end Solcore.Frontend.RustHull.RuntimeCallEffectsCorrespondence
end

section
-- leanmerge: from Solcore.Frontend.RustHull.RuntimeCallInitializedEffects
/-! Named cells from the actual frame allocator supply the call layout, depth,
handler capture and location separation. The dispatcher is an earlier cell. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.RuntimeCallInitializedEffects
open Correspondence ScalarExecution RuntimeInitializedEffects ContractCallCorrespondence

abbrev Base := RuntimeReturnDataEffectsCorrespondence.Layout

def baseSlots (base : Base) : List EffectSlot :=
  [⟨"balances", Core.WordMapping.type, base.balances⟩,
   ⟨"returnData", Core.WordMapping.type, base.returnData⟩,
   ⟨"returnDataSize", .word, base.returnDataSize⟩,
   ⟨"logs", Core.WordMapping.type, base.logs⟩,
   ⟨"logSize", .word, base.logSize⟩,
   ⟨"memory", Core.WordMapping.type, base.memory⟩,
   ⟨"world", AccountState.type, base.storage.world⟩,
   ⟨"address", .word, base.storage.address⟩,
   ⟨"worldComplete", .bool, base.storage.complete⟩,
   ⟨"isStatic", .bool, base.storage.isStatic⟩,
   ⟨"exit", .word, base.storage.exit⟩,
   ⟨"returnOffset", .word, base.storage.returnOffset⟩,
   ⟨"returnSize", .word, base.storage.returnSize⟩,
   ⟨"memorySize", .word, base.storage.memorySize⟩]

structure Ready (base : Base) (cells : List InitializedCell) (store : Core.Store)
    (depth : Core.Word) (source : Core.Word) (dispatcherLocation : Nat) where
  layout : RuntimeCallEffectsCorrespondence.Layout
  baseEqual : layout.toReturnDataLayout = base
  dispatcherEqual : layout.dispatcher = dispatcherLocation
  depthMember : ⟨"callDepth", .word, layout.callDepth⟩ ∈ cells.map InitializedCell.effectSlot
  handlerMember : ⟨"callHandler", Core.OptionalCell.cellType Calls.callbackType, layout.callHandler⟩ ∈ cells.map InitializedCell.effectSlot
  depthRead : store.read? layout.callDepth = some (.word depth)
  handlerValue : Core.Value
  handlerRead : store.read? layout.callHandler = some (.inRight .unit handlerValue)
  handler : AccountCallCorrespondence.CallHandlerClosure source dispatcherLocation handlerValue

theorem ready {cells : List InitializedCell} {store : Core.Store}
    {extra : List (String × Core.Ty)} {base : Base} {depth source : Core.Word} {dispatcherLocation : Nat}
    (signature : cells.map (fun cell => (cell.name, cell.type)) = Effects.slots ++ extra)
    (initialized : InitializedCells cells store) (separate : CellLocations cells)
    (boundary : base.boundary = store.length)
    (members : ∀ slot ∈ baseSlots base, slot ∈ cells.map InitializedCell.effectSlot)
    (dispatcherBelow : dispatcherLocation < base.boundary)
    (dispatcherOutside : ∀ cell ∈ cells, cell.location ≠ dispatcherLocation)
    (depthObserved : ∀ cell ∈ cells, initializedDepth depth cell)
    (handlerObserved : ∀ cell ∈ cells, initializedHandler source dispatcherLocation cell) :
    Nonempty (Ready base cells store depth source dispatcherLocation) := by
  obtain ⟨depthCell⟩ := ContractReturnDataCorrespondence.observe_base signature initialized
    (name := "callDepth") (type := .word) (by simp [Effects.slots])
    (fun cell member named _ => depthObserved cell member named)
  have present : ("callHandler", Core.OptionalCell.cellType Calls.callbackType) ∈
      cells.map (fun cell => (cell.name, cell.type)) := by
    rw [signature]
    exact List.mem_append_left _ (by simp [Effects.slots])
  obtain ⟨handlerCell, handlerMember, handlerSame⟩ := List.mem_map.mp present
  obtain ⟨handlerName, handlerType⟩ := Prod.mk.inj handlerSame
  obtain ⟨handlerValue, handlerStored, ⟨handler⟩⟩ := handlerObserved handlerCell handlerMember handlerName
  have handlerSlot : (⟨"callHandler", Core.OptionalCell.cellType Calls.callbackType, handlerCell.location⟩ : EffectSlot)
      ∈ cells.map InitializedCell.effectSlot :=
    List.mem_map.mpr ⟨handlerCell, handlerMember, by simp only [InitializedCell.effectSlot, handlerName, handlerType]⟩
  let dispatchCell : InitializedCell :=
    ⟨"$dispatcher", Core.OptionalCell.cellType AccountRuntime.dispatchCallbackType, dispatcherLocation, .unit⟩
  let selected : List EffectSlot :=
    (baseSlots base).take 3 ++
    [⟨"callDepth", .word, depthCell.cell.location⟩,
     ⟨"callHandler", Core.OptionalCell.cellType Calls.callbackType, handlerCell.location⟩,
     dispatchCell.effectSlot] ++ (baseSlots base).drop 3
  have selectedIncluded : ∀ slot ∈ selected, slot ∈ (dispatchCell :: cells).map InitializedCell.effectSlot := by
    intro slot member
    simp only [selected, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with (member | rfl | rfl | rfl) | member
    · exact List.mem_cons_of_mem _ (members slot (List.mem_of_mem_take member))
    · exact List.mem_cons_of_mem _ depthCell.slot
    · exact List.mem_cons_of_mem _ handlerSlot
    · exact .head _
    · exact List.mem_cons_of_mem _ (members slot (List.mem_of_mem_drop member))
  have names : (selected.map EffectSlot.name).Nodup := by
    simp only [selected, baseSlots, dispatchCell, InitializedCell.effectSlot, List.take_succ_cons, List.take_zero, List.drop_succ_cons, List.drop_zero, List.map_cons, List.map_nil, List.cons_append, List.nil_append]
    decide
  have distinct := effectSlots_distinct (separate_dispatcher separate dispatcherOutside .unit) selectedIncluded names
  let layout : RuntimeCallEffectsCorrespondence.Layout := {
    toReturnDataLayout := base
    callDepth := depthCell.cell.location
    callHandler := handlerCell.location
    dispatcher := dispatcherLocation
    depthBelow := by rw [boundary]; exact initialized.location_bound depthCell.member
    handlerBelow := by rw [boundary]; exact initialized.location_bound handlerMember
    dispatcherBelow := dispatcherBelow
    callDistinct := distinct }
  exact ⟨layout, rfl, rfl, depthCell.slot, handlerSlot, depthCell.stored, handlerValue,
    by simpa only [handlerStored] using initialized handlerCell handlerMember, handler⟩

end Solcore.Frontend.RustHull.RuntimeCallInitializedEffects
end

section
-- leanmerge: from Solcore.Frontend.RustHull.RuntimeCallInitializedResources
/-! Actual named slots distinguish mutable caller and shared data from all
other environment observations, including optional code images. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.RuntimeCallInitializedEffects
open Correspondence ContractCallCorrespondence RuntimeCallEffectsCorrespondence

theorem base_members {cells : List InitializedCell} {store : Core.Store}
    {state : RuntimeEffectsSemantics.State} {runtime : RuntimeInitializedEffects.StateReady cells store state}
    {words : LogsSemantics.Words} {cursor : Core.Word} {logs : RuntimeLogInitializedEffects.Ready runtime words cursor}
    {balances : StorageSemantics.Words} {accounts : RuntimeAccountInitializedEffects.Ready logs balances}
    {withCode : Bool} {image : Option (List UInt8)} {data : MemorySemantics.Entries} {size : Core.Word}
    (ready : RuntimeReturnDataInitializedEffects.Ready accounts withCode image data size) :
    ∀ slot ∈ baseSlots ready.layout, slot ∈ cells.map InitializedCell.effectSlot := by
  intro slot member
  simp only [baseSlots, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first
    | exact ready.dataMember
    | exact ready.dataSizeMember
    | (simpa only [ready.base] using accounts.balancesMember)
    | (simpa only [ready.base, accounts.base] using logs.logsMember)
    | (simpa only [ready.base, accounts.base] using logs.logSizeMember)
    | (simpa only [ready.base, accounts.base, logs.base, RuntimeEffectsCorrespondence.initialLayout] using runtime.memoryMember)
    | (simpa only [ready.base, accounts.base, logs.base, RuntimeEffectsCorrespondence.initialLayout] using runtime.worldMember)
    | (simpa only [ready.base, accounts.base, logs.base, RuntimeEffectsCorrespondence.initialLayout] using runtime.addressMember)
    | (simpa only [ready.base, accounts.base, logs.base, RuntimeEffectsCorrespondence.initialLayout] using runtime.completeMember)
    | (simpa only [ready.base, accounts.base, logs.base, RuntimeEffectsCorrespondence.initialLayout] using runtime.staticMember)
    | (simpa only [ready.base, accounts.base, logs.base, RuntimeEffectsCorrespondence.initialLayout] using runtime.exitMember)
    | (simpa only [ready.base, accounts.base, logs.base, RuntimeEffectsCorrespondence.initialLayout] using runtime.offsetMember)
    | (simpa only [ready.base, accounts.base, logs.base, RuntimeEffectsCorrespondence.initialLayout] using runtime.returnSizeMember)
    | (simpa only [ready.base, accounts.base, logs.base, RuntimeEffectsCorrespondence.initialLayout] using runtime.sizeMember)

def mutableSlots (layout : Layout) : List EffectSlot :=
  [⟨"memory", Core.WordMapping.type, layout.memory⟩,
   ⟨"memorySize", .word, layout.storage.memorySize⟩,
   ⟨"returnData", Core.WordMapping.type, layout.returnData⟩,
   ⟨"returnDataSize", .word, layout.returnDataSize⟩,
   ⟨"world", AccountState.type, layout.storage.world⟩,
   ⟨"logs", Core.WordMapping.type, layout.logs⟩,
   ⟨"logSize", .word, layout.logSize⟩,
   ⟨"balances", Core.WordMapping.type, layout.balances⟩]

theorem call_passive {cells : List InitializedCell} {layout : Layout}
    (unique : (cells.map InitializedCell.name).Nodup) (separate : CellLocations cells)
    (members : ∀ slot ∈ baseSlots layout.toReturnDataLayout, slot ∈ cells.map InitializedCell.effectSlot)
    (codeMembers : ∀ code, layout.codeCells = some code →
      ⟨"code", Core.WordMapping.type, code.code⟩ ∈ cells.map InitializedCell.effectSlot ∧
      ⟨"codeKnown", .bool, code.known⟩ ∈ cells.map InitializedCell.effectSlot) :
    CallPassive layout (cells.map InitializedCell.effectSlot) := by
  have names : ∀ first ∈ cells.map InitializedCell.effectSlot, ∀ second ∈ cells.map InitializedCell.effectSlot,
      first.location = second.location → first.name = second.name := by
    intro first firstMember second secondMember same
    obtain ⟨left, leftMember, rfl⟩ := List.mem_map.mp firstMember
    obtain ⟨right, rightMember, rfl⟩ := List.mem_map.mp secondMember
    exact separate left leftMember right rightMember same
  have mutableMember : ∀ slot ∈ mutableSlots layout, slot ∈ cells.map InitializedCell.effectSlot := by
    intro slot member
    apply members slot
    simp only [mutableSlots, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [baseSlots]
  have mutableProjection : (mutableSlots layout).map EffectSlot.location = callMutable layout := rfl
  have outside : ∀ slot ∈ cells.map InitializedCell.effectSlot,
      slot.name ∉ ["memory", "memorySize", "returnData", "returnDataSize", "world", "logs", "logSize", "balances"] →
      slot.location ∉ callMutable layout := by
    intro slot member absent inside
    rw [← mutableProjection] at inside
    obtain ⟨other, otherMember, same⟩ := List.mem_map.mp inside
    have named := names slot member other (mutableMember other otherMember) same.symm
    apply absent
    rw [named]
    have present := List.mem_map_of_mem (f := EffectSlot.name) otherMember
    exact present
  refine ⟨?_, ?_, ?_⟩
  · intro code present
    obtain ⟨codeMember, knownMember⟩ := codeMembers code present
    exact ⟨outside _ codeMember (by simp), outside _ knownMember (by simp)⟩
  · intro slot member named _
    exact named_slot_location unique member
      (members ⟨"returnDataSize", .word, layout.returnDataSize⟩ (by simp [baseSlots])) named
  · intro slot member different state value observed inside
    rw [← mutableProjection] at inside
    obtain ⟨other, otherMember, same⟩ := List.mem_map.mp inside
    have named := names slot member other (mutableMember other otherMember) same.symm
    simp only [mutableSlots, List.mem_cons, List.not_mem_nil, or_false] at otherMember
    rcases otherMember with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | exact different named
      | (rw [named] at observed; cases slot.type <;> contradiction)

theorem shared_cells {cells sharedCells : List InitializedCell} {base : Base}
    (members : ∀ slot ∈ baseSlots base, slot ∈ cells.map InitializedCell.effectSlot)
    (origin : ∀ cell ∈ cells, sharedOrigin sharedCells cell) :
    SharedCells sharedCells ⟨base.storage.world, base.logs, base.logSize, base.balances, base.storage.complete⟩ := by
  have selected : ∀ slot ∈ baseSlots base, slot.name ∈ dispatchSharedNames →
      ∃ cell ∈ sharedCells, cell.name = slot.name ∧ cell.reference = .cellRef slot.type slot.location := by
    intro slot member named
    obtain ⟨cell, cellMember, rfl⟩ := List.mem_map.mp (members slot member)
    exact ⟨cell, origin cell cellMember named, rfl, rfl⟩
  exact ⟨selected ⟨"world", AccountState.type, base.storage.world⟩ (by simp [baseSlots]) (by simp [dispatchSharedNames]),
    selected ⟨"logs", Core.WordMapping.type, base.logs⟩ (by simp [baseSlots]) (by simp [dispatchSharedNames]),
    selected ⟨"logSize", .word, base.logSize⟩ (by simp [baseSlots]) (by simp [dispatchSharedNames]),
    selected ⟨"balances", Core.WordMapping.type, base.balances⟩ (by simp [baseSlots]) (by simp [dispatchSharedNames]),
    selected ⟨"worldComplete", .bool, base.storage.complete⟩ (by simp [baseSlots]) (by simp [dispatchSharedNames])⟩

end Solcore.Frontend.RustHull.RuntimeCallInitializedEffects
end

section
-- leanmerge: from Solcore.Frontend.RustHull.RuntimeCallInvokeCorrespondence
/-! The actual caller transport uses concrete callback captures and rebuilds
all caller and shared resources after account dispatch. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.RuntimeCallEffectsCorrespondence
open Core Correspondence ScalarExecution

theorem invoke_preserves {layout : Layout} {baseline : Nat → Option Core.Value} {slots : List EffectSlot}
    {image : Option (List UInt8)} {handlers : Handlers layout} {world : World}
    {state : Semantics.State RuntimeCallEffectsSemantics.State} {initial store : Store}
    {operation : RuntimeCallEffectsSemantics.Operation}
    {gas target value inputOffset inputLength outputOffset outputLength : Word}
    {result : Semantics.Result Semantics.Value} {next : CallTransportSemantics.State}
    {shared : AccountCallSemantics.Shared}
    (executed : CallTransportSemantics.Execute
      (AccountCallSemantics.Dispatch AccountCallSemantics.noChildren .ordinary
        state.external.runtime.runtime.runtime.runtime.runtime.storage.address)
      true (RuntimeCallEffectsSemantics.arguments operation state.external gas target value inputOffset inputLength outputOffset outputLength)
      (RuntimeCallEffectsSemantics.transport state.external) (RuntimeCallEffectsSemantics.shared state.external) result next shared)
    (passive : CallPassive layout slots)
    (stateRelated : StateRel (model layout baseline slots image handlers) world state store)
    {environment : Environment}
    {memoryReference sizeReference returnDataReference returnSizeReference callbackReference
      callerAddress currentDepth staticFlag suppliedGas address transferredValue
      sourceOffset sourceLength destinationOffset destinationLength : Core.Expr}
    (packed : Evaluates environment initial
      (bundle [memoryReference, sizeReference, returnDataReference, returnSizeReference,
        callbackReference, callerAddress, currentDepth, staticFlag, suppliedGas, address,
        transferredValue, sourceOffset, sourceLength, destinationOffset, destinationLength])
      (bundleValues (CallTransportCorrespondence.argumentValues (localLocations layout) layout.callHandler
        (RuntimeCallEffectsSemantics.arguments operation state.external gas target value inputOffset inputLength outputOffset outputLength))) store) :
    ∃ resultValue final, ResultRel .word result resultValue ∧
      Evaluates environment initial
        (Calls.invoke memoryReference sizeReference returnDataReference returnSizeReference callbackReference
          callerAddress currentDepth staticFlag suppliedGas address transferredValue
          sourceOffset sourceLength destinationOffset destinationLength) resultValue final ∧
      StateRel (model layout baseline slots image handlers) world
        {state with external := RuntimeCallEffectsSemantics.withTransport state.external next shared} final ∧
      ClosuresPreserved store final := by
  have sharedRelated := shared_resources stateRelated
  have source := source_eq stateRelated
  have preserved : CallTransportCorrespondence.CallbackPreservation (transportModel layout handlers)
      (AccountCallSemantics.Dispatch AccountCallSemantics.noChildren .ordinary
        state.external.runtime.runtime.runtime.runtime.runtime.storage.address) handlers.handlerValue := by
    rw [source]
    exact callback_preserves layout handlers
  have outside : layout.callHandler ∉ (localLocations layout).all :=
    shared_local_separation layout layout.callHandler (by simp)
  obtain ⟨resultValue, final, resultRelated, evaluated, localFinal, sharedFinal, frame⟩ :=
    CallTransportCorrespondence.invoke_preserves (transportModel layout handlers) executed packed
      (local_related stateRelated) sharedRelated sharedRelated.2.1 outside preserved
  exact ⟨resultValue, final, resultRelated, evaluated,
    transport_updated passive stateRelated localFinal sharedFinal.1 frame, frame_closures stateRelated frame⟩

end Solcore.Frontend.RustHull.RuntimeCallEffectsCorrespondence
end

section
-- leanmerge: from Solcore.Frontend.RustHull.RuntimeChildCallStateCorrespondence
/-! Child-capable callers retain exact catalog links in addition to the
existing memory, account, environment and installed-handler resources. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.RuntimeChildCallEffectsCorrespondence
open Correspondence
open RuntimeCallEffectsCorrespondence (Layout Handlers SharedResources sharedLocations localLocations Frame)

abbrev Anchors := List CatalogWorldCorrespondence.Anchor

/-- Immutable captured resources, such as ambient observations and the creator
cell, may be inspected by a child initializer. Changes to caller/shared mutable
cells do not invalidate these concrete reads. -/
structure Context (layout : Layout) where
  valid : (Nat → Option Core.Value) → Prop
  frame : ∀ {before after : Nat → Option Core.Value},
    (∀ location, location ∉ RuntimeCallEffectsCorrespondence.mutable layout → after location = before location) →
    valid before → valid after

def Context.trivial (layout : Layout) : Context layout := ⟨fun _ => True, fun _ _ => True.intro⟩

theorem mutable_included (layout : Layout) {location : Nat}
    (member : location ∈ RuntimeCallEffectsCorrespondence.callMutable layout) :
    location ∈ RuntimeCallEffectsCorrespondence.mutable layout := by
  simp only [RuntimeCallEffectsCorrespondence.callMutable, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [RuntimeCallEffectsCorrespondence.mutable, RuntimeLogEffectsCorrespondence.mutable,
      RuntimeEffectsCorrespondence.mutable, StorageBuiltinCorrespondence.Locations.mutable]

theorem Context.transport {layout : Layout} (context : Context layout) {initial final : Core.Store}
    (bounded : layout.boundary ≤ initial.length) (frame : Frame layout initial final)
    (before : context.valid (prefixRead layout.boundary initial)) :
    context.valid (prefixRead layout.boundary final) := by
  apply context.frame _ before
  intro location outside
  by_cases below : location < layout.boundary
  · have bound := Nat.lt_of_lt_of_le below bounded
    simpa only [prefixRead, below, ↓reduceIte, Core.Store.read?] using
      (frame.read location _ (fun member => outside (mutable_included layout member))
        (List.getElem?_eq_getElem bound)).trans (List.getElem?_eq_getElem bound).symm
  · simp only [prefixRead, below, ↓reduceIte]

def sourceWorld (state : RuntimeCallEffectsSemantics.State) : StorageSemantics.World :=
  (RuntimeCallEffectsSemantics.shared state).world

def model (layout : Layout) (baseline : Nat → Option Core.Value) (slots : List EffectSlot)
    (image : Option (List UInt8)) (handlers : Handlers layout) (anchors : Anchors) (context : Context layout) : StateModel RuntimeCallEffectsSemantics.State :=
  RuntimeLinkedStateCorrespondence.model layout.boundary
    (fun state read => RuntimeCallEffectsCorrespondence.Resources layout baseline slots image handlers state read ∧ context.valid read)
    anchors layout.storage.world sourceWorld

theorem world_below (layout : Layout) : layout.storage.world < layout.boundary :=
  layout.below _ (by simp [StorageBuiltinCorrespondence.Locations.all])

theorem base_related {layout : Layout} {baseline : Nat → Option Core.Value} {slots : List EffectSlot}
    {image : Option (List UInt8)} {handlers : Handlers layout} {anchors : Anchors} {context : Context layout} {world : World}
    {state : Semantics.State RuntimeCallEffectsSemantics.State} {store : Core.Store}
    (related : StateRel (model layout baseline slots image handlers anchors context) world state store) :
    StateRel (RuntimeCallEffectsCorrespondence.model layout baseline slots image handlers) world state store :=
  ⟨related.toHeapRel, related.external.1, related.external.2.1, related.external.2.2.1.1⟩

theorem linked_related {layout : Layout} {baseline : Nat → Option Core.Value} {slots : List EffectSlot}
    {image : Option (List UInt8)} {handlers : Handlers layout} {anchors : Anchors} {context : Context layout} {world : World}
    {state : Semantics.State RuntimeCallEffectsSemantics.State} {store : Core.Store}
    (related : StateRel (model layout baseline slots image handlers anchors context) world state store) :
    RuntimeLinkedWorldCorrespondence.StateRel anchors (sourceWorld state.external) layout.storage.world store :=
  RuntimeLinkedStateCorrespondence.linked_related (world_below layout) related

theorem of_base {layout : Layout} {baseline : Nat → Option Core.Value} {slots : List EffectSlot}
    {image : Option (List UInt8)} {handlers : Handlers layout} {anchors : Anchors} {context : Context layout} {world : World}
    {state : Semantics.State RuntimeCallEffectsSemantics.State} {store : Core.Store}
    (related : StateRel (RuntimeCallEffectsCorrespondence.model layout baseline slots image handlers) world state store)
    (linked : RuntimeLinkedWorldCorrespondence.StateRel anchors (sourceWorld state.external) layout.storage.world store)
    (captured : context.valid (prefixRead layout.boundary store)) :
    StateRel (model layout baseline slots image handlers anchors context) world state store :=
  RuntimeLinkedStateCorrespondence.of_base (world_below layout)
    ⟨related.toHeapRel, related.external.1, related.external.2.1, related.external.2.2, captured⟩ linked

theorem Context.updated {layout : Layout} (context : Context layout)
    {baseline : Nat → Option Core.Value} {slots : List EffectSlot} {image : Option (List UInt8)} {handlers : Handlers layout}
    {beforeWorld afterWorld : World} {beforeState afterState : Semantics.State RuntimeCallEffectsSemantics.State}
    {initial final : Core.Store}
    (before : StateRel (RuntimeCallEffectsCorrespondence.model layout baseline slots image handlers) beforeWorld beforeState initial)
    (after : StateRel (RuntimeCallEffectsCorrespondence.model layout baseline slots image handlers) afterWorld afterState final)
    (captured : context.valid (prefixRead layout.boundary initial)) :
    context.valid (prefixRead layout.boundary final) := by
  apply context.frame _ captured
  intro location outside
  rw [RuntimeCallEffectsCorrespondence.other_related after outside,
    RuntimeCallEffectsCorrespondence.other_related before outside]

def transportModel (layout : Layout) (handlers : Handlers layout) (anchors : Anchors) (context : Context layout) :
    CallTransportCorrespondence.Model AccountCallSemantics.Shared (localLocations layout) where
  related shared store := SharedResources layout handlers shared store ∧
    RuntimeLinkedWorldCorrespondence.StateRel anchors shared.world layout.storage.world store ∧
    layout.boundary ≤ store.length ∧ context.valid (prefixRead layout.boundary store)
  frame := by
    intro shared initial final frame related
    exact ⟨(RuntimeCallEffectsCorrespondence.transportModel layout handlers).frame frame related.1,
      related.2.1.read_preserved (fun value found => frame.read _ value
        (RuntimeCallEffectsCorrespondence.shared_local_separation layout _ (by simp)) found), Nat.le_trans related.2.2.1 frame.length,
      context.transport related.2.2.1 (Frame.of_local frame) related.2.2.2⟩
  retains := Frame layout
  retainedFrame := Frame.of_local
  retainedTrans := Frame.trans

/-- Internal callback interface. The public theorem supplies this from actual
code selection, fresh child allocation, child execution and checkpoint handling. -/
def CallbackPreservation (layout : Layout) (handlers : Handlers layout) (anchors : Anchors) (context : Context layout)
    (children : RuntimeCallEffectsSemantics.State → AccountCallSemantics.Children)
    (parent : RuntimeCallEffectsSemantics.State) : Prop :=
  CallTransportCorrespondence.CallbackPreservation (transportModel layout handlers anchors context)
    (AccountCallSemantics.Dispatch (children parent) .ordinary
      parent.runtime.runtime.runtime.runtime.runtime.storage.address) handlers.handlerValue

end Solcore.Frontend.RustHull.RuntimeChildCallEffectsCorrespondence
end

section
-- leanmerge: from Solcore.Frontend.RustHull.RuntimeCallModeStateCorrespondence
/-! Mode-specific handlers and the create handler are concrete immutable
captures. The existing linked caller model carries their reads alongside the
captured initialization context. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.RuntimeCallModeEffectsCorrespondence
open Core Correspondence
open RuntimeCallEffectsCorrespondence (Layout Handlers mutable localLocations)
open RuntimeChildCallEffectsCorrespondence (Anchors Context)
open RuntimeCallModeSemantics (Operation)

structure ExtraHandler (layout : Layout) (source : Word) (mode : AccountCallSemantics.Mode) where
  location : Nat
  below : location < layout.boundary
  outside : location ∉ mutable layout
  value : Value
  closure : AccountCallModeCorrespondence.CallHandlerClosure mode source layout.dispatcher value

/-- The create handler cell installed by the object initializer. Every frame
reuses this cell, and no frame resource writes it. -/
structure CreateHandler (layout : Layout) where
  location : Nat
  below : location < layout.boundary
  outside : location ∉ mutable layout
  value : Value
  closure : CreationCorrespondence.HandlerClosure (RuntimeCallEffectsCorrespondence.sharedLocations layout) value

/-- A captured context that also observes the create-handler cell; child
frames receive this read from the frame that calls them. -/
def CreateHandler.context {layout : Layout} (create : CreateHandler layout) (captured : Context layout) :
    Context layout where
  valid read := captured.valid read ∧ read create.location = some (.inRight .unit create.value)
  frame := by
    intro before after kept valid
    exact ⟨captured.frame kept valid.1, (kept _ create.outside).trans valid.2⟩

structure ModeHandlers (layout : Layout) where
  ordinary : Handlers layout
  callCode : ExtraHandler layout ordinary.source .callCode
  delegateCall : ExtraHandler layout ordinary.source .delegateCall
  create : CreateHandler layout

def ModeHandlers.context {layout : Layout} (handlers : ModeHandlers layout) (captured : Context layout) : Context layout where
  valid read := captured.valid read ∧
    read handlers.callCode.location = some (.inRight .unit handlers.callCode.value) ∧
    read handlers.delegateCall.location = some (.inRight .unit handlers.delegateCall.value) ∧
    read handlers.create.location = some (.inRight .unit handlers.create.value)
  frame := by
    intro before after kept valid
    exact ⟨captured.frame kept valid.1,
      (kept _ handlers.callCode.outside).trans valid.2.1,
      (kept _ handlers.delegateCall.outside).trans valid.2.2.1,
      (kept _ handlers.create.outside).trans valid.2.2.2⟩

/-- Slots read by the create lowering beyond the ordinary call slots. -/
structure CreateSlots {layout : Layout} (handlers : ModeHandlers layout) (slots : List EffectSlot) : Prop where
  handler : ⟨"createHandler", OptionalCell.cellType Creation.callbackType, handlers.create.location⟩ ∈ slots
  gas : ∃ location, (⟨"availableGas", .sum .unit .word, location⟩ : EffectSlot) ∈ slots

def model (layout : Layout) (baseline : Nat → Option Value) (slots : List EffectSlot)
    (image : Option (List UInt8)) (handlers : ModeHandlers layout) (anchors : Anchors) (context : Context layout) :
    StateModel RuntimeCallModeSemantics.State :=
  RuntimeChildCallEffectsCorrespondence.model layout baseline slots image handlers.ordinary anchors (handlers.context context)

def ModeHandlers.location {layout : Layout} (handlers : ModeHandlers layout) : Operation → Nat
  | .ordinary | .staticCall => layout.callHandler
  | .callCode => handlers.callCode.location
  | .delegateCall => handlers.delegateCall.location

def ModeHandlers.value {layout : Layout} (handlers : ModeHandlers layout) : Operation → Value
  | .ordinary | .staticCall => handlers.ordinary.handlerValue
  | .callCode => handlers.callCode.value
  | .delegateCall => handlers.delegateCall.value

def ModeHandlers.closure {layout : Layout} (handlers : ModeHandlers layout) (operation : Operation) :
    AccountCallModeCorrespondence.CallHandlerClosure operation.mode handlers.ordinary.source layout.dispatcher (handlers.value operation) := by
  cases operation with
  | ordinary | staticCall => exact .of_ordinary handlers.ordinary.handler
  | callCode => exact handlers.callCode.closure
  | delegateCall => exact handlers.delegateCall.closure

def transportModel (layout : Layout) (handlers : ModeHandlers layout) (anchors : Anchors) (context : Context layout) :=
  RuntimeChildCallEffectsCorrespondence.transportModel layout handlers.ordinary anchors (handlers.context context)

def CallbackPreservation (layout : Layout) (handlers : ModeHandlers layout) (anchors : Anchors) (context : Context layout)
    (children : RuntimeCallModeSemantics.State → AccountCallSemantics.Children)
    (operation : Operation) (parent : RuntimeCallModeSemantics.State) : Prop :=
  CallTransportCorrespondence.CallbackPreservation (transportModel layout handlers anchors context)
    (AccountCallSemantics.Dispatch (children parent) operation.mode parent.runtime.runtime.runtime.runtime.runtime.storage.address)
    (handlers.value operation)

theorem base_related {layout : Layout} {baseline : Nat → Option Value} {slots : List EffectSlot}
    {image : Option (List UInt8)} {handlers : ModeHandlers layout} {anchors : Anchors} {context : Context layout} {world : World}
    {state : Semantics.State RuntimeCallModeSemantics.State} {store : Store}
    (related : StateRel (model layout baseline slots image handlers anchors context) world state store) :
    StateRel (RuntimeCallEffectsCorrespondence.model layout baseline slots image handlers.ordinary) world state store :=
  RuntimeChildCallEffectsCorrespondence.base_related related

theorem handler_read {layout : Layout} {baseline : Nat → Option Value} {slots : List EffectSlot}
    {image : Option (List UInt8)} {handlers : ModeHandlers layout} {anchors : Anchors} {context : Context layout} {world : World}
    {state : Semantics.State RuntimeCallModeSemantics.State} {store : Store}
    (related : StateRel (model layout baseline slots image handlers anchors context) world state store)
    (operation : Operation) : store.read? (handlers.location operation) = some (.inRight .unit (handlers.value operation)) := by
  cases operation with
  | ordinary | staticCall =>
      exact (RuntimeCallEffectsCorrespondence.shared_resources (base_related related)).2.1
  | callCode =>
      simpa only [ModeHandlers.location, ModeHandlers.value, prefixRead, handlers.callCode.below, ↓reduceIte]
        using related.external.2.2.1.2.2.1
  | delegateCall =>
      simpa only [ModeHandlers.location, ModeHandlers.value, prefixRead, handlers.delegateCall.below, ↓reduceIte]
        using related.external.2.2.1.2.2.2.1

theorem create_read {layout : Layout} {baseline : Nat → Option Value} {slots : List EffectSlot}
    {image : Option (List UInt8)} {handlers : ModeHandlers layout} {anchors : Anchors} {context : Context layout} {world : World}
    {state : Semantics.State RuntimeCallModeSemantics.State} {store : Store}
    (related : StateRel (model layout baseline slots image handlers anchors context) world state store) :
    store.read? handlers.create.location = some (.inRight .unit handlers.create.value) := by
  simpa only [prefixRead, handlers.create.below, ↓reduceIte] using related.external.2.2.1.2.2.2.2

theorem CreateHandler.local_outside {layout : Layout} (create : CreateHandler layout) :
    create.location ∉ (localLocations layout).resources.all := by
  intro member
  apply create.outside
  simp only [localLocations, CallTransportCorrespondence.Locations.resources, LogsCorrespondence.Locations.all,
    List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same | same | same | same <;> rw [same] <;>
    simp [mutable, RuntimeLogEffectsCorrespondence.mutable, RuntimeEffectsCorrespondence.mutable,
      StorageBuiltinCorrespondence.Locations.mutable]

theorem ModeHandlers.local_outside {layout : Layout} (handlers : ModeHandlers layout) (operation : Operation) :
    handlers.location operation ∉ (localLocations layout).all := by
  cases operation with
  | ordinary | staticCall => exact RuntimeCallEffectsCorrespondence.shared_local_separation layout _ (by simp [ModeHandlers.location])
  | callCode =>
      intro member
      apply handlers.callCode.outside
      simp only [ModeHandlers.location, localLocations, CallTransportCorrespondence.Locations.all,
        List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with same | same | same | same <;> rw [same] <;>
        simp [mutable, RuntimeLogEffectsCorrespondence.mutable, RuntimeEffectsCorrespondence.mutable,
          StorageBuiltinCorrespondence.Locations.mutable]
  | delegateCall =>
      intro member
      apply handlers.delegateCall.outside
      simp only [ModeHandlers.location, localLocations, CallTransportCorrespondence.Locations.all,
        List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with same | same | same | same <;> rw [same] <;>
        simp [mutable, RuntimeLogEffectsCorrespondence.mutable, RuntimeEffectsCorrespondence.mutable,
          StorageBuiltinCorrespondence.Locations.mutable]

end Solcore.Frontend.RustHull.RuntimeCallModeEffectsCorrespondence
end

section
-- leanmerge: from Solcore.Frontend.RustHull.RuntimeChildCallCallbackCorrespondence
/-! Concrete child dispatch discharges the caller transport interface. Child
frames can change four shared cells; caller memory, return data and captured
context remain available for the subsequent transport steps. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.RuntimeChildCallEffectsCorrespondence
open Core Correspondence
open RuntimeCallEffectsCorrespondence (Layout Handlers sharedLocations localLocations)

theorem shared_mutable_included (layout : Layout) {location : Nat}
    (member : location ∈ (sharedLocations layout).mutable) :
    location ∈ RuntimeCallEffectsCorrespondence.callMutable layout := by
  simp only [sharedLocations, AccountCallCorrespondence.SharedLocations.mutable,
    List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl <;> simp [RuntimeCallEffectsCorrespondence.callMutable]

theorem shared_frame {layout : Layout} {initial final : Core.Store}
    (frame : AccountCallCorrespondence.SharedFrame (sharedLocations layout) initial final) :
    RuntimeCallEffectsCorrespondence.Frame layout initial final :=
  ⟨frame.length_le, fun location value outside found =>
    frame.read location value (fun member => outside (shared_mutable_included layout member)) found⟩

def childReady (layout : Layout) (context : Context layout) (store : Core.Store) : Prop :=
  layout.boundary ≤ store.length ∧ context.valid (prefixRead layout.boundary store)

theorem childReady_preserved {layout : Layout} {context : Context layout} {initial final : Core.Store}
    (frame : AccountCallCorrespondence.SharedFrame (sharedLocations layout) initial final)
    (ready : childReady layout context initial) : childReady layout context final :=
  ⟨Nat.le_trans ready.1 frame.length_le, context.transport ready.1 (shared_frame frame) ready.2⟩

abbrev ChildExecution (layout : Layout) (handlers : Handlers layout) (anchors : Anchors)
    (context : Context layout) (children : AccountCallSemantics.Children) : Prop :=
  AccountCallCorrespondence.ChildRunPreservation anchors (sharedLocations layout)
    handlers.dispatch.shared handlers.dispatch.runFrame children (childReady layout context)
    handlers.dispatch.depth handlers.dispatch.captured

theorem callback_preserves (layout : Layout) (handlers : Handlers layout) (anchors : Anchors)
    (context : Context layout) (children : RuntimeCallEffectsSemantics.State → AccountCallSemantics.Children)
    (parent : RuntimeCallEffectsSemantics.State)
    (source : parent.runtime.runtime.runtime.runtime.runtime.storage.address = handlers.source)
    (childExecution : ChildExecution layout handlers anchors context (children parent)) :
    CallbackPreservation layout handlers anchors context children parent := by
  intro request shared finalShared result computed state environment store function argument related localRelated resolved supplied
  rw [source] at computed
  obtain ⟨target, final, evaluated, resultRelated, sharedFinal, frame⟩ :=
    handlers.handler.apply_children_preserves handlers.dispatch childExecution (fun frame ready => childReady_preserved frame ready)
      computed ⟨related.1.1, related.2.1⟩ related.2.2 related.1.2.2 resolved supplied
  have separated : ∀ location ∈ [layout.memory, layout.storage.memorySize, layout.returnData,
      layout.returnDataSize, layout.callHandler, layout.dispatcher], location ∉ (sharedLocations layout).mutable := by
    have distinct := layout.callDistinct
    simp only [StorageBuiltinCorrespondence.Locations.all, List.nodup_cons, List.mem_cons,
      List.not_mem_nil, or_false, not_or] at distinct
    intro location member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp only [sharedLocations, AccountCallCorrespondence.SharedLocations.mutable,
      List.mem_cons, List.not_mem_nil, or_false, not_or]
    all_goals simp_all [ne_comm]
  have keep {location : Nat} {value : Core.Value}
      (member : location ∈ [layout.memory, layout.storage.memorySize, layout.returnData,
        layout.returnDataSize, layout.callHandler, layout.dispatcher])
      (found : store.read? location = some value) : final.read? location = some value :=
    frame.read location value (separated location member) found
  refine ⟨target, final, resultRelated, evaluated,
    ⟨localRelated.distinct, keep (by simp [localLocations, CallTransportCorrespondence.Locations.resources]) localRelated.memory,
      keep (by simp [localLocations, CallTransportCorrespondence.Locations.resources]) localRelated.memorySize,
      keep (by simp [localLocations, CallTransportCorrespondence.Locations.resources]) localRelated.logs,
      keep (by simp [localLocations, CallTransportCorrespondence.Locations.resources]) localRelated.logSize⟩,
    ⟨⟨sharedFinal.shared, keep (by simp) related.1.2.1, keep (by simp) related.1.2.2⟩,
      sharedFinal.linked, childReady_preserved frame related.2.2⟩, shared_frame frame⟩

end Solcore.Frontend.RustHull.RuntimeChildCallEffectsCorrespondence
end

section
-- leanmerge: from Solcore.Frontend.RustHull.RuntimeCallModeCallbackCorrespondence
/-! Each selected call mode reaches the actual captured dispatcher. The fixed
handler captures survive child execution alongside the parent frame resources. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.RuntimeCallModeEffectsCorrespondence
open Core Correspondence
open RuntimeCallEffectsCorrespondence (Layout sharedLocations localLocations)
open RuntimeChildCallEffectsCorrespondence
  (Anchors Context childReady childReady_preserved shared_frame)

abbrev ChildExecution (layout : Layout) (handlers : ModeHandlers layout) (anchors : Anchors)
    (context : Context layout) (mode : AccountCallSemantics.Mode) (children : AccountCallSemantics.Children) : Prop :=
  AccountCallModeCorrespondence.ChildRunPreservation mode anchors (sharedLocations layout)
    handlers.ordinary.dispatch.shared handlers.ordinary.dispatch.runFrame children (childReady layout (handlers.context context))
    handlers.ordinary.dispatch.depth handlers.ordinary.dispatch.captured

theorem callback_preserves (layout : Layout) (handlers : ModeHandlers layout) (anchors : Anchors)
    (context : Context layout) (children : RuntimeCallModeSemantics.State → AccountCallSemantics.Children)
    (operation : RuntimeCallModeSemantics.Operation) (parent : RuntimeCallModeSemantics.State)
    (source : parent.runtime.runtime.runtime.runtime.runtime.storage.address = handlers.ordinary.source)
    (childExecution : ChildExecution layout handlers anchors context operation.mode (children parent)) :
    CallbackPreservation layout handlers anchors context children operation parent := by
  intro request shared finalShared result computed state environment store function argument related localRelated resolved supplied
  rw [source] at computed
  obtain ⟨target, final, evaluated, resultRelated, sharedFinal, frame⟩ :=
    (handlers.closure operation).apply_children_preserves handlers.ordinary.dispatch childExecution (fun frame ready => childReady_preserved frame ready)
      computed ⟨related.1.1, related.2.1⟩ related.2.2 related.1.2.2 resolved supplied
  have separated : ∀ location ∈ [layout.memory, layout.storage.memorySize, layout.returnData,
      layout.returnDataSize, layout.callHandler, layout.dispatcher], location ∉ (sharedLocations layout).mutable := by
    have distinct := layout.callDistinct
    simp only [StorageBuiltinCorrespondence.Locations.all, List.nodup_cons, List.mem_cons,
      List.not_mem_nil, or_false, not_or] at distinct
    intro location member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp only [sharedLocations, AccountCallCorrespondence.SharedLocations.mutable,
      List.mem_cons, List.not_mem_nil, or_false, not_or]
    all_goals simp_all [ne_comm]
  have keep {location : Nat} {value : Core.Value}
      (member : location ∈ [layout.memory, layout.storage.memorySize, layout.returnData,
        layout.returnDataSize, layout.callHandler, layout.dispatcher])
      (found : store.read? location = some value) : final.read? location = some value :=
    frame.read location value (separated location member) found
  refine ⟨target, final, resultRelated, evaluated,
    ⟨localRelated.distinct, keep (by simp [localLocations, CallTransportCorrespondence.Locations.resources]) localRelated.memory,
      keep (by simp [localLocations, CallTransportCorrespondence.Locations.resources]) localRelated.memorySize,
      keep (by simp [localLocations, CallTransportCorrespondence.Locations.resources]) localRelated.logs,
      keep (by simp [localLocations, CallTransportCorrespondence.Locations.resources]) localRelated.logSize⟩,
    ⟨⟨sharedFinal.shared, keep (by simp) related.1.2.1, keep (by simp) related.1.2.2⟩,
      sharedFinal.linked, childReady_preserved frame related.2.2⟩, shared_frame frame⟩


end Solcore.Frontend.RustHull.RuntimeCallModeEffectsCorrespondence
end

section
-- leanmerge: from Solcore.Frontend.RustHull.RuntimeCallModeCompatibility
/-! Existing ordinary and static-call proofs also apply to the extended source
semantics: their guards, message arguments and callback modes are unchanged. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.RuntimeCallModeSemantics
open Core

section
variable {children : State → AccountCallSemantics.Children}
variable {gas target value inputOffset inputLength outputOffset outputLength : Word}
variable {state final : State} {result : Semantics.Result Semantics.Value}

theorem ordinary_call
    (computed : Call children .ordinary gas target value inputOffset inputLength outputOffset outputLength state result final) :
    RuntimeCallEffectsSemantics.Call children .ordinary gas target value inputOffset inputLength outputOffset outputLength state result final := by
  cases computed with
  | staticValue _ isStatic nonzero => exact .staticValue _ rfl isStatic nonzero
  | gasOverflow _ permitted nonzero overflow =>
      have notStatic : state.runtime.runtime.runtime.runtime.runtime.storage.isStatic = false := permitted.resolve_left (by simp)
      exact .gasOverflow _ rfl notStatic nonzero overflow
  | invoked permitted stipend executed =>
      apply RuntimeCallEffectsSemantics.Call.invoked
      · exact .inr (permitted.resolve_left (by simp))
      · intro _ nonzero
        exact stipend rfl nonzero
      · simpa only [arguments, RuntimeCallEffectsSemantics.arguments, Operation.hasStipend,
          Operation.mode, reduceCtorEq, ↓reduceIte, and_true, true_and] using executed

theorem static_call
    (computed : Call children .staticCall gas target Word.zero inputOffset inputLength outputOffset outputLength state result final) :
    RuntimeCallEffectsSemantics.Call children .staticCall gas target Word.zero inputOffset inputLength outputOffset outputLength state result final := by
  cases computed with
  | staticValue ordinary _ _ => cases ordinary
  | gasOverflow stipend _ _ _ => cases stipend
  | invoked _ _ executed =>
      apply RuntimeCallEffectsSemantics.Call.invoked (.inl rfl)
      · intro impossible
        cases impossible
      · simpa only [arguments, RuntimeCallEffectsSemantics.arguments, Operation.hasStipend,
          Operation.mode, reduceCtorEq, ↓reduceIte, ne_eq, not_true_eq_false, and_false] using executed

end
end Solcore.Frontend.RustHull.RuntimeCallModeSemantics
end

section
-- leanmerge: from Solcore.Frontend.RustHull.RuntimeCallModeInvokeCorrespondence
/-! The actual caller transport uses concrete callback captures and rebuilds
all caller and shared resources after account dispatch. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.RuntimeCallModeEffectsCorrespondence
open Core Correspondence ScalarExecution
open RuntimeCallEffectsCorrespondence (Layout CallPassive localLocations)
open RuntimeChildCallEffectsCorrespondence (Anchors linked_related of_base)

theorem invoke_preserves {layout : Layout} {baseline : Nat → Option Core.Value} {slots : List EffectSlot}
    {image : Option (List UInt8)} {handlers : ModeHandlers layout} {anchors : Anchors} {context : RuntimeChildCallEffectsCorrespondence.Context layout} {world : World}
    {children : RuntimeCallEffectsSemantics.State → AccountCallSemantics.Children}
    {state : Semantics.State RuntimeCallEffectsSemantics.State} {initial store : Store}
    {operation : RuntimeCallModeSemantics.Operation}
    {gas target value inputOffset inputLength outputOffset outputLength : Word}
    {result : Semantics.Result Semantics.Value} {next : CallTransportSemantics.State}
    {shared : AccountCallSemantics.Shared}
    (executed : CallTransportSemantics.Execute
      (AccountCallSemantics.Dispatch (children state.external) operation.mode
        state.external.runtime.runtime.runtime.runtime.runtime.storage.address)
      true (RuntimeCallModeSemantics.arguments operation state.external gas target value inputOffset inputLength outputOffset outputLength)
      (RuntimeCallEffectsSemantics.transport state.external) (RuntimeCallEffectsSemantics.shared state.external) result next shared)
    (passive : CallPassive layout slots)
    (stateRelated : StateRel (model layout baseline slots image handlers anchors context) world state store)
    (callback : CallbackPreservation layout handlers anchors context children operation state.external)
    {environment : Environment}
    {memoryReference sizeReference returnDataReference returnSizeReference callbackReference
      callerAddress currentDepth staticFlag suppliedGas address transferredValue
      sourceOffset sourceLength destinationOffset destinationLength : Core.Expr}
    (packed : Evaluates environment initial
      (bundle [memoryReference, sizeReference, returnDataReference, returnSizeReference,
        callbackReference, callerAddress, currentDepth, staticFlag, suppliedGas, address,
        transferredValue, sourceOffset, sourceLength, destinationOffset, destinationLength])
      (bundleValues (CallTransportCorrespondence.argumentValues (localLocations layout) (handlers.location operation)
        (RuntimeCallModeSemantics.arguments operation state.external gas target value inputOffset inputLength outputOffset outputLength))) store) :
    ∃ resultValue final, ResultRel .word result resultValue ∧
      Evaluates environment initial
        (Calls.invoke memoryReference sizeReference returnDataReference returnSizeReference callbackReference
          callerAddress currentDepth staticFlag suppliedGas address transferredValue
          sourceOffset sourceLength destinationOffset destinationLength) resultValue final ∧
      StateRel (model layout baseline slots image handlers anchors context) world
        {state with external := RuntimeCallEffectsSemantics.withTransport state.external next shared} final ∧
      ClosuresPreserved store final := by
  have before := base_related stateRelated
  have sharedRelated : (transportModel layout handlers anchors context).related
      (RuntimeCallEffectsSemantics.shared state.external) store :=
    ⟨RuntimeCallEffectsCorrespondence.shared_resources before, linked_related stateRelated,
      stateRelated.external.1, stateRelated.external.2.2.1.2⟩
  obtain ⟨resultValue, final, resultRelated, evaluated, localFinal, sharedFinal, frame⟩ :=
    CallTransportCorrespondence.invoke_preserves (transportModel layout handlers anchors context) executed packed
      (RuntimeCallEffectsCorrespondence.local_related before) sharedRelated (handler_read stateRelated operation) (handlers.local_outside operation) callback
  exact ⟨resultValue, final, resultRelated, evaluated,
    of_base (RuntimeCallEffectsCorrespondence.transport_updated passive before localFinal sharedFinal.1.1 frame) sharedFinal.2.1 sharedFinal.2.2.2,
    RuntimeCallEffectsCorrespondence.frame_closures before frame⟩

end Solcore.Frontend.RustHull.RuntimeCallModeEffectsCorrespondence
end

section
-- leanmerge: from Solcore.Frontend.RustHull.RuntimeChildCallEmptyCorrespondence
/-! Existing child-free callers instantiate the linked model with no anchors
and a trivial captured-context condition. The original public API is unchanged. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.RuntimeChildCallEffectsCorrespondence
open Correspondence
open RuntimeCallEffectsCorrespondence (Layout Handlers)

theorem empty_state {layout : Layout} {baseline : Nat → Option Core.Value} {slots : List EffectSlot}
    {image : Option (List UInt8)} {handlers : Handlers layout} {world : World}
    {state : Semantics.State RuntimeCallEffectsSemantics.State} {store : Core.Store}
    (related : StateRel (RuntimeCallEffectsCorrespondence.model layout baseline slots image handlers) world state store) :
    StateRel (model layout baseline slots image handlers [] (Context.trivial layout)) world state store := by
  obtain ⟨accounts, same, read⟩ := (RuntimeCallEffectsCorrespondence.shared_related related).world
  exact of_base related ⟨accounts, same, by simp [CatalogWorldCorrespondence.Links], read⟩ True.intro

theorem empty_callback (layout : Layout) (handlers : Handlers layout)
    (parent : RuntimeCallEffectsSemantics.State)
    (source : parent.runtime.runtime.runtime.runtime.runtime.storage.address = handlers.source) :
    CallbackPreservation layout handlers [] (Context.trivial layout)
      (fun _ => AccountCallSemantics.noChildren) parent := by
  intro request shared finalShared result computed state environment store function argument related localRelated resolved supplied
  rw [source] at computed
  obtain ⟨target, final, resultRelated, evaluated, localFinal, sharedFinal, frame⟩ :=
    RuntimeCallEffectsCorrespondence.callback_preserves layout handlers computed related.1 localRelated resolved supplied
  obtain ⟨accounts, same, read⟩ := sharedFinal.1.world
  refine ⟨target, final, resultRelated, evaluated, localFinal, ?_, frame⟩
  exact ⟨sharedFinal, ⟨accounts, same, by simp [CatalogWorldCorrespondence.Links], read⟩,
    Nat.le_trans related.2.2.1 frame.length_le, True.intro⟩

end Solcore.Frontend.RustHull.RuntimeChildCallEffectsCorrespondence
end

section
-- leanmerge: from Solcore.Frontend.RustHull.RuntimeChildCallInvokeCorrespondence
/-! The actual caller transport uses concrete callback captures and rebuilds
all caller and shared resources after account dispatch. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.RuntimeChildCallEffectsCorrespondence
open Core Correspondence ScalarExecution
open RuntimeCallEffectsCorrespondence (Layout Handlers CallPassive localLocations)

theorem invoke_preserves {layout : Layout} {baseline : Nat → Option Core.Value} {slots : List EffectSlot}
    {image : Option (List UInt8)} {handlers : Handlers layout} {anchors : Anchors} {context : RuntimeChildCallEffectsCorrespondence.Context layout} {world : World}
    {children : RuntimeCallEffectsSemantics.State → AccountCallSemantics.Children}
    {state : Semantics.State RuntimeCallEffectsSemantics.State} {initial store : Store}
    {operation : RuntimeCallEffectsSemantics.Operation}
    {gas target value inputOffset inputLength outputOffset outputLength : Word}
    {result : Semantics.Result Semantics.Value} {next : CallTransportSemantics.State}
    {shared : AccountCallSemantics.Shared}
    (executed : CallTransportSemantics.Execute
      (AccountCallSemantics.Dispatch (children state.external) .ordinary
        state.external.runtime.runtime.runtime.runtime.runtime.storage.address)
      true (RuntimeCallEffectsSemantics.arguments operation state.external gas target value inputOffset inputLength outputOffset outputLength)
      (RuntimeCallEffectsSemantics.transport state.external) (RuntimeCallEffectsSemantics.shared state.external) result next shared)
    (passive : CallPassive layout slots)
    (stateRelated : StateRel (model layout baseline slots image handlers anchors context) world state store)
    (callback : CallbackPreservation layout handlers anchors context children state.external)
    {environment : Environment}
    {memoryReference sizeReference returnDataReference returnSizeReference callbackReference
      callerAddress currentDepth staticFlag suppliedGas address transferredValue
      sourceOffset sourceLength destinationOffset destinationLength : Core.Expr}
    (packed : Evaluates environment initial
      (bundle [memoryReference, sizeReference, returnDataReference, returnSizeReference,
        callbackReference, callerAddress, currentDepth, staticFlag, suppliedGas, address,
        transferredValue, sourceOffset, sourceLength, destinationOffset, destinationLength])
      (bundleValues (CallTransportCorrespondence.argumentValues (localLocations layout) layout.callHandler
        (RuntimeCallEffectsSemantics.arguments operation state.external gas target value inputOffset inputLength outputOffset outputLength))) store) :
    ∃ resultValue final, ResultRel .word result resultValue ∧
      Evaluates environment initial
        (Calls.invoke memoryReference sizeReference returnDataReference returnSizeReference callbackReference
          callerAddress currentDepth staticFlag suppliedGas address transferredValue
          sourceOffset sourceLength destinationOffset destinationLength) resultValue final ∧
      StateRel (model layout baseline slots image handlers anchors context) world
        {state with external := RuntimeCallEffectsSemantics.withTransport state.external next shared} final ∧
      ClosuresPreserved store final := by
  have before := base_related stateRelated
  have sharedRelated : (transportModel layout handlers anchors context).related
      (RuntimeCallEffectsSemantics.shared state.external) store :=
    ⟨RuntimeCallEffectsCorrespondence.shared_resources before, linked_related stateRelated,
      stateRelated.external.1, stateRelated.external.2.2.1.2⟩
  have outside : layout.callHandler ∉ (localLocations layout).all :=
    RuntimeCallEffectsCorrespondence.shared_local_separation layout layout.callHandler (by simp)
  obtain ⟨resultValue, final, resultRelated, evaluated, localFinal, sharedFinal, frame⟩ :=
    CallTransportCorrespondence.invoke_preserves (transportModel layout handlers anchors context) executed packed
      (RuntimeCallEffectsCorrespondence.local_related before) sharedRelated sharedRelated.1.2.1 outside callback
  exact ⟨resultValue, final, resultRelated, evaluated,
    of_base (RuntimeCallEffectsCorrespondence.transport_updated passive before localFinal sharedFinal.1.1 frame) sharedFinal.2.1 sharedFinal.2.2.2,
    RuntimeCallEffectsCorrespondence.frame_closures before frame⟩

end Solcore.Frontend.RustHull.RuntimeChildCallEffectsCorrespondence
end

section
-- leanmerge: from Solcore.Frontend.RustHull.RuntimeChildCallTerminationCorrespondence
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
end

section
-- leanmerge: from Solcore.Frontend.RustHull.RuntimeLifecycleStateCorrespondence
/-! Destruction retains caller-local cells and captures while replacing shared
accounts and balances. Termination then preserves the resulting code links. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.RuntimeLifecycleCorrespondence
open Core Correspondence
open RuntimeCallEffectsCorrespondence (Layout CallPassive sharedLocations localLocations)
open RuntimeCallModeEffectsCorrespondence (ModeHandlers model base_related)
open RuntimeChildCallEffectsCorrespondence (Anchors Context)

theorem transport_shared (state : RuntimeCallEffectsSemantics.State) (shared : AccountCallSemantics.Shared) :
    RuntimeCallEffectsSemantics.withTransport state (RuntimeCallEffectsSemantics.transport state) shared =
      RuntimeCallEffectsSemantics.withShared state shared := by
  have observed : (fun operation => if operation = EnvironmentSemantics.Direct.returnDataSize then
      state.runtime.runtime.runtime.runtime.environment.direct .returnDataSize else
      state.runtime.runtime.runtime.runtime.environment.direct operation) =
      state.runtime.runtime.runtime.runtime.environment.direct := by
    funext operation
    split <;> simp_all
  simp only [RuntimeCallEffectsSemantics.withTransport, RuntimeCallEffectsSemantics.transport,
    RuntimeCallEffectsSemantics.withReturned, RuntimeCallEffectsSemantics.withShared,
    RuntimeReturnDataEffectsSemantics.size, observed]


private theorem separated (layout : Layout) {location : Nat}
    (member : location ∈ [layout.memory, layout.storage.memorySize, layout.returnData,
      layout.returnDataSize, layout.logs, layout.logSize, layout.storage.complete]) :
    location ≠ layout.storage.world ∧ location ≠ layout.balances := by
  have distinct := layout.callDistinct
  simp only [StorageBuiltinCorrespondence.Locations.all, List.nodup_cons, List.mem_cons,
    List.not_mem_nil, or_false, not_or] at distinct
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp_all [ne_comm]

theorem updated_preserves {layout : Layout} {baseline : Nat → Option Value} {slots : List EffectSlot}
    {image : Option (List UInt8)} {handlers : ModeHandlers layout} {anchors : Anchors} {context : Context layout}
    {world : World} {state : Semantics.State RuntimeCallEffectsSemantics.State} {initial final : Store}
    {nextWorld : StorageSemantics.World} {nextBalances : StorageSemantics.Words}
    (passive : CallPassive layout slots)
    (before : StateRel (model layout baseline slots image handlers anchors context) world state initial)
    (linked : RuntimeLinkedWorldCorrespondence.StateRel anchors nextWorld layout.storage.world final)
    (balances : final.read? layout.balances = some (WordMapping.encode nextBalances))
    (frame : StorageCorrespondence.FinalizeFrame layout.storage.world layout.balances initial final) :
    StateRel (model layout baseline slots image handlers anchors context) world
      {state with external := RuntimeLifecycleSemantics.updated state.external nextWorld nextBalances} final ∧
      ClosuresPreserved initial final := by
  have base := base_related before
  have shared := (RuntimeCallEffectsCorrespondence.shared_resources base).1
  have localBefore := RuntimeCallEffectsCorrespondence.local_related base
  have keep {location : Nat} {value : Value} (notWorld : location ≠ layout.storage.world)
      (notBalances : location ≠ layout.balances) (read : initial.read? location = some value) :
      final.read? location = some value := frame.preserved location value notWorld notBalances read
  have localFinal : CallTransportCorrespondence.StateRel (localLocations layout)
      (RuntimeCallEffectsSemantics.transport state.external) final := by
    refine ⟨localBefore.distinct, ?_, ?_, ?_, ?_⟩
    · exact keep (location := layout.memory) (separated layout (by simp)).1 (separated layout (by simp)).2 localBefore.memory
    · exact keep (location := layout.storage.memorySize) (separated layout (by simp)).1 (separated layout (by simp)).2 localBefore.memorySize
    · exact keep (location := layout.returnData) (separated layout (by simp)).1 (separated layout (by simp)).2 localBefore.logs
    · exact keep (location := layout.returnDataSize) (separated layout (by simp)).1 (separated layout (by simp)).2 localBefore.logSize
  have sharedFinal : AccountCallCorrespondence.SharedStateRel (sharedLocations layout)
      {RuntimeCallEffectsSemantics.shared state.external with world := nextWorld, balances := nextBalances} final := by
    refine ⟨linked.forget, ?_, ?_, balances, ?_, shared.distinct⟩
    · exact keep (location := layout.logs) (separated layout (by simp)).1 (separated layout (by simp)).2 shared.logs
    · exact keep (location := layout.logSize) (separated layout (by simp)).1 (separated layout (by simp)).2 shared.logSize
    · exact keep (location := layout.storage.complete) (separated layout (by simp)).1 (separated layout (by simp)).2 shared.complete
  have callFrame : RuntimeCallEffectsCorrespondence.Frame layout initial final := by
    refine ⟨frame.length_le, ?_⟩
    intro location value outside read
    exact keep (fun same => outside (by simp [RuntimeCallEffectsCorrespondence.callMutable, same]))
      (fun same => outside (by simp [RuntimeCallEffectsCorrespondence.callMutable, same])) read
  have changed := RuntimeCallEffectsCorrespondence.transport_updated passive base localFinal sharedFinal callFrame
  rw [transport_shared] at changed
  exact ⟨RuntimeChildCallEffectsCorrespondence.of_base changed linked
      ((handlers.context context).transport before.external.1 callFrame before.external.2.2.1.2),
    RuntimeCallEffectsCorrespondence.frame_closures base callFrame⟩

theorem terminate_linked {layout : Layout} {baseline : Nat → Option Core.Value} {slots : List EffectSlot}
    {image : Option (List UInt8)} {handlers : ModeHandlers layout} {anchors : Anchors} {context : RuntimeChildCallEffectsCorrespondence.Context layout} {world : World}
    {state : Semantics.State RuntimeCallEffectsSemantics.State} {store : Store}
    (kind : Nat)
    (related : StateRel (model layout baseline slots image handlers anchors context) world state store) :
    RuntimeLinkedWorldCorrespondence.StateRel anchors (RuntimeChildCallEffectsCorrespondence.sourceWorld (RuntimeLifecycleSemantics.terminate state.external kind).2)
      layout.storage.world
      (TerminationBuiltinCorrespondence.finalStore layout.storage state.external.runtime.runtime.runtime.runtime.runtime kind Word.zero Word.zero store) := by
  have linked := RuntimeChildCallEffectsCorrespondence.linked_related related
  change RuntimeLinkedWorldCorrespondence.StateRel anchors (RuntimeChildCallEffectsCorrespondence.sourceWorld state.external) layout.storage.world _
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
      layout.storage.returnSize (.word Word.zero)).set layout.storage.exit (.word (Word.ofNatModulo kind)))[layout.storage.world]? = some value
  rw [List.getElem?_set_ne notExit, List.getElem?_set_ne notSize, List.getElem?_set_ne notOffset]
  exact (MemoryCorrespondence.touchStore_other store notMemorySize _ _ _).trans found


theorem terminate_preserves {layout : Layout} {baseline : Nat → Option Value} {slots : List EffectSlot}
    {image : Option (List UInt8)} {handlers : ModeHandlers layout} {anchors : Anchors} {context : Context layout}
    {world : World} {state : Semantics.State RuntimeCallEffectsSemantics.State} {store : Store}
    {scope : Scope} {kind : Nat} {compiled : Core.Expr} {mapping : Renaming} {environment : Environment}
    (accepted : Effects.terminate scope kind (.word Word.zero) (.word Word.zero) = .ok compiled)
    (runtime : EffectEnvironmentRel slots scope mapping environment)
    (passive : RuntimeLogEffectsCorrespondence.Passive layout.toLogLayout slots)
    (memorySizeMember : ⟨"memorySize", .word, layout.storage.memorySize⟩ ∈ slots)
    (exitMember : ⟨"exit", .word, layout.storage.exit⟩ ∈ slots)
    (offsetMember : ⟨"returnOffset", .word, layout.storage.returnOffset⟩ ∈ slots)
    (sizeMember : ⟨"returnSize", .word, layout.storage.returnSize⟩ ∈ slots)
    (before : StateRel (model layout baseline slots image handlers anchors context) world state store) :
    ∃ target final, ResultRel .unit (RuntimeLifecycleSemantics.terminate state.external kind).1 target ∧
      Evaluates environment store (compiled.rename mapping) target final ∧
      StateRel (model layout baseline slots image handlers anchors context) world
        {state with external := (RuntimeLifecycleSemantics.terminate state.external kind).2} final ∧
      ClosuresPreserved store final := by
  have base := base_related before
  have beforeRuntime := RuntimeEnvironmentEffectsCorrespondence.runtime_related
    (RuntimeLogEffectsCorrespondence.runtime_related (RuntimeAccountEffectsCorrespondence.runtime_related
      (RuntimeCallEffectsCorrespondence.account_related base)))
  have memory := RuntimeEffectsCorrespondence.memory_related beforeRuntime
  have storage := RuntimeEffectsCorrespondence.storage_related beforeRuntime
  have executed := TerminationBuiltinCorrespondence.terminate_evaluates accepted runtime
    memorySizeMember exitMember offsetMember sizeMember storage memory.size Word.zero Word.zero
    (fun _ _ => .word) (fun _ _ => .word)
  obtain ⟨result, memoryFinal, storageFinal, frame⟩ :=
    TerminationBuiltinCorrespondence.terminate_state memory storage kind Word.zero Word.zero
  have changed := RuntimeCallEffectsCorrespondence.runtime_updated base
    (RuntimeReturnDataEffectsCorrespondence.runtime_updated passive
      (RuntimeCallEffectsCorrespondence.runtime_related base) memoryFinal storageFinal frame) rfl
  exact ⟨_, _, result, executed, RuntimeChildCallEffectsCorrespondence.of_base changed
      (terminate_linked kind before) ((handlers.context context).updated base changed before.external.2.2.1.2),
    TerminationBuiltinCorrespondence.terminate_closures memory storage kind Word.zero Word.zero⟩

end Solcore.Frontend.RustHull.RuntimeLifecycleCorrespondence
end
