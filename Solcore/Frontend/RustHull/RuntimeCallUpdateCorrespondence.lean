import Solcore.Frontend.RustHull.RuntimeCallResourcesCorrespondence

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
