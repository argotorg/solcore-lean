import Solcore.Frontend.RustHull.RuntimeLifecycleSemantics
import Solcore.Frontend.RustHull.RuntimeCallModeStateCorrespondence
import Solcore.Frontend.RustHull.RuntimeChildCallCallbackCorrespondence
import Solcore.Frontend.RustHull.RuntimeCallCallbackCorrespondence
import Solcore.Frontend.RustHull.TerminationBuiltinCorrespondence

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
