import Solcore.Frontend.RustHull.LinkedEnvironmentWorldCorrespondence
import Solcore.Frontend.RustHull.RuntimeLogEffectsCorrespondence

set_option autoImplicit false
set_option linter.unusedVariables false
namespace Solcore.Frontend.RustHull.LinkedLogWorldCorrespondence
open Correspondence DerivationCorrespondence ScalarExecution RuntimeLogEffectsCorrespondence LinkedBuiltinWorldCorrespondence

private theorem primitive_none {slots : List EffectSlot} {name : String}
    (enabled : supported slots name) (type : Ty) (arguments : List Semantics.Value) :
    Semantics.primitive? name type arguments = none := by
  rcases enabled with ((memory | storage) | environment) | ⟨operation, rfl⟩
  · obtain ⟨operation, rfl⟩ := memory
    cases operation <;> rfl
  · obtain ⟨operation, rfl⟩ := storage
    cases operation with | load transient | store transient => cases transient <;> rfl
  · obtain ⟨operation, rfl, _⟩ := environment
    cases operation <;> (try first | cases ‹EnvironmentSemantics.Direct› | cases ‹EnvironmentSemantics.AmbientWord›)
    all_goals rfl
  · cases operation <;> rfl

private theorem runtime_unsupported (operation : LogsSemantics.Operation)
    (type : Ty) (arguments : List Semantics.Value) (state : RuntimeEnvironmentEffectsSemantics.State) :
    RuntimeEnvironmentEffectsSemantics.builtin operation.name type arguments state = none := by
  cases operation <;> rfl

theorem external_preserves (layout : Layout) (baseline : Nat → Option Core.Value)
    (slots : List EffectSlot) (passive : Passive layout slots)
    (memoryMember : ⟨"memory", Core.WordMapping.type, layout.memory⟩ ∈ slots)
    (worldMember : ⟨"world", AccountState.type, layout.storage.world⟩ ∈ slots)
    (addressMember : ⟨"address", .word, layout.storage.address⟩ ∈ slots)
    (completeMember : ⟨"worldComplete", .bool, layout.storage.complete⟩ ∈ slots)
    (staticMember : ⟨"isStatic", .bool, layout.storage.isStatic⟩ ∈ slots)
    (memorySizeMember : ⟨"memorySize", .word, layout.storage.memorySize⟩ ∈ slots)
    (exitMember : ⟨"exit", .word, layout.storage.exit⟩ ∈ slots)
    (offsetMember : ⟨"returnOffset", .word, layout.storage.returnOffset⟩ ∈ slots)
    (sizeMember : ⟨"returnSize", .word, layout.storage.returnSize⟩ ∈ slots)
    (logsMember : ⟨"logs", Core.WordMapping.type, layout.logs⟩ ∈ slots)
    (logSizeMember : ⟨"logSize", .word, layout.logSize⟩ ∈ slots) :
    ∀ anchors, ExternalWorldPreservation (supported slots) (model layout baseline slots) slots RuntimeLogEffectsSemantics.effects
      anchors layout.storage.world (fun state => state.runtime.runtime.storage.world) := by
  intro anchors
  intro functions name type sources initial final result enabled notFunction called
  cases called with
  | function selected called => rw [notFunction] at selected; contradiction
  | primitive absent computed => rw [primitive_none enabled] at computed; contradiction
  | external absent notPrimitive computed =>
      cases computed with
      | @runtime finalRuntime computed =>
          have runtimeEnabled : RuntimeEnvironmentEffectsCorrespondence.supported slots name := by
            rcases enabled with runtime | ⟨operation, rfl⟩
            · exact runtime
            · rw [runtime_unsupported] at computed
              contradiction
          intro typeFuel expected typeCompiled scope arguments lowered compiled world mapping environment initialStore argumentStore targets codes locations captured related packed runtime state installed linked
          have call : Semantics.EvalCall functions RuntimeEnvironmentEffectsSemantics.effects name type sources
              (sourceRuntime initial) result {sourceRuntime initial with external := finalRuntime} :=
            .external absent notPrimitive computed
          obtain ⟨target, finalStore, evaluated, linkedFinal⟩ :=
            LinkedEnvironmentWorldCorrespondence.external_preserves layout.toLayout (patched layout baseline initial.external)
              slots (passive_runtime passive) memoryMember worldMember addressMember completeMember staticMember
              memorySizeMember exitMember offsetMember sizeMember anchors runtimeEnabled notFunction call
              typeCompiled compiled related packed runtime (runtime_related state) installed linked
          exact ⟨target, finalStore, evaluated, linkedFinal⟩
      | logs computed =>
          cases computed with
          | log operation resultType offset length topics count executed =>
              intro typeFuel expected typeCompiled scope arguments lowered compiled world mapping environment initialStore argumentStore targets codes locations captured related packed runtime state installed linked
              obtain ⟨target, finalStore, resultRelated, evaluated, finalState, frame⟩ :=
                LogBuiltinCorrespondence.preserves operation compiled count executed related runtime
                  memoryMember memorySizeMember logsMember logSizeMember addressMember staticMember exitMember offsetMember sizeMember
                  (logs_related state) packed
              refine ⟨target, finalStore, evaluated, linked.read_preserved ?_⟩
              intro value found
              have joint := layout.jointDistinct
              simp [StorageBuiltinCorrespondence.Locations.all] at joint
              apply frame.preserved _ _ _ found
              simp [logLocations, LogBuiltinCorrespondence.Locations.mutable, LogsCorrespondence.Locations.all]
              simp_all [ne_comm]


end Solcore.Frontend.RustHull.LinkedLogWorldCorrespondence
