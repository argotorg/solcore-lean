import Solcore.Frontend.RustHull.LinkedBuiltinWorldSupport

set_option autoImplicit false
namespace Solcore.Frontend.RustHull.LinkedRuntimeWorldCorrespondence
open Correspondence DerivationCorrespondence ScalarExecution RuntimeEffectsCorrespondence LinkedBuiltinWorldCorrespondence

private theorem memory_unsupported (operation : StorageBuiltinCorrespondence.Operation)
    (type : Ty) (arguments : List Semantics.Value) (state : MemorySemantics.State) :
    MemorySemantics.builtin operation.name type arguments state = none := by
  cases operation with | load transient | store transient => cases transient <;> rfl

theorem external_preserves (layout : Layout) (baseline : Nat → Option Core.Value)
    (slots : List EffectSlot)
    (memoryMember : ⟨"memory", Core.WordMapping.type, layout.memory⟩ ∈ slots)
    (worldMember : ⟨"world", AccountState.type, layout.storage.world⟩ ∈ slots)
    (addressMember : ⟨"address", .word, layout.storage.address⟩ ∈ slots)
    (completeMember : ⟨"worldComplete", .bool, layout.storage.complete⟩ ∈ slots)
    (staticMember : ⟨"isStatic", .bool, layout.storage.isStatic⟩ ∈ slots)
    (memorySizeMember : ⟨"memorySize", .word, layout.storage.memorySize⟩ ∈ slots)
    (exitMember : ⟨"exit", .word, layout.storage.exit⟩ ∈ slots)
    (offsetMember : ⟨"returnOffset", .word, layout.storage.returnOffset⟩ ∈ slots)
    (sizeMember : ⟨"returnSize", .word, layout.storage.returnSize⟩ ∈ slots) :
    ∀ anchors, ExternalWorldPreservation supported (model layout baseline) slots RuntimeEffectsSemantics.effects
      anchors layout.storage.world (fun state => state.storage.world) := by
  intro anchors
  intro functions name type sources initial final result available notFunction called
  rcases available with memory | storage
  · obtain ⟨operation, rfl⟩ := memory
    cases called with
    | function selected called => rw [notFunction] at selected; contradiction
    | primitive absent computed =>
        cases operation <;> simp [MemoryBuiltinCorrespondence.Operation.name, Semantics.primitive?] at computed
    | external absent notPrimitive computed =>
        intro typeFuel expected typeCompiled scope arguments lowered compiled world mapping environment initialStore argumentStore targets codes locations captured related packed runtime state installed linked
        obtain ⟨computedResult, computedState, target, finalStore, meaning, resultRelated, evaluated, memoryFinal, frame⟩ :=
          MemoryBuiltinCorrespondence.preserves operation compiled related runtime memoryMember memorySizeMember
            (memory_related state) packed type
        have combined : RuntimeEffectsSemantics.builtin operation.name type sources initial.external =
            some (computedResult, {initial.external with memory := computedState}) := by
          simp only [RuntimeEffectsSemantics.builtin, meaning]
        have same := Option.some.inj (computed.symm.trans combined)
        cases same
        exact ⟨target, finalStore, evaluated, memory_frame linked frame⟩
  · obtain ⟨operation, rfl⟩ := storage
    cases called with
    | function selected called => rw [notFunction] at selected; contradiction
    | primitive absent computed =>
        cases operation with | load transient | store transient =>
          cases transient <;> simp [StorageBuiltinCorrespondence.Operation.name, Semantics.primitive?] at computed
    | external absent notPrimitive computed =>
        intro typeFuel expected typeCompiled scope arguments lowered compiled world mapping environment initialStore argumentStore targets codes locations captured related packed runtime state installed linked
        obtain ⟨computedResult, computedState, target, finalStore, meaning, resultRelated, evaluated, linkedFinal⟩ :=
          LinkedStorageBuiltinCorrespondence.preserves operation compiled related runtime worldMember addressMember
            completeMember staticMember memorySizeMember exitMember offsetMember sizeMember
            (storage_related state) linked packed type
        have combined : RuntimeEffectsSemantics.builtin operation.name type sources initial.external =
            some (computedResult, {initial.external with storage := computedState}) := by
          simp only [RuntimeEffectsSemantics.builtin, memory_unsupported, meaning, Option.map_some]
        have same := Option.some.inj (computed.symm.trans combined)
        cases same
        exact ⟨target, finalStore, evaluated, linkedFinal⟩

end Solcore.Frontend.RustHull.LinkedRuntimeWorldCorrespondence
