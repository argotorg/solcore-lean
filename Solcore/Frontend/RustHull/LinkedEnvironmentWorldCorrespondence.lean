import Solcore.Frontend.RustHull.LinkedRuntimeWorldCorrespondence
import Solcore.Frontend.RustHull.RuntimeEnvironmentEffectsCorrespondence

set_option autoImplicit false
set_option linter.unusedVariables false
namespace Solcore.Frontend.RustHull.LinkedEnvironmentWorldCorrespondence
open Correspondence DerivationCorrespondence ScalarExecution RuntimeEnvironmentEffectsCorrespondence LinkedBuiltinWorldCorrespondence

private theorem environment_unsupported {name : String} (available : RuntimeEffectsCorrespondence.supported name)
    (type : Ty) (arguments : List Semantics.Value) (state : EnvironmentSemantics.State) :
    EnvironmentSemantics.builtin name type arguments state = none := by
  rcases available with ⟨operation, rfl⟩ | ⟨operation, rfl⟩
  · cases operation <;> rfl
  · cases operation with | load transient | store transient => cases transient <;> rfl

private theorem runtime_unsupported (operation : EnvironmentSemantics.Operation)
    (type : Ty) (arguments : List Semantics.Value) (state : RuntimeEffectsSemantics.State) :
    RuntimeEffectsSemantics.builtin operation.name type arguments state = none := by
  cases operation <;> (try first | cases ‹EnvironmentSemantics.Direct› | cases ‹EnvironmentSemantics.AmbientWord›)
  all_goals rfl

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
    (sizeMember : ⟨"returnSize", .word, layout.storage.returnSize⟩ ∈ slots) :
    ∀ anchors, ExternalWorldPreservation (supported slots) (model layout baseline slots) slots RuntimeEnvironmentEffectsSemantics.effects
      anchors layout.storage.world (fun state => state.runtime.storage.world) := by
  intro anchors
  intro functions name type sources initial final result enabled notFunction called
  rcases enabled with runtimeEnabled | ⟨operation, rfl, available⟩
  · cases called with
    | function selected called => rw [notFunction] at selected; contradiction
    | primitive absent computed =>
        rcases runtimeEnabled with ⟨operation, rfl⟩ | ⟨operation, rfl⟩
        · cases operation <;> simp [MemoryBuiltinCorrespondence.Operation.name, Semantics.primitive?] at computed
        · cases operation with | load transient | store transient =>
            cases transient <;> simp [StorageBuiltinCorrespondence.Operation.name, Semantics.primitive?] at computed
    | external absent notPrimitive computed =>
        change RuntimeEnvironmentEffectsSemantics.builtin _ _ _ _ = some _ at computed
        cases runtimeComputed : RuntimeEffectsSemantics.builtin name type sources initial.external.runtime with
        | none =>
            simp [RuntimeEnvironmentEffectsSemantics.builtin, runtimeComputed,
              environment_unsupported runtimeEnabled] at computed
        | some output =>
            rcases output with ⟨runtimeResult, runtimeState⟩
            simp only [RuntimeEnvironmentEffectsSemantics.builtin, runtimeComputed, Option.some.injEq,
              Prod.mk.injEq] at computed
            rcases computed with ⟨rfl, rfl⟩
            intro typeFuel expected typeCompiled scope arguments lowered compiled world mapping environment initialStore argumentStore targets codes locations captured related packed runtime state installed linked
            have call : Semantics.EvalCall functions RuntimeEffectsSemantics.effects name type sources
                (sourceRuntime initial) runtimeResult {sourceRuntime initial with external := runtimeState} :=
              .external absent notPrimitive runtimeComputed
            obtain ⟨target, finalStore, evaluated, linkedFinal⟩ :=
              LinkedRuntimeWorldCorrespondence.external_preserves layout baseline slots memoryMember worldMember
                addressMember completeMember staticMember memorySizeMember exitMember offsetMember sizeMember anchors
                runtimeEnabled notFunction call typeCompiled compiled related packed runtime (runtime_related state) installed linked
            exact ⟨target, finalStore, evaluated, linkedFinal⟩
  · cases called with
    | function selected called => rw [notFunction] at selected; contradiction
    | primitive absent computed =>
        cases operation <;> (try first | cases ‹EnvironmentSemantics.Direct› | cases ‹EnvironmentSemantics.AmbientWord›)
        all_goals simp [EnvironmentSemantics.Operation.name, EnvironmentSemantics.Direct.name,
          EnvironmentSemantics.AmbientWord.name, Semantics.primitive?] at computed
    | external absent notPrimitive computed =>
        intro typeFuel expected typeCompiled scope arguments lowered compiled world mapping environment initialStore argumentStore targets codes locations captured related packed runtime state installed linked
        obtain ⟨computedResult, target, finalStore, meaning, resultRelated, evaluated, observations, retained⟩ :=
          EnvironmentBuiltinCorrespondence.preserves operation compiled related runtime available
            (observations_related state) packed type
        have combined : RuntimeEnvironmentEffectsSemantics.builtin operation.name type sources initial.external =
            some (computedResult, initial.external) := by
          simp only [RuntimeEnvironmentEffectsSemantics.builtin, runtime_unsupported, meaning, Option.map_some]
        have same := Option.some.inj (computed.symm.trans combined)
        cases same
        exact ⟨target, finalStore, evaluated, linked.retained retained⟩

end Solcore.Frontend.RustHull.LinkedEnvironmentWorldCorrespondence
