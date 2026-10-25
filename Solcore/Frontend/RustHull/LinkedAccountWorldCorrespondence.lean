import Solcore.Frontend.RustHull.RuntimeAccountEffectsCorrespondence
import Solcore.Frontend.RustHull.LinkedHashWorldCorrespondence

/-! Exact catalog links survive the concrete account/image inspection leaves. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.LinkedAccountWorldCorrespondence
open Correspondence ScalarExecution DerivationCorrespondence
open RuntimeAccountEffectsCorrespondence
open LinkedBuiltinWorldCorrespondence

private theorem primitive_none {slots : List EffectSlot} {name : String}
    (enabled : supported slots name) (type : Ty) (arguments : List Semantics.Value) :
    Semantics.primitive? name type arguments = none := by
  rcases enabled with ((((((memory | storage) | environment) | logs) | termination) | copy) | hash) | ⟨operation, rfl⟩
  · obtain ⟨operation, rfl⟩ := memory
    cases operation <;> rfl
  · obtain ⟨operation, rfl⟩ := storage
    cases operation with | load transient | store transient => cases transient <;> rfl
  · obtain ⟨operation, rfl, _⟩ := environment
    cases operation <;> (try first | cases ‹EnvironmentSemantics.Direct› | cases ‹EnvironmentSemantics.AmbientWord›)
    all_goals rfl
  · obtain ⟨operation, rfl⟩ := logs
    cases operation <;> rfl
  · obtain ⟨operation, rfl⟩ := termination
    cases operation <;> rfl
  · obtain ⟨operation, rfl, _⟩ := copy
    cases operation <;> rfl
  · subst name
    rfl
  · cases operation <;> rfl

private theorem copy_named {calldata : MemorySemantics.Entries} {name : String} {type : Ty}
    {arguments : List Semantics.Value} {initial final : MemorySemantics.State} {result : Semantics.Result Semantics.Value}
    (computed : MemoryCopySemantics.Builtin calldata name type arguments initial result final) :
    ∃ operation : MemoryCopySemantics.Operation, operation.name = name := by
  cases computed with
  | move _ => exact ⟨.move, rfl⟩
  | calldata _ => exact ⟨.calldata, rfl⟩

private theorem log_named {name : String} {type : Ty} {arguments : List Semantics.Value}
    {initial final : LogsSemantics.State} {result : Semantics.Result Semantics.Value}
    (computed : LogsSemantics.Builtin name type arguments initial result final) :
    ∃ operation : LogsSemantics.Operation, operation.name = name := by
  cases computed with | log operation _ _ _ _ _ _ => exact ⟨operation, rfl⟩

private theorem hash_named {name : String} {type : Ty} {arguments : List Semantics.Value}
    {initial final : MemorySemantics.State} {result : Semantics.Result Semantics.Value}
    (computed : KeccakSemantics.Builtin name type arguments initial result final) : name = "keccak256" := by
  cases computed
  rfl

private theorem runtime_unsupported (operation : AccountObservationSemantics.Operation)
    {type : Ty} {arguments : List Semantics.Value} {initial final : RuntimeHashEffectsSemantics.State}
    {result : Semantics.Result Semantics.Value}
    (computed : RuntimeHashEffectsSemantics.Builtin operation.name type arguments initial result final) : False := by
  cases computed with
  | runtime computed =>
      cases computed with
      | runtime computed =>
          cases computed with
          | runtime computed =>
              cases computed with
              | runtime computed =>
                  have missing : RuntimeEnvironmentEffectsSemantics.builtin operation.name type arguments initial.runtime = none := by
                    cases operation <;> rfl
                  rw [missing] at computed
                  contradiction
              | logs computed =>
                  obtain ⟨log, named⟩ := log_named computed
                  cases operation <;> cases log <;> simp [AccountObservationSemantics.Operation.name, LogsSemantics.Operation.name] at named
          | termination computed =>
              have missing : TerminationSemantics.builtin operation.name type arguments initial.runtime.runtime = none := by
                cases operation <;> rfl
              rw [missing] at computed
              contradiction
      | copy computed =>
          obtain ⟨copy, named⟩ := copy_named computed
          cases operation <;> cases copy <;> simp [AccountObservationSemantics.Operation.name, MemoryCopySemantics.Operation.name] at named
  | hash computed =>
      have named := hash_named computed
      cases operation <;> simp [AccountObservationSemantics.Operation.name] at named

theorem external_preserves (layout : Layout) (baseline : Nat → Option Core.Value)
    (slots : List EffectSlot) (passive : RuntimeLogEffectsCorrespondence.Passive layout.toLogLayout slots)
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
    (logSizeMember : ⟨"logSize", .word, layout.logSize⟩ ∈ slots)
    (balancesMember : ⟨"balances", Core.WordMapping.type, layout.balances⟩ ∈ slots) :
    ∀ anchors, ExternalWorldPreservation (supported slots) (model layout baseline slots) slots RuntimeAccountEffectsSemantics.effects
      anchors layout.storage.world (fun state => state.runtime.runtime.runtime.storage.world) := by
  intro anchors
  intro functions name type sources initial final result enabled notFunction called
  cases called with
  | function selected called => rw [notFunction] at selected; contradiction
  | primitive absent computed => rw [primitive_none enabled] at computed; contradiction
  | external absent notPrimitive computed =>
      cases computed with
      | runtime computed =>
          have runtimeEnabled : RuntimeHashEffectsCorrespondence.supported slots name := by
            rcases enabled with runtime | ⟨operation, rfl⟩
            · exact runtime
            · exact False.elim (runtime_unsupported operation computed)
          have call : Semantics.EvalCall functions RuntimeHashEffectsSemantics.effects name type sources
              (sourceRuntime initial) result _ := .external absent notPrimitive computed
          intro typeFuel expected typeCompiled scope arguments lowered compiled world mapping environment initialStore argumentStore targets codes locations captured related packed runtime state installed linked
          obtain ⟨target, finalStore, evaluated, finalLinked⟩ :=
            LinkedHashWorldCorrespondence.external_preserves layout.toLogLayout baseline slots passive
              memoryMember worldMember addressMember completeMember staticMember memorySizeMember exitMember offsetMember sizeMember
              logsMember logSizeMember anchors runtimeEnabled notFunction call typeCompiled compiled related packed runtime (runtime_related state) installed linked
          exact ⟨target, finalStore, evaluated, finalLinked⟩
      | observation computed =>
          obtain ⟨operation, named⟩ := computed.named
          subst name
          intro typeFuel expected typeCompiled scope arguments lowered compiled world mapping environment initialStore argumentStore targets codes locations captured related packed runtime state installed linked
          have beforeLog := runtime_related state
          have beforeEnvironment := RuntimeLogEffectsCorrespondence.runtime_related beforeLog
          have beforeRuntime := RuntimeEnvironmentEffectsCorrespondence.runtime_related beforeEnvironment
          have memoryRelated := RuntimeEffectsCorrespondence.memory_related beforeRuntime
          have storageRelated := RuntimeEffectsCorrespondence.storage_related beforeRuntime
          obtain ⟨target, finalStore, resultRelated, evaluated, memoryFinal, frame⟩ :=
            AccountObservationBuiltinCorrespondence.preserves operation compiled computed related runtime
              memoryMember memorySizeMember worldMember addressMember completeMember balancesMember
              memoryRelated storageRelated (balances_related state) packed
          exact ⟨target, finalStore, evaluated, memory_frame linked frame⟩

end Solcore.Frontend.RustHull.LinkedAccountWorldCorrespondence
