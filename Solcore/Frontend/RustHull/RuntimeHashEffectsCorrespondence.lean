import Solcore.Frontend.RustHull.RuntimeHashEffectsSemantics
import Solcore.Frontend.RustHull.RuntimeCopyEffectsCorrespondence
import Solcore.Frontend.RustHull.KeccakBuiltinCorrespondence

/-! Hashing extends the concrete runtime while preserving memory contents,
account state, event snapshots and immutable observations. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.RuntimeHashEffectsCorrespondence
open Correspondence ScalarExecution DerivationCorrespondence
open RuntimeLogEffectsCorrespondence (Layout model Passive)

def supported (slots : List EffectSlot) (name : String) : Prop :=
  RuntimeCopyEffectsCorrespondence.supported slots name ∨ name = "keccak256"

private theorem primitive_none {slots : List EffectSlot} {name : String}
    (enabled : supported slots name) (type : Ty) (arguments : List Semantics.Value) :
    Semantics.primitive? name type arguments = none := by
  rcases enabled with (((((memory | storage) | environment) | logs) | termination) | copy) | rfl
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
  · rfl

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

private theorem runtime_unsupported {type : Ty} {arguments : List Semantics.Value}
    {initial final : RuntimeCopyEffectsSemantics.State} {result : Semantics.Result Semantics.Value}
    (computed : RuntimeCopyEffectsSemantics.Builtin "keccak256" type arguments initial result final) : False := by
  cases computed with
  | runtime computed =>
      cases computed with
      | runtime computed =>
          cases computed with
          | runtime computed => contradiction
          | logs computed =>
              obtain ⟨operation, named⟩ := log_named computed
              cases operation <;> simp [LogsSemantics.Operation.name] at named
      | termination computed => contradiction
  | copy computed =>
      obtain ⟨operation, named⟩ := copy_named computed
      cases operation <;> simp [MemoryCopySemantics.Operation.name] at named

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
    ExternalCallPreservation (supported slots) (model layout baseline slots) slots RuntimeHashEffectsSemantics.effects := by
  intro functions name type sources initial final result enabled notFunction called
  cases called with
  | function selected called => rw [notFunction] at selected; contradiction
  | primitive absent computed => rw [primitive_none enabled] at computed; contradiction
  | external absent notPrimitive computed =>
      cases computed with
      | runtime computed =>
          have runtimeEnabled : RuntimeCopyEffectsCorrespondence.supported slots name := by
            rcases enabled with runtime | rfl
            · exact runtime
            · exact False.elim (runtime_unsupported computed)
          have call : Semantics.EvalCall functions RuntimeCopyEffectsSemantics.effects name type sources initial result _ :=
            .external absent notPrimitive computed
          intro typeFuel expected typeCompiled
          exact RuntimeCopyEffectsCorrespondence.external_preserves layout baseline slots passive
            memoryMember worldMember addressMember completeMember staticMember memorySizeMember exitMember offsetMember sizeMember
            logsMember logSizeMember runtimeEnabled notFunction call typeCompiled
      | hash computed =>
          have named := hash_named computed
          subst name
          intro typeFuel expected typeCompiled scope arguments lowered compiled world mapping environment initialStore argumentStore targets codes locations captured related packed runtime state installed
          have beforeEnvironment := RuntimeLogEffectsCorrespondence.runtime_related state
          have beforeRuntime := RuntimeEnvironmentEffectsCorrespondence.runtime_related beforeEnvironment
          have memoryRelated := RuntimeEffectsCorrespondence.memory_related beforeRuntime
          obtain ⟨target, finalStore, resultRelated, evaluated, memoryFinal, frame⟩ :=
            KeccakBuiltinCorrespondence.preserves compiled computed related runtime memoryMember memorySizeMember memoryRelated packed
          have retained : ClosuresPreserved argumentStore finalStore := MemoryEffectCorrespondence.closures_preserved memoryRelated frame
          exact ⟨target, finalStore, resultRelated, evaluated,
            RuntimeCopyEffectsCorrespondence.memory_updated passive state memoryFinal frame,
            installed.preserved retained, retained⟩

theorem assemble_program (layout : Layout) (baseline : Nat → Option Core.Value)
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
    (logSizeMember : ⟨"logSize", .word, layout.logSize⟩ ∈ slots)
    {functions : List Function} {function : Function} {entry : String} {runtime : Scope}
    {fuel : Nat} {own : Signature} {allocated : Core.Expr}
    (accepted : assemble functions entry runtime fuel = .ok (own, allocated))
    (selected : functions.find? (·.name == entry) = some function)
    (eligible : ExecutableProgram (supported slots) functions)
    {sources : List Semantics.Value} {targets : List Core.Value}
    (values : ValuesRel own.parameters sources targets)
    {initial final : Semantics.State RuntimeLogEffectsSemantics.State}
    {sourceResult : Semantics.Result Semantics.Value}
    (evaluated : Semantics.EvalFunction functions RuntimeHashEffectsSemantics.effects
      function sources initial sourceResult final)
    {world : World} {runtimeValues caller : Core.Environment} {store : Core.Store}
    (runtimeLength : runtimeValues.length = runtime.length)
    (covered : ScopeCoverage [] runtime)
    (runtimeRelated : EffectEnvironmentRel slots runtime Core.Renaming.id
      (runtimeValues ++ bundleValues targets :: caller))
    (separated : EffectSlotsSeparate slots)
    (state : StateRel (model layout baseline slots) world initial store) :
    ∃ extension target finalStore,
      ResultRel own.result sourceResult target ∧
      Core.Evaluates (runtimeValues ++ bundleValues targets :: caller) store allocated target finalStore ∧
      StateRel (model layout baseline slots) (world ++ extension) final finalStore ∧
      ClosuresPreserved store finalStore :=
  assemble_recursive_program_effects accepted selected
    (external_preserves layout baseline slots passive memoryMember worldMember addressMember completeMember staticMember
      memorySizeMember exitMember offsetMember sizeMember logsMember logSizeMember) eligible values evaluated
    runtimeLength covered runtimeRelated separated state

end Solcore.Frontend.RustHull.RuntimeHashEffectsCorrespondence
