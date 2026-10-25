import Solcore.Frontend.RustHull.RuntimeCodeStateCorrespondence
import Solcore.Frontend.RustHull.RuntimeCodeEffectsSemantics
import Solcore.Frontend.RustHull.CodeImageBuiltinCorrespondence

/-! Linked image copying composes with the existing runtime semantics before
actual function assembly and public execution. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.RuntimeCodeEffectsCorrespondence
open Correspondence ScalarExecution DerivationCorrespondence

def supported (slots : List EffectSlot) (name : String) : Prop :=
  RuntimeAccountEffectsCorrespondence.supported slots name ∨
    ∃ operation : CodeImageSemantics.Operation, operation.name = name

private theorem primitive_none {slots : List EffectSlot} {name : String}
    (enabled : supported slots name) (type : Ty) (arguments : List Semantics.Value) :
    Semantics.primitive? name type arguments = none := by
  rcases enabled with (((((((memory | storage) | environment) | logs) | termination) | copy) | hash) | account) | ⟨operation, rfl⟩
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
  · obtain ⟨operation, rfl⟩ := account
    cases operation <;> rfl
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

private theorem hash_runtime_unsupported (operation : CodeImageSemantics.Operation)
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
                  cases operation <;> cases log <;> simp [CodeImageSemantics.Operation.name, LogsSemantics.Operation.name] at named
          | termination computed =>
              have missing : TerminationSemantics.builtin operation.name type arguments initial.runtime.runtime = none := by
                cases operation <;> rfl
              rw [missing] at computed
              contradiction
      | copy computed =>
          obtain ⟨copy, named⟩ := copy_named computed
          cases operation <;> cases copy <;> simp [CodeImageSemantics.Operation.name, MemoryCopySemantics.Operation.name] at named
  | hash computed =>
      have named := hash_named computed
      cases operation <;> simp [CodeImageSemantics.Operation.name] at named

private theorem runtime_unsupported (operation : CodeImageSemantics.Operation)
    {type : Ty} {arguments : List Semantics.Value} {initial final : RuntimeAccountEffectsSemantics.State}
    {result : Semantics.Result Semantics.Value}
    (computed : RuntimeAccountEffectsSemantics.Builtin operation.name type arguments initial result final) : False := by
  cases computed with
  | runtime computed => exact hash_runtime_unsupported operation computed
  | observation computed =>
      obtain ⟨observation, named⟩ := computed.named
      cases operation <;> cases observation <;>
        simp [CodeImageSemantics.Operation.name, AccountObservationSemantics.Operation.name] at named

theorem external_preserves (layout : Layout) (baseline : Nat → Option Core.Value)
    (slots : List EffectSlot) (image : Option (List UInt8)) (passive : RuntimeLogEffectsCorrespondence.Passive layout.toLogLayout slots)
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
    (balancesMember : ⟨"balances", Core.WordMapping.type, layout.balances⟩ ∈ slots)
    (codeMember : ⟨"code", Core.WordMapping.type, layout.code⟩ ∈ slots)
    (knownMember : ⟨"codeKnown", .bool, layout.known⟩ ∈ slots) :
    ExternalCallPreservation (supported slots) (model layout baseline slots image) slots (RuntimeCodeEffectsSemantics.effects image) := by
  intro functions name type sources initial final result enabled notFunction called
  cases called with
  | function selected called => rw [notFunction] at selected; contradiction
  | primitive absent computed => rw [primitive_none enabled] at computed; contradiction
  | external absent notPrimitive computed =>
      cases computed with
      | runtime computed =>
          have runtimeEnabled : RuntimeAccountEffectsCorrespondence.supported slots name := by
            rcases enabled with runtime | ⟨operation, rfl⟩
            · exact runtime
            · exact False.elim (runtime_unsupported operation computed)
          have call : Semantics.EvalCall functions RuntimeAccountEffectsSemantics.effects name type sources
              initial result _ := .external absent notPrimitive computed
          intro typeFuel expected typeCompiled scope arguments lowered compiled world mapping environment initialStore argumentStore targets codes locations captured related packed runtime state installed
          obtain ⟨target, finalStore, resultRelated, evaluated, finalState, installedFinal, retained⟩ :=
            RuntimeAccountEffectsCorrespondence.external_preserves layout.toAccountLayout baseline slots passive
              memoryMember worldMember addressMember completeMember staticMember memorySizeMember exitMember offsetMember sizeMember
              logsMember logSizeMember balancesMember runtimeEnabled notFunction call typeCompiled compiled related packed runtime (account_related state) installed
          exact ⟨target, finalStore, resultRelated, evaluated, account_updated state finalState, installedFinal, retained⟩
      | copy computed =>
          obtain ⟨operation, named⟩ := computed.named
          subst name
          intro typeFuel expected typeCompiled scope arguments lowered compiled world mapping environment initialStore argumentStore targets codes locations captured related packed runtime state installed
          have beforeAccount := account_related state
          have beforeLog := RuntimeAccountEffectsCorrespondence.runtime_related beforeAccount
          have beforeEnvironment := RuntimeLogEffectsCorrespondence.runtime_related beforeLog
          have beforeRuntime := RuntimeEnvironmentEffectsCorrespondence.runtime_related beforeEnvironment
          have memoryRelated := RuntimeEffectsCorrespondence.memory_related beforeRuntime
          obtain ⟨target, finalStore, resultRelated, evaluated, memoryFinal, frame⟩ :=
            CodeImageBuiltinCorrespondence.preserves operation compiled computed related runtime
              memoryMember memorySizeMember codeMember knownMember
              (code_related state) (known_related state) memoryRelated packed
          have retained : ClosuresPreserved argumentStore finalStore := MemoryEffectCorrespondence.closures_preserved memoryRelated frame
          exact ⟨target, finalStore, resultRelated, evaluated, memory_updated passive state memoryFinal frame,
            installed.preserved retained, retained⟩

theorem assemble_program (layout : Layout) (baseline : Nat → Option Core.Value)
    (slots : List EffectSlot) (image : Option (List UInt8)) (passive : RuntimeLogEffectsCorrespondence.Passive layout.toLogLayout slots)
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
    (balancesMember : ⟨"balances", Core.WordMapping.type, layout.balances⟩ ∈ slots)
    (codeMember : ⟨"code", Core.WordMapping.type, layout.code⟩ ∈ slots)
    (knownMember : ⟨"codeKnown", .bool, layout.known⟩ ∈ slots)
    {functions : List Function} {function : Function} {entry : String} {runtime : Scope}
    {fuel : Nat} {own : Signature} {allocated : Core.Expr}
    (accepted : assemble functions entry runtime fuel = .ok (own, allocated))
    (selected : functions.find? (·.name == entry) = some function)
    (eligible : ExecutableProgram (supported slots) functions)
    {sources : List Semantics.Value} {targets : List Core.Value}
    (values : ValuesRel own.parameters sources targets)
    {initial final : Semantics.State RuntimeAccountEffectsSemantics.State}
    {sourceResult : Semantics.Result Semantics.Value}
    (evaluated : Semantics.EvalFunction functions (RuntimeCodeEffectsSemantics.effects image)
      function sources initial sourceResult final)
    {world : World} {runtimeValues caller : Core.Environment} {store : Core.Store}
    (runtimeLength : runtimeValues.length = runtime.length)
    (covered : ScopeCoverage [] runtime)
    (runtimeRelated : EffectEnvironmentRel slots runtime Core.Renaming.id
      (runtimeValues ++ bundleValues targets :: caller))
    (separated : EffectSlotsSeparate slots)
    (state : StateRel (model layout baseline slots image) world initial store) :
    ∃ extension target finalStore,
      ResultRel own.result sourceResult target ∧
      Core.Evaluates (runtimeValues ++ bundleValues targets :: caller) store allocated target finalStore ∧
      StateRel (model layout baseline slots image) (world ++ extension) final finalStore ∧
      ClosuresPreserved store finalStore :=
  assemble_recursive_program_effects accepted selected
    (external_preserves layout baseline slots image passive memoryMember worldMember addressMember completeMember staticMember
      memorySizeMember exitMember offsetMember sizeMember logsMember logSizeMember balancesMember codeMember knownMember) eligible values evaluated
    runtimeLength covered runtimeRelated separated state

end Solcore.Frontend.RustHull.RuntimeCodeEffectsCorrespondence
