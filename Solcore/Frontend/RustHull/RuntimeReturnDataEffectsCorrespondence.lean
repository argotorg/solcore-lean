import Solcore.Frontend.RustHull.RuntimeReturnDataStateCorrespondence
import Solcore.Frontend.RustHull.RuntimeReturnDataSupported
import Solcore.Frontend.RustHull.ReturnDataBuiltinCorrespondence
import Solcore.Frontend.RustHull.MemoryGuardBuiltinCorrespondence

/-! Caller return data, optional code images, and existing runtime effects are
connected to the actual compiler and recursive Hull execution in one model. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.RuntimeReturnDataEffectsCorrespondence
open Correspondence ScalarExecution DerivationCorrespondence

theorem external_preserves (layout : Layout) (baseline : Nat → Option Core.Value)
    (slots : List EffectSlot) (image : Option (List UInt8)) (withCode : Bool) (passive : RuntimeLogEffectsCorrespondence.Passive layout.toLogLayout slots)
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
    (codeMembers : ∀ cells, layout.codeCells = some cells →
      (⟨"code", Core.WordMapping.type, cells.code⟩ ∈ slots ∧ ⟨"codeKnown", .bool, cells.known⟩ ∈ slots))
    (dataMember : ⟨"returnData", Core.WordMapping.type, layout.returnData⟩ ∈ slots)
    (dataSizeMember : ⟨"returnDataSize", .word, layout.returnDataSize⟩ ∈ slots)
    (mode : layout.codeCells.isSome = withCode) :
    ExternalCallPreservation (supported slots withCode) (model layout baseline slots image) slots
      (RuntimeReturnDataEffectsSemantics.effects image) := by
  intro functions name type sources initial final result enabled notFunction called
  cases called with
  | function selected called => rw [notFunction] at selected; contradiction
  | primitive absent computed => rw [primitive_none enabled] at computed; contradiction
  | external absent notPrimitive computed =>
      cases computed with
      | runtime computed =>
          have sizeEqual := congrArg (fun environment => environment.direct .returnDataSize)
            (RuntimeReturnDataEffectsSemantics.runtime_environment computed)
          intro typeFuel expected typeCompiled scope arguments lowered compiled world mapping environment initialStore argumentStore targets codes locations captured related packed runtime state installed
          cases present : layout.codeCells with
          | some cells =>
              let codeLayout : RuntimeCodeEffectsCorrespondence.Layout :=
                { toAccountLayout := layout.toAccountLayout
                  code := cells.code, known := cells.known
                  codeBelow := cells.codeBelow, knownBelow := cells.knownBelow
                  codeOutside := cells.codeOutside, knownOutside := cells.knownOutside }
              have beforeAccount := account_related state
              have codeState : StateRel (RuntimeCodeEffectsCorrespondence.model codeLayout
                  (patched layout baseline initial.external) slots image) world (sourceRuntime initial) argumentStore :=
                ⟨beforeAccount.toHeapRel, beforeAccount.external.1, beforeAccount.external.2.1,
                  beforeAccount.external.2.2, state.external.2.2.2.2.2 cells present⟩
              have call : Semantics.EvalCall functions (RuntimeCodeEffectsSemantics.effects image) name type sources
                  (sourceRuntime initial) result _ := .external absent notPrimitive computed
              obtain ⟨target, finalStore, resultRelated, evaluated, finalState, installedFinal, retained⟩ :=
                RuntimeCodeEffectsCorrespondence.external_preserves codeLayout
                  (patched layout baseline initial.external) slots image passive
                  memoryMember worldMember addressMember completeMember staticMember memorySizeMember exitMember offsetMember sizeMember
                  logsMember logSizeMember balancesMember (codeMembers cells present).1 (codeMembers cells present).2
                  (runtime_enabled enabled computed) notFunction call typeCompiled compiled related packed runtime codeState installed
              exact ⟨target, finalStore, resultRelated, evaluated,
                account_updated state (RuntimeCodeEffectsCorrespondence.account_related finalState) sizeEqual,
                installedFinal, retained⟩
          | none =>
              have disabled : withCode = false := by simpa only [present, Option.isSome_none] using mode.symm
              have accountEnabled := account_enabled (disabled ▸ enabled) computed
              cases computed with
              | runtime computed =>
                  have call : Semantics.EvalCall functions RuntimeAccountEffectsSemantics.effects name type sources
                      (sourceRuntime initial) result _ := .external absent notPrimitive computed
                  obtain ⟨target, finalStore, resultRelated, evaluated, finalState, installedFinal, retained⟩ :=
                    RuntimeAccountEffectsCorrespondence.external_preserves layout.toAccountLayout
                      (patched layout baseline initial.external) slots passive
                      memoryMember worldMember addressMember completeMember staticMember memorySizeMember exitMember offsetMember sizeMember
                      logsMember logSizeMember balancesMember accountEnabled notFunction call typeCompiled compiled related packed runtime
                      (account_related state) installed
                  exact ⟨target, finalStore, resultRelated, evaluated, account_updated state finalState sizeEqual,
                    installedFinal, retained⟩
              | copy computed =>
                  obtain ⟨operation, named⟩ := computed.named
                  subst name
                  exact False.elim (code_unsupported operation accountEnabled)
      | copy computed =>
          have named := computed.named
          subst name
          intro typeFuel expected typeCompiled scope arguments lowered compiled world mapping environment initialStore argumentStore targets codes locations captured related packed runtime state installed
          have beforeAccount := account_related state
          have beforeLog := RuntimeAccountEffectsCorrespondence.runtime_related beforeAccount
          have beforeEnvironment := RuntimeLogEffectsCorrespondence.runtime_related beforeLog
          have beforeRuntime := RuntimeEnvironmentEffectsCorrespondence.runtime_related beforeEnvironment
          obtain ⟨target, finalStore, resultRelated, evaluated, memoryFinal, storageFinal, frame, retained⟩ :=
            ReturnDataBuiltinCorrespondence.preserves compiled computed related runtime
              memoryMember memorySizeMember exitMember offsetMember sizeMember dataMember dataSizeMember
              (data_related state) (size_related state)
              (RuntimeEffectsCorrespondence.memory_related beforeRuntime)
              (RuntimeEffectsCorrespondence.storage_related beforeRuntime) packed
          exact ⟨target, finalStore, resultRelated, evaluated,
            runtime_updated passive state memoryFinal storageFinal frame, installed.preserved retained, retained⟩
      | guard computed =>
          have named := computed.named
          subst name
          intro typeFuel expected typeCompiled scope arguments lowered compiled world mapping environment initialStore argumentStore targets codes locations captured related packed runtime state installed
          obtain ⟨target, resultRelated, evaluated⟩ := MemoryGuardBuiltinCorrespondence.preserves compiled computed related packed
          exact ⟨target, argumentStore, resultRelated, evaluated, state, installed, ClosuresPreserved.refl _⟩

theorem assemble_program (layout : Layout) (baseline : Nat → Option Core.Value)
    (slots : List EffectSlot) (image : Option (List UInt8)) (withCode : Bool) (passive : RuntimeLogEffectsCorrespondence.Passive layout.toLogLayout slots)
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
    (codeMembers : ∀ cells, layout.codeCells = some cells →
      (⟨"code", Core.WordMapping.type, cells.code⟩ ∈ slots ∧ ⟨"codeKnown", .bool, cells.known⟩ ∈ slots))
    (dataMember : ⟨"returnData", Core.WordMapping.type, layout.returnData⟩ ∈ slots)
    (dataSizeMember : ⟨"returnDataSize", .word, layout.returnDataSize⟩ ∈ slots)
    (mode : layout.codeCells.isSome = withCode)
    {functions : List Function} {function : Function} {entry : String} {runtime : Scope}
    {fuel : Nat} {own : Signature} {allocated : Core.Expr}
    (accepted : assemble functions entry runtime fuel = .ok (own, allocated))
    (selected : functions.find? (·.name == entry) = some function)
    (eligible : ExecutableProgram (supported slots withCode) functions)
    {sources : List Semantics.Value} {targets : List Core.Value}
    (values : ValuesRel own.parameters sources targets)
    {initial final : Semantics.State RuntimeReturnDataEffectsSemantics.State}
    {sourceResult : Semantics.Result Semantics.Value}
    (evaluated : Semantics.EvalFunction functions (RuntimeReturnDataEffectsSemantics.effects image)
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
    (external_preserves layout baseline slots image withCode passive memoryMember worldMember addressMember completeMember staticMember
      memorySizeMember exitMember offsetMember sizeMember logsMember logSizeMember balancesMember codeMembers dataMember dataSizeMember mode) eligible values evaluated
    runtimeLength covered runtimeRelated separated state


end Solcore.Frontend.RustHull.RuntimeReturnDataEffectsCorrespondence
