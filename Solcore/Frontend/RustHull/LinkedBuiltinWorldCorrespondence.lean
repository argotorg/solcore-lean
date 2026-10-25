import Solcore.Frontend.RustHull.RuntimeReturnDataEffectsCorrespondence
import Solcore.Frontend.RustHull.LinkedCodeWorldCorrespondence
import Solcore.Frontend.RustHull.ReadOnlyWorldBuiltinCorrespondence

/-! Exact executable catalog IDs survive every call-free runtime operation. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.LinkedBuiltinWorldCorrespondence
open Correspondence ScalarExecution DerivationCorrespondence
open RuntimeReturnDataEffectsCorrespondence

private theorem copy_world {entries : MemorySemantics.Entries} {size : Core.Word} {name : String} {type : Ty}
    {arguments : List Semantics.Value} {initial final : RuntimeEffectsSemantics.State} {result : Semantics.Result Semantics.Value}
    (called : ReturnDataSemantics.Builtin entries size name type arguments initial result final) :
    final.storage.world = initial.storage.world := by
  cases called with
  | copy executed => cases executed <;> rfl

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
    ∀ anchors, ExternalWorldPreservation (supported slots withCode) (model layout baseline slots image) slots
      (RuntimeReturnDataEffectsSemantics.effects image) anchors layout.storage.world
      (fun state => state.runtime.runtime.runtime.runtime.storage.world) := by
  intro anchors
  intro functions name type sources initial final result enabled notFunction called
  cases called with
  | function selected called => rw [notFunction] at selected; contradiction
  | primitive absent computed => rw [primitive_none enabled] at computed; contradiction
  | external absent notPrimitive computed =>
      cases computed with
      | runtime computed =>
          have sizeEqual := congrArg (fun environment => environment.direct .returnDataSize)
            (RuntimeReturnDataEffectsSemantics.runtime_environment computed)
          intro typeFuel expected typeCompiled scope arguments lowered compiled world mapping environment initialStore argumentStore targets codes locations captured related packed runtime state installed linked
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
              obtain ⟨target, finalStore, evaluated, finalLinked⟩ :=
                LinkedCodeWorldCorrespondence.external_preserves codeLayout
                  (patched layout baseline initial.external) slots image passive
                  memoryMember worldMember addressMember completeMember staticMember memorySizeMember exitMember offsetMember sizeMember
                  logsMember logSizeMember balancesMember (codeMembers cells present).1 (codeMembers cells present).2 anchors
                  (runtime_enabled enabled computed) notFunction call typeCompiled compiled related packed runtime codeState installed linked
              exact ⟨target, finalStore, evaluated, finalLinked⟩
          | none =>
              have disabled : withCode = false := by simpa only [present, Option.isSome_none] using mode.symm
              have accountEnabled := account_enabled (disabled ▸ enabled) computed
              cases computed with
              | runtime computed =>
                  have call : Semantics.EvalCall functions RuntimeAccountEffectsSemantics.effects name type sources
                      (sourceRuntime initial) result _ := .external absent notPrimitive computed
                  obtain ⟨target, finalStore, evaluated, finalLinked⟩ :=
                    LinkedAccountWorldCorrespondence.external_preserves layout.toAccountLayout
                      (patched layout baseline initial.external) slots passive
                      memoryMember worldMember addressMember completeMember staticMember memorySizeMember exitMember offsetMember sizeMember
                      logsMember logSizeMember balancesMember anchors accountEnabled notFunction call typeCompiled compiled related packed runtime
                      (account_related state) installed linked
                  exact ⟨target, finalStore, evaluated, finalLinked⟩
              | copy computed =>
                  obtain ⟨operation, named⟩ := computed.named
                  subst name
                  exact False.elim (code_unsupported operation accountEnabled)
      | copy computed =>
          have named := computed.named
          subst name
          intro typeFuel expected typeCompiled scope arguments lowered compiled world mapping environment initialStore argumentStore targets codes locations captured related packed runtime state installed linked
          have beforeAccount := account_related state
          have beforeLog := RuntimeAccountEffectsCorrespondence.runtime_related beforeAccount
          have beforeEnvironment := RuntimeLogEffectsCorrespondence.runtime_related beforeLog
          have beforeRuntime := RuntimeEnvironmentEffectsCorrespondence.runtime_related beforeEnvironment
          obtain ⟨target, finalStore, resultRelated, evaluated, memoryFinal, storageFinal, frame, retained, worldRead⟩ :=
            ReadOnlyWorldBuiltinCorrespondence.ReturnData.preserves compiled computed related runtime
              memoryMember memorySizeMember exitMember offsetMember sizeMember dataMember dataSizeMember
              (data_related state) (size_related state)
              (RuntimeEffectsCorrespondence.memory_related beforeRuntime)
              (RuntimeEffectsCorrespondence.storage_related beforeRuntime) packed
          have unchanged := copy_world computed
          exact ⟨target, finalStore, evaluated, by
            change RuntimeLinkedWorldCorrespondence.StateRel anchors _ layout.storage.world finalStore
            simpa only [RuntimeReturnDataEffectsSemantics.withRuntime, RuntimeFullEffectsSemantics.withRuntime, unchanged] using linked.read_preserved worldRead
            ⟩
      | guard computed =>
          have named := computed.named
          subst name
          intro typeFuel expected typeCompiled scope arguments lowered compiled world mapping environment initialStore argumentStore targets codes locations captured related packed runtime state installed linked
          obtain ⟨target, resultRelated, evaluated⟩ := MemoryGuardBuiltinCorrespondence.preserves compiled computed related packed
          exact ⟨target, argumentStore, evaluated, linked⟩

end Solcore.Frontend.RustHull.LinkedBuiltinWorldCorrespondence
