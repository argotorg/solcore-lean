import Solcore.Frontend.RustHull.Internal.CallLayout
import Solcore.Frontend.RustHull.Internal.CallBuiltins
import Solcore.Frontend.RustHull.Internal.AccountLayers
import Solcore.Frontend.RustHull.Internal.EffectLayers
import Solcore.Frontend.RustHull.Internal.CallStates
import Solcore.Frontend.RustHull.Internal.LinkedWorld
import Solcore.Frontend.RustHull.Internal.CreationBuiltin

/-!
# Call effect layers

The frame and message proofs of the call, child call and call mode layers.
-/

section
-- leanmerge: from Solcore.Frontend.RustHull.RuntimeCallEffectsCorrespondence
/-! Ordinary and static calls join all existing concrete effects in the
recursive Hull proof. The callback evidence is supplied by actual installation. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.RuntimeCallEffectsCorrespondence
open Correspondence ScalarExecution DerivationCorrespondence

theorem external_preserves (layout : Layout) (baseline : Nat → Option Core.Value)
    (slots : List EffectSlot) (image : Option (List UInt8)) (withCode : Bool) (handlers : Handlers layout)
    (passive : RuntimeLogEffectsCorrespondence.Passive layout.toLogLayout slots) (callPassive : CallPassive layout slots)
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
    (callDepthMember : ⟨"callDepth", .word, layout.callDepth⟩ ∈ slots)
    (callHandlerMember : ⟨"callHandler", Core.OptionalCell.cellType Calls.callbackType, layout.callHandler⟩ ∈ slots) :
    ExternalCallPreservation (supported slots withCode) (model layout baseline slots image handlers) slots
      (RuntimeCallEffectsSemantics.effects image) := by
  intro functions name type sources initial final result enabled notFunction called
  cases called with
  | function selected called => rw [notFunction] at selected; contradiction
  | primitive absent computed => rw [primitive_none enabled] at computed; contradiction
  | external absent notPrimitive computed =>
      cases computed with
      | runtime computed =>
          intro typeFuel expected typeCompiled scope arguments lowered compiled world mapping environment initialStore argumentStore targets codes locations captured related packed runtime state installed
          have call : Semantics.EvalCall functions (RuntimeReturnDataEffectsSemantics.effects image) name type sources
              (sourceRuntime initial) result _ := .external absent notPrimitive computed
          obtain ⟨target, finalStore, resultRelated, evaluated, finalState, installedFinal, retained⟩ :=
            RuntimeReturnDataEffectsCorrespondence.external_preserves layout.toReturnDataLayout
              (patched layout baseline initial.external) slots image withCode passive
              memoryMember worldMember addressMember completeMember staticMember memorySizeMember exitMember offsetMember sizeMember
              logsMember logSizeMember balancesMember codeMembers dataMember dataSizeMember mode
              (runtime_enabled enabled computed) notFunction call typeCompiled compiled related packed runtime
              (runtime_related state) installed
          exact ⟨target, finalStore, resultRelated, evaluated,
            runtime_updated state finalState (RuntimeCallEffectsSemantics.runtime_balances computed), installedFinal, retained⟩
      | call computed =>
          intro typeFuel expected typeCompiled scope arguments lowered compiled world mapping environment initialStore argumentStore targets codes locations captured related packed runtime state installed
          obtain ⟨target, finalStore, resultRelated, evaluated, finalState, retained⟩ :=
            CallBuiltinCorrespondence.ordinary_preserves compiled computed related runtime passive callPassive
              memoryMember memorySizeMember dataMember dataSizeMember callHandlerMember addressMember callDepthMember staticMember
              exitMember offsetMember sizeMember state packed
          exact ⟨target, finalStore, resultRelated, evaluated, finalState, installed.preserved retained, retained⟩
      | staticCall computed =>
          intro typeFuel expected typeCompiled scope arguments lowered compiled world mapping environment initialStore argumentStore targets codes locations captured related packed runtime state installed
          obtain ⟨target, finalStore, resultRelated, evaluated, finalState, retained⟩ :=
            CallBuiltinCorrespondence.static_preserves compiled computed related runtime passive callPassive
              memoryMember memorySizeMember dataMember dataSizeMember callHandlerMember addressMember callDepthMember staticMember
              exitMember offsetMember sizeMember state packed
          exact ⟨target, finalStore, resultRelated, evaluated, finalState, installed.preserved retained, retained⟩

theorem assemble_program (layout : Layout) (baseline : Nat → Option Core.Value)
    (slots : List EffectSlot) (image : Option (List UInt8)) (withCode : Bool) (handlers : Handlers layout)
    (passive : RuntimeLogEffectsCorrespondence.Passive layout.toLogLayout slots) (callPassive : CallPassive layout slots)
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
    (callDepthMember : ⟨"callDepth", .word, layout.callDepth⟩ ∈ slots)
    (callHandlerMember : ⟨"callHandler", Core.OptionalCell.cellType Calls.callbackType, layout.callHandler⟩ ∈ slots)
    {functions : List Function} {function : Function} {entry : String} {runtime : Scope}
    {fuel : Nat} {own : Signature} {allocated : Core.Expr}
    (accepted : assemble functions entry runtime fuel = .ok (own, allocated))
    (selected : functions.find? (·.name == entry) = some function)
    (eligible : ExecutableProgram (supported slots withCode) functions)
    {sources : List Semantics.Value} {targets : List Core.Value}
    (values : ValuesRel own.parameters sources targets)
    {initial final : Semantics.State RuntimeCallEffectsSemantics.State}
    {sourceResult : Semantics.Result Semantics.Value}
    (evaluated : Semantics.EvalFunction functions (RuntimeCallEffectsSemantics.effects image)
      function sources initial sourceResult final)
    {world : World} {runtimeValues caller : Core.Environment} {store : Core.Store}
    (runtimeLength : runtimeValues.length = runtime.length)
    (covered : ScopeCoverage [] runtime)
    (runtimeRelated : EffectEnvironmentRel slots runtime Core.Renaming.id
      (runtimeValues ++ bundleValues targets :: caller))
    (separated : EffectSlotsSeparate slots)
    (state : StateRel (model layout baseline slots image handlers) world initial store) :
    ∃ extension target finalStore,
      ResultRel own.result sourceResult target ∧
      Core.Evaluates (runtimeValues ++ bundleValues targets :: caller) store allocated target finalStore ∧
      StateRel (model layout baseline slots image handlers) (world ++ extension) final finalStore ∧
      ClosuresPreserved store finalStore :=
  assemble_recursive_program_effects accepted selected
    (external_preserves layout baseline slots image withCode handlers passive callPassive memoryMember worldMember addressMember completeMember staticMember
      memorySizeMember exitMember offsetMember sizeMember logsMember logSizeMember balancesMember codeMembers dataMember dataSizeMember mode callDepthMember callHandlerMember) eligible values evaluated
    runtimeLength covered runtimeRelated separated state


end Solcore.Frontend.RustHull.RuntimeCallEffectsCorrespondence
end

section
-- leanmerge: from Solcore.Frontend.RustHull.RuntimeCallEffectsFrameCorrespondence
/-! Source message calls reach actual frame calls and final snapshots.
The same proof covers ordinary frames and frames with linked code slots. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.RuntimeCallEffectsFrameCorrespondence
open Correspondence ScalarExecution DerivationCorrespondence
open RuntimeCallEffectsCorrespondence (Layout Handlers CallPassive model account_related)
open RuntimeAccountEffectsCorrespondence (runtime_related balances_related)
open RuntimeCallEffectsCorrespondence (supported assemble_program)

abbrev slotTypes := RuntimeLogEffectsFrameCorrespondence.slotTypes
abbrev cell_observed := @RuntimeLogEffectsFrameCorrespondence.cell_observed
def snapshotValues (state : RuntimeCallEffectsSemantics.State) :=
  RuntimeAccountEffectsFrameCorrespondence.snapshotValues state.runtime.runtime

/-- A frame installed earlier retains its captured environment. The body and
completion wrapper observe the final source world and balances through the
compiler's actual frame references. -/
theorem compileFrame_call_preserves_observed {program : Program} {code : CodeBlock} {slots : List EffectSlot}
    {fuel : Nat} {compiled : Core.Expr} {withCode : Bool}
    (accepted : AccountRuntime.compileFrame program code (slotTypes slots) fuel = .ok compiled)
    (eligible : ExecutableProgram (supported slots withCode)
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code]))
    {layout : Layout} {image : Option (List UInt8)} {handlers : Handlers layout}
    {initial : RuntimeCallEffectsSemantics.State}
    {before initialStore store : Core.Store} {values environment captured : Core.Environment}
    {function argument : Core.Expr} {closure : Core.Value}
    (closureRelated : CapturedClosure compiled captured closure)
    (resolved : Core.Evaluates environment before function closure initialStore)
    (supplied : Core.Evaluates environment initialStore argument (bundleValues values) store)
    (length : values.length = slots.length)
    (runtime : EffectEnvironmentRel slots (AccountRuntime.frameScope (slotTypes slots)) Core.Renaming.id
      (values.reverse ++ .unit :: bundleValues values :: captured))
    (separated : EffectSlotsSeparate slots)
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
      ⟨"code", Core.WordMapping.type, cells.code⟩ ∈ slots ∧ ⟨"codeKnown", .bool, cells.known⟩ ∈ slots)
    (dataMember : ⟨"returnData", Core.WordMapping.type, layout.returnData⟩ ∈ slots)
    (dataSizeMember : ⟨"returnDataSize", .word, layout.returnDataSize⟩ ∈ slots)
    (mode : layout.codeCells.isSome = withCode)
    (callDepthMember : ⟨"callDepth", .word, layout.callDepth⟩ ∈ slots)
    (callHandlerMember : ⟨"callHandler", Core.OptionalCell.cellType Calls.callbackType, layout.callHandler⟩ ∈ slots)
    (initialRelated : StateRel (model layout (prefixRead layout.boundary store) slots image handlers) [] ⟨[], initial⟩ store)
    (passive : RuntimeLogEffectsCorrespondence.Passive layout.toLogLayout slots)
    (callPassive : CallPassive layout slots)
    {final : Semantics.State RuntimeCallEffectsSemantics.State} {result : Semantics.Result Semantics.Value}
    (evaluated : Semantics.EvalFunction
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code]) (RuntimeCallEffectsSemantics.effects image)
      (AccountRuntime.frameFunction code) [] ⟨[], initial⟩ result final) :
    ∃ extension status accounts finalStore,
      accounts.map Prod.fst = final.external.runtime.runtime.runtime.runtime.runtime.storage.world ∧
      ResultRel .unit result status ∧
      Core.Evaluates environment before (.apply function argument)
        (frameCompletionValue status (snapshotValues final.external accounts)
          (StorageCorrespondence.get accounts final.external.runtime.runtime.runtime.runtime.runtime.storage.address final.external.runtime.runtime.runtime.runtime.runtime.storage.complete)) finalStore ∧
      StateRel (model layout (prefixRead layout.boundary store) slots image handlers)
        extension final finalStore ∧
      finalStore.read? layout.storage.world = some (StorageCorrespondence.world accounts) := by
  obtain ⟨own, body, cells, assembled, references, rfl⟩ := compileFrame_components accepted
  have selected := MemoryFrameCorrespondence.frame_selected accepted
  obtain ⟨signatures, codes, selectedFunction, selectedCode, index, _, sourceSelected,
    signatureCompiled, _, _, _, _, _⟩ := assemble_selection assembled
  have sameFunction := Option.some.inj (sourceSelected.symm.trans selected)
  subst selectedFunction
  obtain ⟨parameters, resultType⟩ := MemoryFrameCorrespondence.frame_signature signatureCompiled
  have argumentValues : ValuesRel own.parameters [] [] := by rw [parameters]; exact .nil
  obtain ⟨extension, status, bodyStore, related, executed, state, _⟩ :=
    assemble_program layout (prefixRead layout.boundary store) slots image withCode handlers passive callPassive
      memoryMember worldMember addressMember completeMember staticMember memorySizeMember exitMember offsetMember sizeMember
      logsMember logSizeMember balancesMember codeMembers dataMember dataSizeMember mode callDepthMember callHandlerMember assembled selected eligible argumentValues evaluated
      (runtimeValues := values.reverse) (caller := bundleValues values :: captured)
      (by simpa [AccountRuntime.frameScope, slotTypes, MemoryFrameCorrespondence.slotTypes] using length)
      (MemoryFrameCorrespondence.frame_coverage _) runtime separated
      initialRelated
  have finalStorage := RuntimeEffectsCorrespondence.storage_related
    (RuntimeEnvironmentEffectsCorrespondence.runtime_related (RuntimeLogEffectsCorrespondence.runtime_related (runtime_related (account_related state))))
  have finalLogs := RuntimeLogEffectsCorrespondence.logs_related (runtime_related (account_related state))
  obtain ⟨accounts, sourceWorld, worldRead⟩ := finalStorage.world
  have finalWorld := cell_observed references runtime worldMember worldRead
  have finalAddress := cell_observed references runtime addressMember finalStorage.address
  have finalComplete := cell_observed references runtime completeMember finalStorage.complete
  have finalSnapshot : ∀ name ∈ frameSnapshotNames,
      FrameCellObserved cells (values.reverse ++ .unit :: bundleValues values :: captured)
        bodyStore name (snapshotValues final.external accounts name) := by
    intro name member
    simp [frameSnapshotNames] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact cell_observed references runtime exitMember finalStorage.exit
    · exact cell_observed references runtime offsetMember finalStorage.returnOffset
    · exact cell_observed references runtime sizeMember finalStorage.returnSize
    · exact cell_observed references runtime memoryMember finalLogs.logs.memory
    · exact cell_observed references runtime logsMember finalLogs.logs.logs
    · exact cell_observed references runtime logSizeMember finalLogs.logs.logSize
    · exact cell_observed references runtime balancesMember (balances_related (account_related state))
    · exact finalWorld
  have completed := frameCompletion_evaluates executed accounts final.external.runtime.runtime.runtime.runtime.runtime.storage.address final.external.runtime.runtime.runtime.runtime.runtime.storage.complete
    finalWorld finalAddress finalComplete finalSnapshot
  obtain ⟨suffix, _, extended⟩ := StorageCorrespondence.getStore_extension accounts
    final.external.runtime.runtime.runtime.runtime.runtime.storage.address final.external.runtime.runtime.runtime.runtime.runtime.storage.complete
    (status :: (values.reverse ++ .unit :: bundleValues values :: captured)) bodyStore
  refine ⟨extension, status, accounts, _, sourceWorld, by simpa only [resultType] using related,
    frameUnpack_call_evaluates (by simpa only [slotTypes, MemoryFrameCorrespondence.slotTypes, List.length_map] using length)
      closureRelated resolved supplied completed, ?_, ?_⟩
  · rw [show bundleValues ([] : List Core.Value) = .unit from rfl, extended]
    simpa only [List.nil_append] using state.appendCore suffix
  · rw [show bundleValues ([] : List Core.Value) = .unit from rfl, extended]
    exact ((StoreRetains.append bodyStore suffix).read layout.storage.world
      (List.getElem?_eq_some_iff.mp worldRead).1).trans worldRead

theorem compileFrame_call_preserves {program : Program} {code : CodeBlock} {slots : List EffectSlot}
    {fuel : Nat} {compiled : Core.Expr} {withCode : Bool}
    (accepted : AccountRuntime.compileFrame program code (slotTypes slots) fuel = .ok compiled)
    (eligible : ExecutableProgram (supported slots withCode)
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code]))
    {layout : Layout} {image : Option (List UInt8)} {handlers : Handlers layout}
    {initial : RuntimeCallEffectsSemantics.State}
    {before initialStore store : Core.Store} {values environment captured : Core.Environment}
    {function argument : Core.Expr} {closure : Core.Value}
    (closureRelated : CapturedClosure compiled captured closure)
    (resolved : Core.Evaluates environment before function closure initialStore)
    (supplied : Core.Evaluates environment initialStore argument (bundleValues values) store)
    (length : values.length = slots.length)
    (runtime : EffectEnvironmentRel slots (AccountRuntime.frameScope (slotTypes slots)) Core.Renaming.id
      (values.reverse ++ .unit :: bundleValues values :: captured))
    (separated : EffectSlotsSeparate slots)
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
      ⟨"code", Core.WordMapping.type, cells.code⟩ ∈ slots ∧ ⟨"codeKnown", .bool, cells.known⟩ ∈ slots)
    (dataMember : ⟨"returnData", Core.WordMapping.type, layout.returnData⟩ ∈ slots)
    (dataSizeMember : ⟨"returnDataSize", .word, layout.returnDataSize⟩ ∈ slots)
    (mode : layout.codeCells.isSome = withCode)
    (callDepthMember : ⟨"callDepth", .word, layout.callDepth⟩ ∈ slots)
    (callHandlerMember : ⟨"callHandler", Core.OptionalCell.cellType Calls.callbackType, layout.callHandler⟩ ∈ slots)
    (initialRelated : StateRel (model layout (prefixRead layout.boundary store) slots image handlers) [] ⟨[], initial⟩ store)
    (passive : RuntimeLogEffectsCorrespondence.Passive layout.toLogLayout slots)
    (callPassive : CallPassive layout slots)
    {final : Semantics.State RuntimeCallEffectsSemantics.State} {result : Semantics.Result Semantics.Value}
    (evaluated : Semantics.EvalFunction
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code]) (RuntimeCallEffectsSemantics.effects image)
      (AccountRuntime.frameFunction code) [] ⟨[], initial⟩ result final) :
    ∃ extension status accounts finalStore,
      accounts.map Prod.fst = final.external.runtime.runtime.runtime.runtime.runtime.storage.world ∧
      ResultRel .unit result status ∧
      Core.Evaluates environment before (.apply function argument)
        (frameCompletionValue status (snapshotValues final.external accounts)
          (StorageCorrespondence.get accounts final.external.runtime.runtime.runtime.runtime.runtime.storage.address final.external.runtime.runtime.runtime.runtime.runtime.storage.complete)) finalStore ∧
      StateRel (model layout (prefixRead layout.boundary store) slots image handlers)
        extension final finalStore := by
  obtain ⟨extension, status, accounts, finalStore, represented, related, executed, state, _⟩ :=
    compileFrame_call_preserves_observed accepted eligible closureRelated resolved supplied length runtime separated
      memoryMember worldMember addressMember completeMember staticMember memorySizeMember exitMember offsetMember sizeMember
      logsMember logSizeMember balancesMember codeMembers dataMember dataSizeMember mode callDepthMember callHandlerMember initialRelated passive callPassive evaluated
  exact ⟨extension, status, accounts, finalStore, represented, related, executed, state⟩

/-- Direct evaluation of freshly compiled frame code is a special case of the
same theorem for captured calls. -/
theorem compileFrame_preserves {program : Program} {code : CodeBlock} {slots : List EffectSlot}
    {fuel : Nat} {compiled : Core.Expr} {withCode : Bool}
    (accepted : AccountRuntime.compileFrame program code (slotTypes slots) fuel = .ok compiled)
    (eligible : ExecutableProgram (supported slots withCode)
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code]))
    {layout : Layout} {image : Option (List UInt8)} {handlers : Handlers layout}
    {initial : RuntimeCallEffectsSemantics.State}
    {initialStore store : Core.Store} {values environment : Core.Environment} {argument : Core.Expr}
    (supplied : Core.Evaluates environment initialStore argument (bundleValues values) store)
    (length : values.length = slots.length)
    (runtime : EffectEnvironmentRel slots (AccountRuntime.frameScope (slotTypes slots)) Core.Renaming.id
      (values.reverse ++ .unit :: bundleValues values :: environment))
    (separated : EffectSlotsSeparate slots)
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
      ⟨"code", Core.WordMapping.type, cells.code⟩ ∈ slots ∧ ⟨"codeKnown", .bool, cells.known⟩ ∈ slots)
    (dataMember : ⟨"returnData", Core.WordMapping.type, layout.returnData⟩ ∈ slots)
    (dataSizeMember : ⟨"returnDataSize", .word, layout.returnDataSize⟩ ∈ slots)
    (mode : layout.codeCells.isSome = withCode)
    (callDepthMember : ⟨"callDepth", .word, layout.callDepth⟩ ∈ slots)
    (callHandlerMember : ⟨"callHandler", Core.OptionalCell.cellType Calls.callbackType, layout.callHandler⟩ ∈ slots)
    (initialRelated : StateRel (model layout (prefixRead layout.boundary store) slots image handlers) [] ⟨[], initial⟩ store)
    (passive : RuntimeLogEffectsCorrespondence.Passive layout.toLogLayout slots)
    (callPassive : CallPassive layout slots)
    {final : Semantics.State RuntimeCallEffectsSemantics.State} {result : Semantics.Result Semantics.Value}
    (evaluated : Semantics.EvalFunction
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code]) (RuntimeCallEffectsSemantics.effects image)
      (AccountRuntime.frameFunction code) [] ⟨[], initial⟩ result final) :
    ∃ extension status accounts finalStore,
      accounts.map Prod.fst = final.external.runtime.runtime.runtime.runtime.runtime.storage.world ∧
      ResultRel .unit result status ∧
      Core.Evaluates environment initialStore (.apply compiled argument)
        (frameCompletionValue status (snapshotValues final.external accounts)
          (StorageCorrespondence.get accounts final.external.runtime.runtime.runtime.runtime.runtime.storage.address final.external.runtime.runtime.runtime.runtime.runtime.storage.complete)) finalStore ∧
      StateRel (model layout (prefixRead layout.boundary store) slots image handlers)
        extension final finalStore := by
  obtain ⟨own, body, cells, _, _, rfl⟩ := compileFrame_components accepted
  exact compileFrame_call_preserves accepted eligible (CapturedClosure.lambda _ _ _ environment)
    Core.Evaluates.lambda supplied length runtime separated memoryMember worldMember addressMember completeMember
    staticMember memorySizeMember exitMember offsetMember sizeMember logsMember logSizeMember balancesMember codeMembers dataMember dataSizeMember mode
    callDepthMember callHandlerMember initialRelated passive callPassive evaluated

end Solcore.Frontend.RustHull.RuntimeCallEffectsFrameCorrespondence
end

section
-- leanmerge: from Solcore.Frontend.RustHull.ContractCallCorrespondence
/-! Message calls and their shared state reach actual message
completion with or without linked code cells. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.ContractCallCorrespondence
open Correspondence ScalarExecution CodeBuilder

def supported (withCode : Bool) (name : String) : Prop :=
  ContractReturnDataCorrespondence.supported withCode name ∨ name = "call" ∨ name = "staticcall"

theorem supported_actual {slots : List EffectSlot} {withCode : Bool}
    (signature : RuntimeEffectsFrameCorrespondence.slotTypes slots = RuntimeExtendedInitializedEffects.slots withCode) :
    RuntimeCallEffectsCorrespondence.supported slots withCode = supported withCode := by
  funext name
  apply propext
  simp only [RuntimeCallEffectsCorrespondence.supported, supported,
    ContractReturnDataCorrespondence.supported_actual signature]

def messageValue (result : Semantics.Result Semantics.Value) (state : RuntimeCallEffectsSemantics.State)
    (accounts : StorageCorrespondence.Accounts) (target : Core.Word) : Core.Value :=
  ContractAccountCorrespondence.messageValue result state.runtime.runtime accounts target

def MessageRel (result : Semantics.Result Semantics.Value) (state : RuntimeCallEffectsSemantics.State)
    (target : Core.Word) (value : Core.Value) : Prop :=
  ContractAccountCorrespondence.MessageRel result state.runtime.runtime target value

theorem frameCall_message_evaluates {program : Program} {code : CodeBlock} {slots : List EffectSlot}
    {fuel : Nat} {compiled : Core.Expr} {withCode : Bool}
    (accepted : AccountRuntime.compileFrame program code (RuntimeLogEffectsFrameCorrespondence.slotTypes slots) fuel = .ok compiled)
    (eligible : DerivationCorrespondence.ExecutableProgram (RuntimeCallEffectsCorrespondence.supported slots withCode)
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code]))
    {layout : RuntimeCallEffectsCorrespondence.Layout} {image : Option (List UInt8)}
    {handlers : RuntimeCallEffectsCorrespondence.Handlers layout}
    {initial : RuntimeCallEffectsSemantics.State}
    {before initialStore store : Core.Store} {values environment captured : Core.Environment}
    {function argument target deploying : Code} {depth : Nat}
    {shared : AccountRuntime.References} {images : List (Nat × List UInt8)} {closure : Core.Value}
    (closureRelated : CapturedClosure compiled captured closure)
    (resolved : Core.Evaluates environment before (function depth) closure initialStore)
    (supplied : Core.Evaluates environment initialStore (argument depth) (bundleValues values) store)
    (length : values.length = slots.length)
    (runtime : EffectEnvironmentRel slots (AccountRuntime.frameScope (RuntimeLogEffectsFrameCorrespondence.slotTypes slots)) Core.Renaming.id
      (values.reverse ++ .unit :: bundleValues values :: captured))
    (separated : EffectSlotsSeparate slots)
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
      ⟨"code", Core.WordMapping.type, cells.code⟩ ∈ slots ∧ ⟨"codeKnown", .bool, cells.known⟩ ∈ slots)
    (dataMember : ⟨"returnData", Core.WordMapping.type, layout.returnData⟩ ∈ slots)
    (dataSizeMember : ⟨"returnDataSize", .word, layout.returnDataSize⟩ ∈ slots)
    (mode : layout.codeCells.isSome = withCode)
    (callDepthMember : ⟨"callDepth", .word, layout.callDepth⟩ ∈ slots)
    (callHandlerMember : ⟨"callHandler", Core.OptionalCell.cellType Calls.callbackType, layout.callHandler⟩ ∈ slots)
    (initialRelated : StateRel (RuntimeCallEffectsCorrespondence.model layout (prefixRead layout.boundary store) slots image handlers) [] ⟨[], initial⟩ store)
    (passive : RuntimeLogEffectsCorrespondence.Passive layout.toLogLayout slots)
    (callPassive : RuntimeCallEffectsCorrespondence.CallPassive layout slots)
    {final : Semantics.State RuntimeCallEffectsSemantics.State} {result : Semantics.Result Semantics.Value}
    (evaluated : Semantics.EvalFunction
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code]) (RuntimeCallEffectsSemantics.effects image)
      (AccountRuntime.frameFunction code) [] ⟨[], initial⟩ result final)
    (address : Core.Word)
    (worldReference : CodeValue depth environment (AccountRuntime.reference shared "world")
      (.cellRef AccountState.type layout.storage.world))
    (balancesReference : CodeValue depth environment (AccountRuntime.reference shared "balances")
      (.cellRef Core.WordMapping.type layout.balances))
    (targetValue : CodeValue depth environment target (.word address))
    (deployingValue : CodeValue depth environment deploying (.bool false)) :
    ∃ value finalStore, Core.Evaluates environment before
      (bind (apply function argument) (fun framed => AccountRuntime.completeMessage shared images target deploying framed) depth)
      value finalStore ∧ MessageRel result final.external address value := by
  obtain ⟨extension, status, accounts, bodyStore, represented, statusRelated, executed, related, worldFinal⟩ :=
    RuntimeCallEffectsFrameCorrespondence.compileFrame_call_preserves_observed accepted eligible closureRelated resolved supplied length
      runtime separated memoryMember worldMember addressMember completeMember staticMember memorySizeMember exitMember offsetMember sizeMember
      logsMember logSizeMember balancesMember codeMembers dataMember dataSizeMember mode callDepthMember callHandlerMember initialRelated passive callPassive evaluated
  have balancesFinal := RuntimeAccountEffectsCorrespondence.balances_related (RuntimeCallEffectsCorrespondence.account_related related)
  let frameResult := frameCompletionValue status (ContractLogCorrespondence.snapshotValues final.external.runtime.runtime.runtime accounts final.external.runtime.runtime.balances)
    (StorageCorrespondence.get accounts final.external.runtime.runtime.runtime.runtime.runtime.storage.address final.external.runtime.runtime.runtime.runtime.runtime.storage.complete)
  obtain ⟨finalStore, completed⟩ := ContractLogCorrespondence.message_evaluates result final.external.runtime.runtime.runtime accounts address final.external.runtime.runtime.balances
    statusRelated (worldReference.prepend [frameResult]) (balancesReference.prepend [frameResult])
    (targetValue.prepend [frameResult]) (deployingValue.prepend [frameResult])
    (CodeValue.bound depth environment frameResult) worldFinal balancesFinal
  exact ⟨_, finalStore, .letE executed completed, accounts, represented, rfl⟩

end Solcore.Frontend.RustHull.ContractCallCorrespondence
end

section
-- leanmerge: from Solcore.Frontend.RustHull.RuntimeCallModeEffectsCorrespondence
/-! Message calls, account destruction, creation attempts, Hull's explicit
revert and inline Yul blocks join the existing concrete effects in the
recursive Hull proof. Actual installation supplies captured handlers. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.RuntimeCallModeEffectsCorrespondence
open Correspondence ScalarExecution DerivationCorrespondence
open RuntimeChildCallEffectsCorrespondence (Anchors Context of_base linked_related)
open RuntimeCallEffectsCorrespondence (Layout CallPassive sourceRuntime patched runtime_related runtime_updated)

theorem external_preserves (layout : Layout) (baseline : Nat → Option Core.Value)
    (slots : List EffectSlot) (image : Option (List UInt8)) (withCode : Bool) (handlers : ModeHandlers layout)
    (passive : RuntimeLogEffectsCorrespondence.Passive layout.toLogLayout slots) (callPassive : CallPassive layout slots)
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
    (callDepthMember : ⟨"callDepth", .word, layout.callDepth⟩ ∈ slots)
    (callHandlerMember : ⟨"callHandler", Core.OptionalCell.cellType Calls.callbackType, layout.callHandler⟩ ∈ slots)
    (callCodeMember : ⟨"callCodeHandler", Core.OptionalCell.cellType Calls.callbackType, handlers.callCode.location⟩ ∈ slots)
    (delegateMember : ⟨"delegateCallHandler", Core.OptionalCell.cellType Calls.callbackType, handlers.delegateCall.location⟩ ∈ slots)
    (callerMember : ∃ location, (⟨"caller", .word, location⟩ : EffectSlot) ∈ slots)
    (valueMember : ∃ location, (⟨"callvalue", .word, location⟩ : EffectSlot) ∈ slots)
    (createSlots : CreateSlots handlers slots)
    (anchors : Anchors) (context : Context layout)
    (children : RuntimeCallEffectsSemantics.State → AccountCallSemantics.Children)
    (callbacks : ∀ {world state store},
      StateRel (model layout baseline slots image handlers anchors context) world state store →
      ∀ operation, CallbackPreservation layout handlers anchors context children operation state.external) :
    ExternalCallPreservation (supported slots withCode) (model layout baseline slots image handlers anchors context) slots
      (RuntimeCallModeSemantics.effectsWith children image) := by
  intro functions name type sources initial final result enabled notFunction called
  cases called with
  | function selected called => rw [notFunction] at selected; contradiction
  | primitive absent computed => rw [primitive_none enabled] at computed; contradiction
  | external absent notPrimitive computed =>
      cases computed with
      | runtime computed =>
          intro typeFuel expected typeCompiled scope arguments lowered compiled world mapping environment initialStore argumentStore targets codes locations captured related packed runtime state installed
          have call : Semantics.EvalCall functions (RuntimeReturnDataEffectsSemantics.effects image) name type sources
              (sourceRuntime initial) result _ := .external absent notPrimitive computed
          obtain ⟨target, finalStore, resultRelated, evaluated, finalState, installedFinal, retained⟩ :=
            RuntimeLinkedReturnDataEffectsCorrespondence.external_preserves layout.toReturnDataLayout
              (patched layout baseline initial.external) slots image withCode passive
              memoryMember worldMember addressMember completeMember staticMember memorySizeMember exitMember offsetMember sizeMember
              logsMember logSizeMember balancesMember codeMembers dataMember dataSizeMember mode anchors
              (runtime_enabled enabled computed) notFunction call typeCompiled compiled related packed runtime
              (RuntimeLinkedReturnDataEffectsCorrespondence.of_base (runtime_related (base_related state)) (linked_related state)) installed
          have baseFinal := runtime_updated (base_related state)
            (RuntimeLinkedReturnDataEffectsCorrespondence.base_related finalState)
            (RuntimeCallEffectsSemantics.runtime_balances computed)
          exact ⟨target, finalStore, resultRelated, evaluated,
            of_base baseFinal (RuntimeLinkedReturnDataEffectsCorrespondence.linked_related finalState)
              ((handlers.context context).updated (base_related state) baseFinal state.external.2.2.1.2), installedFinal, retained⟩
      | call computed =>
          intro typeFuel expected typeCompiled scope arguments lowered compiled world mapping environment initialStore argumentStore targets codes locations captured related packed runtime state installed
          obtain ⟨target, finalStore, resultRelated, evaluated, finalState, retained⟩ :=
            ChildCallBuiltinCorrespondence.ordinary_preserves compiled (RuntimeCallModeSemantics.ordinary_call computed) related runtime passive callPassive
              memoryMember memorySizeMember dataMember dataSizeMember callHandlerMember addressMember callDepthMember staticMember
              exitMember offsetMember sizeMember state (callbacks state .ordinary) packed
          exact ⟨target, finalStore, resultRelated, evaluated, finalState, installed.preserved retained, retained⟩
      | staticCall computed =>
          intro typeFuel expected typeCompiled scope arguments lowered compiled world mapping environment initialStore argumentStore targets codes locations captured related packed runtime state installed
          obtain ⟨target, finalStore, resultRelated, evaluated, finalState, retained⟩ :=
            ChildCallBuiltinCorrespondence.static_preserves compiled (RuntimeCallModeSemantics.static_call computed) related runtime passive callPassive
              memoryMember memorySizeMember dataMember dataSizeMember callHandlerMember addressMember callDepthMember staticMember
              exitMember offsetMember sizeMember state (callbacks state .staticCall) packed
          exact ⟨target, finalStore, resultRelated, evaluated, finalState, installed.preserved retained, retained⟩
      | callCode computed =>
          intro typeFuel expected typeCompiled scope arguments lowered compiled world mapping environment initialStore argumentStore targets codes locations captured related packed runtime state installed
          obtain ⟨target, finalStore, resultRelated, evaluated, finalState, retained⟩ :=
            CallModeBuiltinCorrespondence.callCode_preserves compiled computed related runtime callPassive
              memoryMember memorySizeMember dataMember dataSizeMember callCodeMember addressMember callDepthMember staticMember
              state (callbacks state .callCode) packed
          exact ⟨target, finalStore, resultRelated, evaluated, finalState, installed.preserved retained, retained⟩
      | delegateCall computed =>
          intro typeFuel expected typeCompiled scope arguments lowered compiled world mapping environment initialStore argumentStore targets codes locations captured related packed runtime state installed
          obtain ⟨callerLocation, callerMember⟩ := callerMember
          obtain ⟨valueLocation, valueMember⟩ := valueMember
          obtain ⟨target, finalStore, resultRelated, evaluated, finalState, retained⟩ :=
            CallModeBuiltinCorrespondence.delegate_preserves compiled computed related runtime callPassive
              memoryMember memorySizeMember dataMember dataSizeMember delegateMember callerMember valueMember callDepthMember staticMember
              state (callbacks state .delegateCall) packed
          exact ⟨target, finalStore, resultRelated, evaluated, finalState, installed.preserved retained, retained⟩
      | destroy computed =>
          intro typeFuel expected typeCompiled scope arguments lowered compiled world mapping environment initialStore argumentStore targets codes locations captured related packed runtime state installed
          obtain ⟨target, finalStore, resultRelated, evaluated, finalState, retained⟩ :=
            LifecycleBuiltinCorrespondence.preserves compiled computed related runtime passive callPassive
              worldMember balancesMember addressMember completeMember staticMember memorySizeMember exitMember offsetMember sizeMember
              state packed
          exact ⟨target, finalStore, resultRelated, evaluated, finalState, installed.preserved retained, retained⟩
      | create computed =>
          intro typeFuel expected typeCompiled scope arguments lowered compiled world mapping environment initialStore argumentStore targets codes locations captured related packed runtime state installed
          obtain ⟨gasLocation, gasMember⟩ := createSlots.gas
          obtain ⟨target, finalStore, resultRelated, evaluated, finalState, retained⟩ :=
            CreationBuiltinCorrespondence.create_preserves compiled computed related runtime passive callPassive
              memoryMember memorySizeMember dataMember dataSizeMember addressMember callDepthMember staticMember
              exitMember offsetMember sizeMember gasMember state
              ⟨handlers.create.location, handlers.create.value, create_read state,
                handlers.create.local_outside, handlers.create.closure⟩ createSlots.handler packed
          exact ⟨target, finalStore, resultRelated, evaluated, finalState, installed.preserved retained, retained⟩
      | create2 computed =>
          intro typeFuel expected typeCompiled scope arguments lowered compiled world mapping environment initialStore argumentStore targets codes locations captured related packed runtime state installed
          obtain ⟨gasLocation, gasMember⟩ := createSlots.gas
          obtain ⟨target, finalStore, resultRelated, evaluated, finalState, retained⟩ :=
            CreationBuiltinCorrespondence.create2_preserves compiled computed related runtime passive callPassive
              memoryMember memorySizeMember dataMember dataSizeMember addressMember callDepthMember staticMember
              exitMember offsetMember sizeMember gasMember state
              ⟨handlers.create.location, handlers.create.value, create_read state,
                handlers.create.local_outside, handlers.create.closure⟩ createSlots.handler packed
          exact ⟨target, finalStore, resultRelated, evaluated, finalState, installed.preserved retained, retained⟩
      | createAdmitted computed =>
          intro typeFuel expected typeCompiled scope arguments lowered compiled world mapping environment initialStore argumentStore targets codes locations captured related packed runtime state installed
          obtain ⟨gasLocation, gasMember⟩ := createSlots.gas
          obtain ⟨target, finalStore, resultRelated, evaluated, finalState, retained⟩ :=
            CreationBuiltinCorrespondence.createAdmitted_preserves compiled computed related runtime passive callPassive
              memoryMember memorySizeMember dataMember dataSizeMember addressMember callDepthMember staticMember
              exitMember offsetMember sizeMember gasMember state
              ⟨handlers.create.location, handlers.create.value, create_read state,
                handlers.create.local_outside, handlers.create.closure⟩ createSlots.handler packed
          exact ⟨target, finalStore, resultRelated, evaluated, finalState, installed.preserved retained, retained⟩
      | create2Admitted computed =>
          intro typeFuel expected typeCompiled scope arguments lowered compiled world mapping environment initialStore argumentStore targets codes locations captured related packed runtime state installed
          obtain ⟨gasLocation, gasMember⟩ := createSlots.gas
          obtain ⟨target, finalStore, resultRelated, evaluated, finalState, retained⟩ :=
            CreationBuiltinCorrespondence.create2Admitted_preserves compiled computed related runtime passive callPassive
              memoryMember memorySizeMember dataMember dataSizeMember addressMember callDepthMember staticMember
              exitMember offsetMember sizeMember gasMember state
              ⟨handlers.create.location, handlers.create.value, create_read state,
                handlers.create.local_outside, handlers.create.closure⟩ createSlots.handler packed
          exact ⟨target, finalStore, resultRelated, evaluated, finalState, installed.preserved retained, retained⟩

theorem revert_preserves (layout : Layout) (baseline : Nat → Option Core.Value)
    (slots : List EffectSlot) (image : Option (List UInt8)) (withCode : Bool) (handlers : ModeHandlers layout)
    (passive : RuntimeLogEffectsCorrespondence.Passive layout.toLogLayout slots)
    (memoryMember : ⟨"memory", Core.WordMapping.type, layout.memory⟩ ∈ slots)
    (memorySizeMember : ⟨"memorySize", .word, layout.storage.memorySize⟩ ∈ slots)
    (exitMember : ⟨"exit", .word, layout.storage.exit⟩ ∈ slots)
    (offsetMember : ⟨"returnOffset", .word, layout.storage.returnOffset⟩ ∈ slots)
    (sizeMember : ⟨"returnSize", .word, layout.storage.returnSize⟩ ∈ slots)
    (anchors : Anchors) (context : Context layout)
    (children : RuntimeCallEffectsSemantics.State → AccountCallSemantics.Children) :
    RevertPreservation (supported slots withCode) (model layout baseline slots image handlers anchors context) slots
      (RuntimeCallModeSemantics.effectsWith children image) := by
  intro message initial control final _ reverted scope exit compiled world mapping environment store runtime state
  exact RevertBuiltinCorrespondence.preserves passive memoryMember memorySizeMember exitMember offsetMember sizeMember
    reverted compiled runtime state

theorem assembly_preserves (layout : Layout) (baseline : Nat → Option Core.Value)
    (slots : List EffectSlot) (image : Option (List UInt8)) (withCode : Bool) (handlers : ModeHandlers layout)
    (passive : RuntimeLogEffectsCorrespondence.Passive layout.toLogLayout slots)
    (memoryMember : ⟨"memory", Core.WordMapping.type, layout.memory⟩ ∈ slots)
    (memorySizeMember : ⟨"memorySize", .word, layout.storage.memorySize⟩ ∈ slots)
    (exitMember : ⟨"exit", .word, layout.storage.exit⟩ ∈ slots)
    (offsetMember : ⟨"returnOffset", .word, layout.storage.returnOffset⟩ ∈ slots)
    (sizeMember : ⟨"returnSize", .word, layout.storage.returnSize⟩ ∈ slots)
    (anchors : Anchors) (context : Context layout)
    (children : RuntimeCallEffectsSemantics.State → AccountCallSemantics.Children) :
    AssemblyPreservation (supported slots withCode) (model layout baseline slots image handlers anchors context) slots
      (RuntimeCallModeSemantics.effectsWith children image) :=
  YulBlockCorrespondence.assembly_preserves (fun executed => executed)
    (YulBuiltinCorrespondence.step passive memoryMember memorySizeMember exitMember offsetMember sizeMember)

theorem assemble_program (layout : Layout) (baseline : Nat → Option Core.Value)
    (slots : List EffectSlot) (image : Option (List UInt8)) (withCode : Bool) (handlers : ModeHandlers layout)
    (passive : RuntimeLogEffectsCorrespondence.Passive layout.toLogLayout slots) (callPassive : CallPassive layout slots)
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
    (callDepthMember : ⟨"callDepth", .word, layout.callDepth⟩ ∈ slots)
    (callHandlerMember : ⟨"callHandler", Core.OptionalCell.cellType Calls.callbackType, layout.callHandler⟩ ∈ slots)
    (callCodeMember : ⟨"callCodeHandler", Core.OptionalCell.cellType Calls.callbackType, handlers.callCode.location⟩ ∈ slots)
    (delegateMember : ⟨"delegateCallHandler", Core.OptionalCell.cellType Calls.callbackType, handlers.delegateCall.location⟩ ∈ slots)
    (callerMember : ∃ location, (⟨"caller", .word, location⟩ : EffectSlot) ∈ slots)
    (valueMember : ∃ location, (⟨"callvalue", .word, location⟩ : EffectSlot) ∈ slots)
    (createSlots : CreateSlots handlers slots)
    (anchors : Anchors) (context : Context layout)
    (children : RuntimeCallEffectsSemantics.State → AccountCallSemantics.Children)
    (callbacks : ∀ {world state store},
      StateRel (model layout baseline slots image handlers anchors context) world state store →
      ∀ operation, CallbackPreservation layout handlers anchors context children operation state.external)
    {functions : List Function} {function : Function} {entry : String} {runtime : Scope}
    {fuel : Nat} {own : Signature} {allocated : Core.Expr}
    (accepted : assemble functions entry runtime fuel = .ok (own, allocated))
    (selected : functions.find? (·.name == entry) = some function)
    (eligible : ExecutableProgram (supported slots withCode) functions)
    {sources : List Semantics.Value} {targets : List Core.Value}
    (values : ValuesRel own.parameters sources targets)
    {initial final : Semantics.State RuntimeCallEffectsSemantics.State}
    {sourceResult : Semantics.Result Semantics.Value}
    (evaluated : Semantics.EvalFunction functions (RuntimeCallModeSemantics.effectsWith children image)
      function sources initial sourceResult final)
    {world : World} {runtimeValues caller : Core.Environment} {store : Core.Store}
    (runtimeLength : runtimeValues.length = runtime.length)
    (covered : ScopeCoverage [] runtime)
    (runtimeRelated : EffectEnvironmentRel slots runtime Core.Renaming.id
      (runtimeValues ++ bundleValues targets :: caller))
    (separated : EffectSlotsSeparate slots)
    (state : StateRel (model layout baseline slots image handlers anchors context) world initial store) :
    ∃ extension target finalStore,
      ResultRel own.result sourceResult target ∧
      Core.Evaluates (runtimeValues ++ bundleValues targets :: caller) store allocated target finalStore ∧
      StateRel (model layout baseline slots image handlers anchors context) (world ++ extension) final finalStore ∧
      ClosuresPreserved store finalStore :=
  assemble_recursive_program_effects accepted selected
    (external_preserves layout baseline slots image withCode handlers passive callPassive memoryMember worldMember addressMember completeMember staticMember
      memorySizeMember exitMember offsetMember sizeMember logsMember logSizeMember balancesMember codeMembers dataMember dataSizeMember mode callDepthMember callHandlerMember callCodeMember delegateMember callerMember valueMember createSlots anchors context children callbacks) eligible values evaluated
    runtimeLength covered runtimeRelated separated state
    (revert_preserves layout baseline slots image withCode handlers passive memoryMember memorySizeMember exitMember
      offsetMember sizeMember anchors context children)
    (assembly_preserves layout baseline slots image withCode handlers passive memoryMember memorySizeMember exitMember
      offsetMember sizeMember anchors context children)


end Solcore.Frontend.RustHull.RuntimeCallModeEffectsCorrespondence
end

section
-- leanmerge: from Solcore.Frontend.RustHull.RuntimeCallModeEffectsFrameCorrespondence
/-! Source message calls reach actual frame calls and final snapshots.
The same proof covers ordinary frames and frames with linked code slots. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.RuntimeCallModeEffectsFrameCorrespondence
open Correspondence ScalarExecution DerivationCorrespondence
open RuntimeCallEffectsCorrespondence (Layout CallPassive account_related)
open RuntimeChildCallEffectsCorrespondence (Context Anchors)
open RuntimeCallModeEffectsCorrespondence (model base_related ModeHandlers CallbackPreservation assemble_program)
open RuntimeAccountEffectsCorrespondence (runtime_related balances_related)
open RuntimeCallModeEffectsCorrespondence (supported)

abbrev slotTypes := RuntimeLogEffectsFrameCorrespondence.slotTypes
abbrev cell_observed := @RuntimeLogEffectsFrameCorrespondence.cell_observed
def snapshotValues (state : RuntimeCallEffectsSemantics.State) :=
  RuntimeAccountEffectsFrameCorrespondence.snapshotValues state.runtime.runtime

/-- A frame installed earlier retains its captured environment. The body and
completion wrapper observe the final source world and balances through the
compiler's actual frame references. -/
theorem compileFrame_call_preserves_observed {program : Program} {code : CodeBlock} {slots : List EffectSlot}
    {fuel : Nat} {compiled : Core.Expr} {withCode : Bool}
    (accepted : AccountRuntime.compileFrame program code (slotTypes slots) fuel = .ok compiled)
    (eligible : ExecutableProgram (supported slots withCode)
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code]))
    {layout : Layout} {image : Option (List UInt8)} {handlers : ModeHandlers layout}
    {anchors : Anchors} {context : Context layout}
    {children : RuntimeCallEffectsSemantics.State → AccountCallSemantics.Children}
    {initial : RuntimeCallEffectsSemantics.State}
    {before initialStore store : Core.Store} {values environment captured : Core.Environment}
    {function argument : Core.Expr} {closure : Core.Value}
    (closureRelated : CapturedClosure compiled captured closure)
    (resolved : Core.Evaluates environment before function closure initialStore)
    (supplied : Core.Evaluates environment initialStore argument (bundleValues values) store)
    (length : values.length = slots.length)
    (runtime : EffectEnvironmentRel slots (AccountRuntime.frameScope (slotTypes slots)) Core.Renaming.id
      (values.reverse ++ .unit :: bundleValues values :: captured))
    (separated : EffectSlotsSeparate slots)
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
      ⟨"code", Core.WordMapping.type, cells.code⟩ ∈ slots ∧ ⟨"codeKnown", .bool, cells.known⟩ ∈ slots)
    (dataMember : ⟨"returnData", Core.WordMapping.type, layout.returnData⟩ ∈ slots)
    (dataSizeMember : ⟨"returnDataSize", .word, layout.returnDataSize⟩ ∈ slots)
    (mode : layout.codeCells.isSome = withCode)
    (callDepthMember : ⟨"callDepth", .word, layout.callDepth⟩ ∈ slots)
    (callHandlerMember : ⟨"callHandler", Core.OptionalCell.cellType Calls.callbackType, layout.callHandler⟩ ∈ slots)
    (callCodeMember : ⟨"callCodeHandler", Core.OptionalCell.cellType Calls.callbackType, handlers.callCode.location⟩ ∈ slots)
    (delegateMember : ⟨"delegateCallHandler", Core.OptionalCell.cellType Calls.callbackType, handlers.delegateCall.location⟩ ∈ slots)
    (callerMember : ∃ location, (⟨"caller", .word, location⟩ : EffectSlot) ∈ slots)
    (valueMember : ∃ location, (⟨"callvalue", .word, location⟩ : EffectSlot) ∈ slots)
    (createSlots : RuntimeCallModeEffectsCorrespondence.CreateSlots handlers slots)
    (initialRelated : StateRel (model layout (prefixRead layout.boundary store) slots image handlers anchors context) [] ⟨[], initial⟩ store)
    (passive : RuntimeLogEffectsCorrespondence.Passive layout.toLogLayout slots)
    (callPassive : CallPassive layout slots)
    (callbacks : ∀ {world state current},
      StateRel (model layout (prefixRead layout.boundary store) slots image handlers anchors context) world state current →
      ∀ operation, CallbackPreservation layout handlers anchors context children operation state.external)
    {final : Semantics.State RuntimeCallEffectsSemantics.State} {result : Semantics.Result Semantics.Value}
    (evaluated : Semantics.EvalFunction
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code]) (RuntimeCallModeSemantics.effectsWith children image)
      (AccountRuntime.frameFunction code) [] ⟨[], initial⟩ result final) :
    ∃ extension status accounts finalStore,
      accounts.map Prod.fst = final.external.runtime.runtime.runtime.runtime.runtime.storage.world ∧
      ResultRel .unit result status ∧
      Core.Evaluates environment before (.apply function argument)
        (frameCompletionValue status (snapshotValues final.external accounts)
          (StorageCorrespondence.get accounts final.external.runtime.runtime.runtime.runtime.runtime.storage.address final.external.runtime.runtime.runtime.runtime.runtime.storage.complete)) finalStore ∧
      StateRel (model layout (prefixRead layout.boundary store) slots image handlers anchors context)
        extension final finalStore ∧
      finalStore.read? layout.storage.world = some (StorageCorrespondence.world accounts) := by
  obtain ⟨own, body, cells, assembled, references, rfl⟩ := compileFrame_components accepted
  have selected := MemoryFrameCorrespondence.frame_selected accepted
  obtain ⟨signatures, codes, selectedFunction, selectedCode, index, _, sourceSelected,
    signatureCompiled, _, _, _, _, _⟩ := assemble_selection assembled
  have sameFunction := Option.some.inj (sourceSelected.symm.trans selected)
  subst selectedFunction
  obtain ⟨parameters, resultType⟩ := MemoryFrameCorrespondence.frame_signature signatureCompiled
  have argumentValues : ValuesRel own.parameters [] [] := by rw [parameters]; exact .nil
  obtain ⟨extension, status, bodyStore, related, executed, state, _⟩ :=
    assemble_program layout (prefixRead layout.boundary store) slots image withCode handlers passive callPassive
      memoryMember worldMember addressMember completeMember staticMember memorySizeMember exitMember offsetMember sizeMember
      logsMember logSizeMember balancesMember codeMembers dataMember dataSizeMember mode callDepthMember callHandlerMember callCodeMember delegateMember callerMember valueMember createSlots anchors context children callbacks assembled selected eligible argumentValues evaluated
      (runtimeValues := values.reverse) (caller := bundleValues values :: captured)
      (by simpa [AccountRuntime.frameScope, slotTypes, MemoryFrameCorrespondence.slotTypes] using length)
      (MemoryFrameCorrespondence.frame_coverage _) runtime separated
      initialRelated
  have finalStorage := RuntimeEffectsCorrespondence.storage_related
    (RuntimeEnvironmentEffectsCorrespondence.runtime_related (RuntimeLogEffectsCorrespondence.runtime_related (runtime_related (account_related (base_related state)))))
  have finalLogs := RuntimeLogEffectsCorrespondence.logs_related (runtime_related (account_related (base_related state)))
  obtain ⟨accounts, sourceWorld, worldRead⟩ := finalStorage.world
  have finalWorld := cell_observed references runtime worldMember worldRead
  have finalAddress := cell_observed references runtime addressMember finalStorage.address
  have finalComplete := cell_observed references runtime completeMember finalStorage.complete
  have finalSnapshot : ∀ name ∈ frameSnapshotNames,
      FrameCellObserved cells (values.reverse ++ .unit :: bundleValues values :: captured)
        bodyStore name (snapshotValues final.external accounts name) := by
    intro name member
    simp [frameSnapshotNames] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact cell_observed references runtime exitMember finalStorage.exit
    · exact cell_observed references runtime offsetMember finalStorage.returnOffset
    · exact cell_observed references runtime sizeMember finalStorage.returnSize
    · exact cell_observed references runtime memoryMember finalLogs.logs.memory
    · exact cell_observed references runtime logsMember finalLogs.logs.logs
    · exact cell_observed references runtime logSizeMember finalLogs.logs.logSize
    · exact cell_observed references runtime balancesMember (balances_related (account_related (base_related state)))
    · exact finalWorld
  have completed := frameCompletion_evaluates executed accounts final.external.runtime.runtime.runtime.runtime.runtime.storage.address final.external.runtime.runtime.runtime.runtime.runtime.storage.complete
    finalWorld finalAddress finalComplete finalSnapshot
  obtain ⟨suffix, _, extended⟩ := StorageCorrespondence.getStore_extension accounts
    final.external.runtime.runtime.runtime.runtime.runtime.storage.address final.external.runtime.runtime.runtime.runtime.runtime.storage.complete
    (status :: (values.reverse ++ .unit :: bundleValues values :: captured)) bodyStore
  refine ⟨extension, status, accounts, _, sourceWorld, by simpa only [resultType] using related,
    frameUnpack_call_evaluates (by simpa only [slotTypes, MemoryFrameCorrespondence.slotTypes, List.length_map] using length)
      closureRelated resolved supplied completed, ?_, ?_⟩
  · rw [show bundleValues ([] : List Core.Value) = .unit from rfl, extended]
    simpa only [List.nil_append] using state.appendCore suffix
  · rw [show bundleValues ([] : List Core.Value) = .unit from rfl, extended]
    exact ((StoreRetains.append bodyStore suffix).read layout.storage.world
      (List.getElem?_eq_some_iff.mp worldRead).1).trans worldRead

theorem compileFrame_call_preserves {program : Program} {code : CodeBlock} {slots : List EffectSlot}
    {fuel : Nat} {compiled : Core.Expr} {withCode : Bool}
    (accepted : AccountRuntime.compileFrame program code (slotTypes slots) fuel = .ok compiled)
    (eligible : ExecutableProgram (supported slots withCode)
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code]))
    {layout : Layout} {image : Option (List UInt8)} {handlers : ModeHandlers layout}
    {anchors : Anchors} {context : Context layout}
    {children : RuntimeCallEffectsSemantics.State → AccountCallSemantics.Children}
    {initial : RuntimeCallEffectsSemantics.State}
    {before initialStore store : Core.Store} {values environment captured : Core.Environment}
    {function argument : Core.Expr} {closure : Core.Value}
    (closureRelated : CapturedClosure compiled captured closure)
    (resolved : Core.Evaluates environment before function closure initialStore)
    (supplied : Core.Evaluates environment initialStore argument (bundleValues values) store)
    (length : values.length = slots.length)
    (runtime : EffectEnvironmentRel slots (AccountRuntime.frameScope (slotTypes slots)) Core.Renaming.id
      (values.reverse ++ .unit :: bundleValues values :: captured))
    (separated : EffectSlotsSeparate slots)
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
      ⟨"code", Core.WordMapping.type, cells.code⟩ ∈ slots ∧ ⟨"codeKnown", .bool, cells.known⟩ ∈ slots)
    (dataMember : ⟨"returnData", Core.WordMapping.type, layout.returnData⟩ ∈ slots)
    (dataSizeMember : ⟨"returnDataSize", .word, layout.returnDataSize⟩ ∈ slots)
    (mode : layout.codeCells.isSome = withCode)
    (callDepthMember : ⟨"callDepth", .word, layout.callDepth⟩ ∈ slots)
    (callHandlerMember : ⟨"callHandler", Core.OptionalCell.cellType Calls.callbackType, layout.callHandler⟩ ∈ slots)
    (callCodeMember : ⟨"callCodeHandler", Core.OptionalCell.cellType Calls.callbackType, handlers.callCode.location⟩ ∈ slots)
    (delegateMember : ⟨"delegateCallHandler", Core.OptionalCell.cellType Calls.callbackType, handlers.delegateCall.location⟩ ∈ slots)
    (callerMember : ∃ location, (⟨"caller", .word, location⟩ : EffectSlot) ∈ slots)
    (valueMember : ∃ location, (⟨"callvalue", .word, location⟩ : EffectSlot) ∈ slots)
    (createSlots : RuntimeCallModeEffectsCorrespondence.CreateSlots handlers slots)
    (initialRelated : StateRel (model layout (prefixRead layout.boundary store) slots image handlers anchors context) [] ⟨[], initial⟩ store)
    (passive : RuntimeLogEffectsCorrespondence.Passive layout.toLogLayout slots)
    (callPassive : CallPassive layout slots)
    (callbacks : ∀ {world state current},
      StateRel (model layout (prefixRead layout.boundary store) slots image handlers anchors context) world state current →
      ∀ operation, CallbackPreservation layout handlers anchors context children operation state.external)
    {final : Semantics.State RuntimeCallEffectsSemantics.State} {result : Semantics.Result Semantics.Value}
    (evaluated : Semantics.EvalFunction
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code]) (RuntimeCallModeSemantics.effectsWith children image)
      (AccountRuntime.frameFunction code) [] ⟨[], initial⟩ result final) :
    ∃ extension status accounts finalStore,
      accounts.map Prod.fst = final.external.runtime.runtime.runtime.runtime.runtime.storage.world ∧
      ResultRel .unit result status ∧
      Core.Evaluates environment before (.apply function argument)
        (frameCompletionValue status (snapshotValues final.external accounts)
          (StorageCorrespondence.get accounts final.external.runtime.runtime.runtime.runtime.runtime.storage.address final.external.runtime.runtime.runtime.runtime.runtime.storage.complete)) finalStore ∧
      StateRel (model layout (prefixRead layout.boundary store) slots image handlers anchors context)
        extension final finalStore := by
  obtain ⟨extension, status, accounts, finalStore, represented, related, executed, state, _⟩ :=
    compileFrame_call_preserves_observed accepted eligible closureRelated resolved supplied length runtime separated
      memoryMember worldMember addressMember completeMember staticMember memorySizeMember exitMember offsetMember sizeMember
      logsMember logSizeMember balancesMember codeMembers dataMember dataSizeMember mode callDepthMember callHandlerMember callCodeMember delegateMember callerMember valueMember createSlots initialRelated passive callPassive callbacks evaluated
  exact ⟨extension, status, accounts, finalStore, represented, related, executed, state⟩

/-- Direct evaluation of freshly compiled frame code is a special case of the
same theorem for captured calls. -/
theorem compileFrame_preserves {program : Program} {code : CodeBlock} {slots : List EffectSlot}
    {fuel : Nat} {compiled : Core.Expr} {withCode : Bool}
    (accepted : AccountRuntime.compileFrame program code (slotTypes slots) fuel = .ok compiled)
    (eligible : ExecutableProgram (supported slots withCode)
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code]))
    {layout : Layout} {image : Option (List UInt8)} {handlers : ModeHandlers layout}
    {anchors : Anchors} {context : Context layout}
    {children : RuntimeCallEffectsSemantics.State → AccountCallSemantics.Children}
    {initial : RuntimeCallEffectsSemantics.State}
    {initialStore store : Core.Store} {values environment : Core.Environment} {argument : Core.Expr}
    (supplied : Core.Evaluates environment initialStore argument (bundleValues values) store)
    (length : values.length = slots.length)
    (runtime : EffectEnvironmentRel slots (AccountRuntime.frameScope (slotTypes slots)) Core.Renaming.id
      (values.reverse ++ .unit :: bundleValues values :: environment))
    (separated : EffectSlotsSeparate slots)
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
      ⟨"code", Core.WordMapping.type, cells.code⟩ ∈ slots ∧ ⟨"codeKnown", .bool, cells.known⟩ ∈ slots)
    (dataMember : ⟨"returnData", Core.WordMapping.type, layout.returnData⟩ ∈ slots)
    (dataSizeMember : ⟨"returnDataSize", .word, layout.returnDataSize⟩ ∈ slots)
    (mode : layout.codeCells.isSome = withCode)
    (callDepthMember : ⟨"callDepth", .word, layout.callDepth⟩ ∈ slots)
    (callHandlerMember : ⟨"callHandler", Core.OptionalCell.cellType Calls.callbackType, layout.callHandler⟩ ∈ slots)
    (callCodeMember : ⟨"callCodeHandler", Core.OptionalCell.cellType Calls.callbackType, handlers.callCode.location⟩ ∈ slots)
    (delegateMember : ⟨"delegateCallHandler", Core.OptionalCell.cellType Calls.callbackType, handlers.delegateCall.location⟩ ∈ slots)
    (callerMember : ∃ location, (⟨"caller", .word, location⟩ : EffectSlot) ∈ slots)
    (valueMember : ∃ location, (⟨"callvalue", .word, location⟩ : EffectSlot) ∈ slots)
    (createSlots : RuntimeCallModeEffectsCorrespondence.CreateSlots handlers slots)
    (initialRelated : StateRel (model layout (prefixRead layout.boundary store) slots image handlers anchors context) [] ⟨[], initial⟩ store)
    (passive : RuntimeLogEffectsCorrespondence.Passive layout.toLogLayout slots)
    (callPassive : CallPassive layout slots)
    (callbacks : ∀ {world state current},
      StateRel (model layout (prefixRead layout.boundary store) slots image handlers anchors context) world state current →
      ∀ operation, CallbackPreservation layout handlers anchors context children operation state.external)
    {final : Semantics.State RuntimeCallEffectsSemantics.State} {result : Semantics.Result Semantics.Value}
    (evaluated : Semantics.EvalFunction
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code]) (RuntimeCallModeSemantics.effectsWith children image)
      (AccountRuntime.frameFunction code) [] ⟨[], initial⟩ result final) :
    ∃ extension status accounts finalStore,
      accounts.map Prod.fst = final.external.runtime.runtime.runtime.runtime.runtime.storage.world ∧
      ResultRel .unit result status ∧
      Core.Evaluates environment initialStore (.apply compiled argument)
        (frameCompletionValue status (snapshotValues final.external accounts)
          (StorageCorrespondence.get accounts final.external.runtime.runtime.runtime.runtime.runtime.storage.address final.external.runtime.runtime.runtime.runtime.runtime.storage.complete)) finalStore ∧
      StateRel (model layout (prefixRead layout.boundary store) slots image handlers anchors context)
        extension final finalStore := by
  obtain ⟨own, body, cells, _, _, rfl⟩ := compileFrame_components accepted
  exact compileFrame_call_preserves accepted eligible (CapturedClosure.lambda _ _ _ environment)
    Core.Evaluates.lambda supplied length runtime separated memoryMember worldMember addressMember completeMember
    staticMember memorySizeMember exitMember offsetMember sizeMember logsMember logSizeMember balancesMember codeMembers dataMember dataSizeMember mode
    callDepthMember callHandlerMember callCodeMember delegateMember callerMember valueMember createSlots initialRelated passive callPassive callbacks evaluated

end Solcore.Frontend.RustHull.RuntimeCallModeEffectsFrameCorrespondence
end

section
-- leanmerge: from Solcore.Frontend.RustHull.ContractCallModeCorrespondence
/-! Message calls and their shared state reach actual message
completion with or without linked code cells. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.ContractCallModeCorrespondence
open Correspondence ScalarExecution CodeBuilder

def messageValue (result : Semantics.Result Semantics.Value) (state : RuntimeCallEffectsSemantics.State)
    (accounts : StorageCorrespondence.Accounts) (target : Core.Word) : Core.Value :=
  ContractAccountCorrespondence.messageValue result state.runtime.runtime accounts target

def MessageRel (result : Semantics.Result Semantics.Value) (state : RuntimeCallEffectsSemantics.State)
    (target : Core.Word) (value : Core.Value) : Prop :=
  ContractAccountCorrespondence.MessageRel result state.runtime.runtime target value

theorem frameCall_message_evaluates {program : Program} {code : CodeBlock} {slots : List EffectSlot}
    {fuel : Nat} {compiled : Core.Expr} {withCode : Bool}
    (accepted : AccountRuntime.compileFrame program code (RuntimeLogEffectsFrameCorrespondence.slotTypes slots) fuel = .ok compiled)
    (eligible : DerivationCorrespondence.ExecutableProgram (RuntimeCallModeEffectsCorrespondence.supported slots withCode)
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code]))
    {layout : RuntimeCallEffectsCorrespondence.Layout} {image : Option (List UInt8)}
    {handlers : RuntimeCallModeEffectsCorrespondence.ModeHandlers layout}
    {anchors : RuntimeChildCallEffectsCorrespondence.Anchors}
    {context : RuntimeChildCallEffectsCorrespondence.Context layout}
    {children : RuntimeCallEffectsSemantics.State → AccountCallSemantics.Children}
    {initial : RuntimeCallEffectsSemantics.State}
    {before initialStore store : Core.Store} {values environment captured : Core.Environment}
    {function argument target deploying : Code} {depth : Nat}
    {shared : AccountRuntime.References} {images : List (Nat × List UInt8)} {closure : Core.Value}
    (closureRelated : CapturedClosure compiled captured closure)
    (resolved : Core.Evaluates environment before (function depth) closure initialStore)
    (supplied : Core.Evaluates environment initialStore (argument depth) (bundleValues values) store)
    (length : values.length = slots.length)
    (runtime : EffectEnvironmentRel slots (AccountRuntime.frameScope (RuntimeLogEffectsFrameCorrespondence.slotTypes slots)) Core.Renaming.id
      (values.reverse ++ .unit :: bundleValues values :: captured))
    (separated : EffectSlotsSeparate slots)
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
      ⟨"code", Core.WordMapping.type, cells.code⟩ ∈ slots ∧ ⟨"codeKnown", .bool, cells.known⟩ ∈ slots)
    (dataMember : ⟨"returnData", Core.WordMapping.type, layout.returnData⟩ ∈ slots)
    (dataSizeMember : ⟨"returnDataSize", .word, layout.returnDataSize⟩ ∈ slots)
    (mode : layout.codeCells.isSome = withCode)
    (callDepthMember : ⟨"callDepth", .word, layout.callDepth⟩ ∈ slots)
    (callHandlerMember : ⟨"callHandler", Core.OptionalCell.cellType Calls.callbackType, layout.callHandler⟩ ∈ slots)
    (callCodeMember : ⟨"callCodeHandler", Core.OptionalCell.cellType Calls.callbackType, handlers.callCode.location⟩ ∈ slots)
    (delegateMember : ⟨"delegateCallHandler", Core.OptionalCell.cellType Calls.callbackType, handlers.delegateCall.location⟩ ∈ slots)
    (callerMember : ∃ location, (⟨"caller", .word, location⟩ : EffectSlot) ∈ slots)
    (valueMember : ∃ location, (⟨"callvalue", .word, location⟩ : EffectSlot) ∈ slots)
    (createSlots : RuntimeCallModeEffectsCorrespondence.CreateSlots handlers slots)
    (initialRelated : StateRel (RuntimeCallModeEffectsCorrespondence.model layout (prefixRead layout.boundary store) slots image handlers anchors context) [] ⟨[], initial⟩ store)
    (passive : RuntimeLogEffectsCorrespondence.Passive layout.toLogLayout slots)
    (callPassive : RuntimeCallEffectsCorrespondence.CallPassive layout slots)
    (callbacks : ∀ {world state current},
      StateRel (RuntimeCallModeEffectsCorrespondence.model layout (prefixRead layout.boundary store) slots image handlers anchors context) world state current →
      ∀ operation, RuntimeCallModeEffectsCorrespondence.CallbackPreservation layout handlers anchors context children operation state.external)
    {final : Semantics.State RuntimeCallEffectsSemantics.State} {result : Semantics.Result Semantics.Value}
    (evaluated : Semantics.EvalFunction
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code]) (RuntimeCallModeSemantics.effectsWith children image)
      (AccountRuntime.frameFunction code) [] ⟨[], initial⟩ result final)
    (address : Core.Word)
    (worldReference : CodeValue depth environment (AccountRuntime.reference shared "world")
      (.cellRef AccountState.type layout.storage.world))
    (balancesReference : CodeValue depth environment (AccountRuntime.reference shared "balances")
      (.cellRef Core.WordMapping.type layout.balances))
    (targetValue : CodeValue depth environment target (.word address))
    (deployingValue : CodeValue depth environment deploying (.bool false)) :
    ∃ value finalStore, Core.Evaluates environment before
      (bind (apply function argument) (fun framed => AccountRuntime.completeMessage shared images target deploying framed) depth)
      value finalStore ∧ MessageRel result final.external address value := by
  obtain ⟨extension, status, accounts, bodyStore, represented, statusRelated, executed, related, worldFinal⟩ :=
    RuntimeCallModeEffectsFrameCorrespondence.compileFrame_call_preserves_observed accepted eligible closureRelated resolved supplied length
      runtime separated memoryMember worldMember addressMember completeMember staticMember memorySizeMember exitMember offsetMember sizeMember
      logsMember logSizeMember balancesMember codeMembers dataMember dataSizeMember mode callDepthMember callHandlerMember callCodeMember delegateMember callerMember valueMember createSlots initialRelated passive callPassive callbacks evaluated
  have balancesFinal := RuntimeAccountEffectsCorrespondence.balances_related (RuntimeCallEffectsCorrespondence.account_related (RuntimeCallModeEffectsCorrespondence.base_related related))
  let frameResult := frameCompletionValue status (ContractLogCorrespondence.snapshotValues final.external.runtime.runtime.runtime accounts final.external.runtime.runtime.balances)
    (StorageCorrespondence.get accounts final.external.runtime.runtime.runtime.runtime.runtime.storage.address final.external.runtime.runtime.runtime.runtime.runtime.storage.complete)
  obtain ⟨finalStore, completed⟩ := ContractLogCorrespondence.message_evaluates result final.external.runtime.runtime.runtime accounts address final.external.runtime.runtime.balances
    statusRelated (worldReference.prepend [frameResult]) (balancesReference.prepend [frameResult])
    (targetValue.prepend [frameResult]) (deployingValue.prepend [frameResult])
    (CodeValue.bound depth environment frameResult) worldFinal balancesFinal
  exact ⟨_, finalStore, .letE executed completed, accounts, represented, rfl⟩

end Solcore.Frontend.RustHull.ContractCallModeCorrespondence
end

section
-- leanmerge: from Solcore.Frontend.RustHull.RuntimeChildCallEffectsCorrespondence
/-! Ordinary and static calls join all existing concrete effects in the
recursive Hull proof. The callback evidence is supplied by actual installation. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.RuntimeChildCallEffectsCorrespondence
open Correspondence ScalarExecution DerivationCorrespondence
open RuntimeCallEffectsCorrespondence (Layout Handlers CallPassive supported primitive_none runtime_enabled sourceRuntime patched runtime_related runtime_updated)

theorem external_preserves (layout : Layout) (baseline : Nat → Option Core.Value)
    (slots : List EffectSlot) (image : Option (List UInt8)) (withCode : Bool) (handlers : Handlers layout)
    (passive : RuntimeLogEffectsCorrespondence.Passive layout.toLogLayout slots) (callPassive : CallPassive layout slots)
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
    (callDepthMember : ⟨"callDepth", .word, layout.callDepth⟩ ∈ slots)
    (callHandlerMember : ⟨"callHandler", Core.OptionalCell.cellType Calls.callbackType, layout.callHandler⟩ ∈ slots)
    (anchors : Anchors) (context : Context layout)
    (children : RuntimeCallEffectsSemantics.State → AccountCallSemantics.Children)
    (callbacks : ∀ {world state store},
      StateRel (model layout baseline slots image handlers anchors context) world state store →
      CallbackPreservation layout handlers anchors context children state.external) :
    ExternalCallPreservation (supported slots withCode) (model layout baseline slots image handlers anchors context) slots
      (RuntimeCallEffectsSemantics.effectsWith children image) := by
  intro functions name type sources initial final result enabled notFunction called
  cases called with
  | function selected called => rw [notFunction] at selected; contradiction
  | primitive absent computed => rw [primitive_none enabled] at computed; contradiction
  | external absent notPrimitive computed =>
      cases computed with
      | runtime computed =>
          intro typeFuel expected typeCompiled scope arguments lowered compiled world mapping environment initialStore argumentStore targets codes locations captured related packed runtime state installed
          have call : Semantics.EvalCall functions (RuntimeReturnDataEffectsSemantics.effects image) name type sources
              (sourceRuntime initial) result _ := .external absent notPrimitive computed
          obtain ⟨target, finalStore, resultRelated, evaluated, finalState, installedFinal, retained⟩ :=
            RuntimeLinkedReturnDataEffectsCorrespondence.external_preserves layout.toReturnDataLayout
              (patched layout baseline initial.external) slots image withCode passive
              memoryMember worldMember addressMember completeMember staticMember memorySizeMember exitMember offsetMember sizeMember
              logsMember logSizeMember balancesMember codeMembers dataMember dataSizeMember mode anchors
              (runtime_enabled enabled computed) notFunction call typeCompiled compiled related packed runtime
              (RuntimeLinkedReturnDataEffectsCorrespondence.of_base (runtime_related (base_related state)) (linked_related state)) installed
          have baseFinal := runtime_updated (base_related state)
            (RuntimeLinkedReturnDataEffectsCorrespondence.base_related finalState)
            (RuntimeCallEffectsSemantics.runtime_balances computed)
          exact ⟨target, finalStore, resultRelated, evaluated,
            of_base baseFinal (RuntimeLinkedReturnDataEffectsCorrespondence.linked_related finalState)
              (context.updated (base_related state) baseFinal state.external.2.2.1.2), installedFinal, retained⟩
      | call computed =>
          intro typeFuel expected typeCompiled scope arguments lowered compiled world mapping environment initialStore argumentStore targets codes locations captured related packed runtime state installed
          obtain ⟨target, finalStore, resultRelated, evaluated, finalState, retained⟩ :=
            ChildCallBuiltinCorrespondence.ordinary_preserves compiled computed related runtime passive callPassive
              memoryMember memorySizeMember dataMember dataSizeMember callHandlerMember addressMember callDepthMember staticMember
              exitMember offsetMember sizeMember state (callbacks state) packed
          exact ⟨target, finalStore, resultRelated, evaluated, finalState, installed.preserved retained, retained⟩
      | staticCall computed =>
          intro typeFuel expected typeCompiled scope arguments lowered compiled world mapping environment initialStore argumentStore targets codes locations captured related packed runtime state installed
          obtain ⟨target, finalStore, resultRelated, evaluated, finalState, retained⟩ :=
            ChildCallBuiltinCorrespondence.static_preserves compiled computed related runtime passive callPassive
              memoryMember memorySizeMember dataMember dataSizeMember callHandlerMember addressMember callDepthMember staticMember
              exitMember offsetMember sizeMember state (callbacks state) packed
          exact ⟨target, finalStore, resultRelated, evaluated, finalState, installed.preserved retained, retained⟩

theorem assemble_program (layout : Layout) (baseline : Nat → Option Core.Value)
    (slots : List EffectSlot) (image : Option (List UInt8)) (withCode : Bool) (handlers : Handlers layout)
    (passive : RuntimeLogEffectsCorrespondence.Passive layout.toLogLayout slots) (callPassive : CallPassive layout slots)
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
    (callDepthMember : ⟨"callDepth", .word, layout.callDepth⟩ ∈ slots)
    (callHandlerMember : ⟨"callHandler", Core.OptionalCell.cellType Calls.callbackType, layout.callHandler⟩ ∈ slots)
    (anchors : Anchors) (context : Context layout)
    (children : RuntimeCallEffectsSemantics.State → AccountCallSemantics.Children)
    (callbacks : ∀ {world state store},
      StateRel (model layout baseline slots image handlers anchors context) world state store →
      CallbackPreservation layout handlers anchors context children state.external)
    {functions : List Function} {function : Function} {entry : String} {runtime : Scope}
    {fuel : Nat} {own : Signature} {allocated : Core.Expr}
    (accepted : assemble functions entry runtime fuel = .ok (own, allocated))
    (selected : functions.find? (·.name == entry) = some function)
    (eligible : ExecutableProgram (supported slots withCode) functions)
    {sources : List Semantics.Value} {targets : List Core.Value}
    (values : ValuesRel own.parameters sources targets)
    {initial final : Semantics.State RuntimeCallEffectsSemantics.State}
    {sourceResult : Semantics.Result Semantics.Value}
    (evaluated : Semantics.EvalFunction functions (RuntimeCallEffectsSemantics.effectsWith children image)
      function sources initial sourceResult final)
    {world : World} {runtimeValues caller : Core.Environment} {store : Core.Store}
    (runtimeLength : runtimeValues.length = runtime.length)
    (covered : ScopeCoverage [] runtime)
    (runtimeRelated : EffectEnvironmentRel slots runtime Core.Renaming.id
      (runtimeValues ++ bundleValues targets :: caller))
    (separated : EffectSlotsSeparate slots)
    (state : StateRel (model layout baseline slots image handlers anchors context) world initial store) :
    ∃ extension target finalStore,
      ResultRel own.result sourceResult target ∧
      Core.Evaluates (runtimeValues ++ bundleValues targets :: caller) store allocated target finalStore ∧
      StateRel (model layout baseline slots image handlers anchors context) (world ++ extension) final finalStore ∧
      ClosuresPreserved store finalStore :=
  assemble_recursive_program_effects accepted selected
    (external_preserves layout baseline slots image withCode handlers passive callPassive memoryMember worldMember addressMember completeMember staticMember
      memorySizeMember exitMember offsetMember sizeMember logsMember logSizeMember balancesMember codeMembers dataMember dataSizeMember mode callDepthMember callHandlerMember anchors context children callbacks) eligible values evaluated
    runtimeLength covered runtimeRelated separated state


end Solcore.Frontend.RustHull.RuntimeChildCallEffectsCorrespondence
end

section
-- leanmerge: from Solcore.Frontend.RustHull.RuntimeChildCallEffectsFrameCorrespondence
/-! Source message calls reach actual frame calls and final snapshots.
The same proof covers ordinary frames and frames with linked code slots. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.RuntimeChildCallEffectsFrameCorrespondence
open Correspondence ScalarExecution DerivationCorrespondence
open RuntimeCallEffectsCorrespondence (Layout Handlers CallPassive account_related)
open RuntimeChildCallEffectsCorrespondence (model base_related Context Anchors CallbackPreservation assemble_program)
open RuntimeAccountEffectsCorrespondence (runtime_related balances_related)
open RuntimeCallEffectsCorrespondence (supported)

abbrev slotTypes := RuntimeLogEffectsFrameCorrespondence.slotTypes
abbrev cell_observed := @RuntimeLogEffectsFrameCorrespondence.cell_observed
def snapshotValues (state : RuntimeCallEffectsSemantics.State) :=
  RuntimeAccountEffectsFrameCorrespondence.snapshotValues state.runtime.runtime

/-- A frame installed earlier retains its captured environment. The body and
completion wrapper observe the final source world and balances through the
compiler's actual frame references. -/
theorem compileFrame_call_preserves_observed {program : Program} {code : CodeBlock} {slots : List EffectSlot}
    {fuel : Nat} {compiled : Core.Expr} {withCode : Bool}
    (accepted : AccountRuntime.compileFrame program code (slotTypes slots) fuel = .ok compiled)
    (eligible : ExecutableProgram (supported slots withCode)
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code]))
    {layout : Layout} {image : Option (List UInt8)} {handlers : Handlers layout}
    {anchors : Anchors} {context : Context layout}
    {children : RuntimeCallEffectsSemantics.State → AccountCallSemantics.Children}
    {initial : RuntimeCallEffectsSemantics.State}
    {before initialStore store : Core.Store} {values environment captured : Core.Environment}
    {function argument : Core.Expr} {closure : Core.Value}
    (closureRelated : CapturedClosure compiled captured closure)
    (resolved : Core.Evaluates environment before function closure initialStore)
    (supplied : Core.Evaluates environment initialStore argument (bundleValues values) store)
    (length : values.length = slots.length)
    (runtime : EffectEnvironmentRel slots (AccountRuntime.frameScope (slotTypes slots)) Core.Renaming.id
      (values.reverse ++ .unit :: bundleValues values :: captured))
    (separated : EffectSlotsSeparate slots)
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
      ⟨"code", Core.WordMapping.type, cells.code⟩ ∈ slots ∧ ⟨"codeKnown", .bool, cells.known⟩ ∈ slots)
    (dataMember : ⟨"returnData", Core.WordMapping.type, layout.returnData⟩ ∈ slots)
    (dataSizeMember : ⟨"returnDataSize", .word, layout.returnDataSize⟩ ∈ slots)
    (mode : layout.codeCells.isSome = withCode)
    (callDepthMember : ⟨"callDepth", .word, layout.callDepth⟩ ∈ slots)
    (callHandlerMember : ⟨"callHandler", Core.OptionalCell.cellType Calls.callbackType, layout.callHandler⟩ ∈ slots)
    (initialRelated : StateRel (model layout (prefixRead layout.boundary store) slots image handlers anchors context) [] ⟨[], initial⟩ store)
    (passive : RuntimeLogEffectsCorrespondence.Passive layout.toLogLayout slots)
    (callPassive : CallPassive layout slots)
    (callbacks : ∀ {world state current},
      StateRel (model layout (prefixRead layout.boundary store) slots image handlers anchors context) world state current →
      CallbackPreservation layout handlers anchors context children state.external)
    {final : Semantics.State RuntimeCallEffectsSemantics.State} {result : Semantics.Result Semantics.Value}
    (evaluated : Semantics.EvalFunction
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code]) (RuntimeCallEffectsSemantics.effectsWith children image)
      (AccountRuntime.frameFunction code) [] ⟨[], initial⟩ result final) :
    ∃ extension status accounts finalStore,
      accounts.map Prod.fst = final.external.runtime.runtime.runtime.runtime.runtime.storage.world ∧
      ResultRel .unit result status ∧
      Core.Evaluates environment before (.apply function argument)
        (frameCompletionValue status (snapshotValues final.external accounts)
          (StorageCorrespondence.get accounts final.external.runtime.runtime.runtime.runtime.runtime.storage.address final.external.runtime.runtime.runtime.runtime.runtime.storage.complete)) finalStore ∧
      StateRel (model layout (prefixRead layout.boundary store) slots image handlers anchors context)
        extension final finalStore ∧
      finalStore.read? layout.storage.world = some (StorageCorrespondence.world accounts) := by
  obtain ⟨own, body, cells, assembled, references, rfl⟩ := compileFrame_components accepted
  have selected := MemoryFrameCorrespondence.frame_selected accepted
  obtain ⟨signatures, codes, selectedFunction, selectedCode, index, _, sourceSelected,
    signatureCompiled, _, _, _, _, _⟩ := assemble_selection assembled
  have sameFunction := Option.some.inj (sourceSelected.symm.trans selected)
  subst selectedFunction
  obtain ⟨parameters, resultType⟩ := MemoryFrameCorrespondence.frame_signature signatureCompiled
  have argumentValues : ValuesRel own.parameters [] [] := by rw [parameters]; exact .nil
  obtain ⟨extension, status, bodyStore, related, executed, state, _⟩ :=
    assemble_program layout (prefixRead layout.boundary store) slots image withCode handlers passive callPassive
      memoryMember worldMember addressMember completeMember staticMember memorySizeMember exitMember offsetMember sizeMember
      logsMember logSizeMember balancesMember codeMembers dataMember dataSizeMember mode callDepthMember callHandlerMember anchors context children callbacks assembled selected eligible argumentValues evaluated
      (runtimeValues := values.reverse) (caller := bundleValues values :: captured)
      (by simpa [AccountRuntime.frameScope, slotTypes, MemoryFrameCorrespondence.slotTypes] using length)
      (MemoryFrameCorrespondence.frame_coverage _) runtime separated
      initialRelated
  have finalStorage := RuntimeEffectsCorrespondence.storage_related
    (RuntimeEnvironmentEffectsCorrespondence.runtime_related (RuntimeLogEffectsCorrespondence.runtime_related (runtime_related (account_related (base_related state)))))
  have finalLogs := RuntimeLogEffectsCorrespondence.logs_related (runtime_related (account_related (base_related state)))
  obtain ⟨accounts, sourceWorld, worldRead⟩ := finalStorage.world
  have finalWorld := cell_observed references runtime worldMember worldRead
  have finalAddress := cell_observed references runtime addressMember finalStorage.address
  have finalComplete := cell_observed references runtime completeMember finalStorage.complete
  have finalSnapshot : ∀ name ∈ frameSnapshotNames,
      FrameCellObserved cells (values.reverse ++ .unit :: bundleValues values :: captured)
        bodyStore name (snapshotValues final.external accounts name) := by
    intro name member
    simp [frameSnapshotNames] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact cell_observed references runtime exitMember finalStorage.exit
    · exact cell_observed references runtime offsetMember finalStorage.returnOffset
    · exact cell_observed references runtime sizeMember finalStorage.returnSize
    · exact cell_observed references runtime memoryMember finalLogs.logs.memory
    · exact cell_observed references runtime logsMember finalLogs.logs.logs
    · exact cell_observed references runtime logSizeMember finalLogs.logs.logSize
    · exact cell_observed references runtime balancesMember (balances_related (account_related (base_related state)))
    · exact finalWorld
  have completed := frameCompletion_evaluates executed accounts final.external.runtime.runtime.runtime.runtime.runtime.storage.address final.external.runtime.runtime.runtime.runtime.runtime.storage.complete
    finalWorld finalAddress finalComplete finalSnapshot
  obtain ⟨suffix, _, extended⟩ := StorageCorrespondence.getStore_extension accounts
    final.external.runtime.runtime.runtime.runtime.runtime.storage.address final.external.runtime.runtime.runtime.runtime.runtime.storage.complete
    (status :: (values.reverse ++ .unit :: bundleValues values :: captured)) bodyStore
  refine ⟨extension, status, accounts, _, sourceWorld, by simpa only [resultType] using related,
    frameUnpack_call_evaluates (by simpa only [slotTypes, MemoryFrameCorrespondence.slotTypes, List.length_map] using length)
      closureRelated resolved supplied completed, ?_, ?_⟩
  · rw [show bundleValues ([] : List Core.Value) = .unit from rfl, extended]
    simpa only [List.nil_append] using state.appendCore suffix
  · rw [show bundleValues ([] : List Core.Value) = .unit from rfl, extended]
    exact ((StoreRetains.append bodyStore suffix).read layout.storage.world
      (List.getElem?_eq_some_iff.mp worldRead).1).trans worldRead

theorem compileFrame_call_preserves {program : Program} {code : CodeBlock} {slots : List EffectSlot}
    {fuel : Nat} {compiled : Core.Expr} {withCode : Bool}
    (accepted : AccountRuntime.compileFrame program code (slotTypes slots) fuel = .ok compiled)
    (eligible : ExecutableProgram (supported slots withCode)
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code]))
    {layout : Layout} {image : Option (List UInt8)} {handlers : Handlers layout}
    {anchors : Anchors} {context : Context layout}
    {children : RuntimeCallEffectsSemantics.State → AccountCallSemantics.Children}
    {initial : RuntimeCallEffectsSemantics.State}
    {before initialStore store : Core.Store} {values environment captured : Core.Environment}
    {function argument : Core.Expr} {closure : Core.Value}
    (closureRelated : CapturedClosure compiled captured closure)
    (resolved : Core.Evaluates environment before function closure initialStore)
    (supplied : Core.Evaluates environment initialStore argument (bundleValues values) store)
    (length : values.length = slots.length)
    (runtime : EffectEnvironmentRel slots (AccountRuntime.frameScope (slotTypes slots)) Core.Renaming.id
      (values.reverse ++ .unit :: bundleValues values :: captured))
    (separated : EffectSlotsSeparate slots)
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
      ⟨"code", Core.WordMapping.type, cells.code⟩ ∈ slots ∧ ⟨"codeKnown", .bool, cells.known⟩ ∈ slots)
    (dataMember : ⟨"returnData", Core.WordMapping.type, layout.returnData⟩ ∈ slots)
    (dataSizeMember : ⟨"returnDataSize", .word, layout.returnDataSize⟩ ∈ slots)
    (mode : layout.codeCells.isSome = withCode)
    (callDepthMember : ⟨"callDepth", .word, layout.callDepth⟩ ∈ slots)
    (callHandlerMember : ⟨"callHandler", Core.OptionalCell.cellType Calls.callbackType, layout.callHandler⟩ ∈ slots)
    (initialRelated : StateRel (model layout (prefixRead layout.boundary store) slots image handlers anchors context) [] ⟨[], initial⟩ store)
    (passive : RuntimeLogEffectsCorrespondence.Passive layout.toLogLayout slots)
    (callPassive : CallPassive layout slots)
    (callbacks : ∀ {world state current},
      StateRel (model layout (prefixRead layout.boundary store) slots image handlers anchors context) world state current →
      CallbackPreservation layout handlers anchors context children state.external)
    {final : Semantics.State RuntimeCallEffectsSemantics.State} {result : Semantics.Result Semantics.Value}
    (evaluated : Semantics.EvalFunction
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code]) (RuntimeCallEffectsSemantics.effectsWith children image)
      (AccountRuntime.frameFunction code) [] ⟨[], initial⟩ result final) :
    ∃ extension status accounts finalStore,
      accounts.map Prod.fst = final.external.runtime.runtime.runtime.runtime.runtime.storage.world ∧
      ResultRel .unit result status ∧
      Core.Evaluates environment before (.apply function argument)
        (frameCompletionValue status (snapshotValues final.external accounts)
          (StorageCorrespondence.get accounts final.external.runtime.runtime.runtime.runtime.runtime.storage.address final.external.runtime.runtime.runtime.runtime.runtime.storage.complete)) finalStore ∧
      StateRel (model layout (prefixRead layout.boundary store) slots image handlers anchors context)
        extension final finalStore := by
  obtain ⟨extension, status, accounts, finalStore, represented, related, executed, state, _⟩ :=
    compileFrame_call_preserves_observed accepted eligible closureRelated resolved supplied length runtime separated
      memoryMember worldMember addressMember completeMember staticMember memorySizeMember exitMember offsetMember sizeMember
      logsMember logSizeMember balancesMember codeMembers dataMember dataSizeMember mode callDepthMember callHandlerMember initialRelated passive callPassive callbacks evaluated
  exact ⟨extension, status, accounts, finalStore, represented, related, executed, state⟩

/-- Direct evaluation of freshly compiled frame code is a special case of the
same theorem for captured calls. -/
theorem compileFrame_preserves {program : Program} {code : CodeBlock} {slots : List EffectSlot}
    {fuel : Nat} {compiled : Core.Expr} {withCode : Bool}
    (accepted : AccountRuntime.compileFrame program code (slotTypes slots) fuel = .ok compiled)
    (eligible : ExecutableProgram (supported slots withCode)
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code]))
    {layout : Layout} {image : Option (List UInt8)} {handlers : Handlers layout}
    {anchors : Anchors} {context : Context layout}
    {children : RuntimeCallEffectsSemantics.State → AccountCallSemantics.Children}
    {initial : RuntimeCallEffectsSemantics.State}
    {initialStore store : Core.Store} {values environment : Core.Environment} {argument : Core.Expr}
    (supplied : Core.Evaluates environment initialStore argument (bundleValues values) store)
    (length : values.length = slots.length)
    (runtime : EffectEnvironmentRel slots (AccountRuntime.frameScope (slotTypes slots)) Core.Renaming.id
      (values.reverse ++ .unit :: bundleValues values :: environment))
    (separated : EffectSlotsSeparate slots)
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
      ⟨"code", Core.WordMapping.type, cells.code⟩ ∈ slots ∧ ⟨"codeKnown", .bool, cells.known⟩ ∈ slots)
    (dataMember : ⟨"returnData", Core.WordMapping.type, layout.returnData⟩ ∈ slots)
    (dataSizeMember : ⟨"returnDataSize", .word, layout.returnDataSize⟩ ∈ slots)
    (mode : layout.codeCells.isSome = withCode)
    (callDepthMember : ⟨"callDepth", .word, layout.callDepth⟩ ∈ slots)
    (callHandlerMember : ⟨"callHandler", Core.OptionalCell.cellType Calls.callbackType, layout.callHandler⟩ ∈ slots)
    (initialRelated : StateRel (model layout (prefixRead layout.boundary store) slots image handlers anchors context) [] ⟨[], initial⟩ store)
    (passive : RuntimeLogEffectsCorrespondence.Passive layout.toLogLayout slots)
    (callPassive : CallPassive layout slots)
    (callbacks : ∀ {world state current},
      StateRel (model layout (prefixRead layout.boundary store) slots image handlers anchors context) world state current →
      CallbackPreservation layout handlers anchors context children state.external)
    {final : Semantics.State RuntimeCallEffectsSemantics.State} {result : Semantics.Result Semantics.Value}
    (evaluated : Semantics.EvalFunction
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code]) (RuntimeCallEffectsSemantics.effectsWith children image)
      (AccountRuntime.frameFunction code) [] ⟨[], initial⟩ result final) :
    ∃ extension status accounts finalStore,
      accounts.map Prod.fst = final.external.runtime.runtime.runtime.runtime.runtime.storage.world ∧
      ResultRel .unit result status ∧
      Core.Evaluates environment initialStore (.apply compiled argument)
        (frameCompletionValue status (snapshotValues final.external accounts)
          (StorageCorrespondence.get accounts final.external.runtime.runtime.runtime.runtime.runtime.storage.address final.external.runtime.runtime.runtime.runtime.runtime.storage.complete)) finalStore ∧
      StateRel (model layout (prefixRead layout.boundary store) slots image handlers anchors context)
        extension final finalStore := by
  obtain ⟨own, body, cells, _, _, rfl⟩ := compileFrame_components accepted
  exact compileFrame_call_preserves accepted eligible (CapturedClosure.lambda _ _ _ environment)
    Core.Evaluates.lambda supplied length runtime separated memoryMember worldMember addressMember completeMember
    staticMember memorySizeMember exitMember offsetMember sizeMember logsMember logSizeMember balancesMember codeMembers dataMember dataSizeMember mode
    callDepthMember callHandlerMember initialRelated passive callPassive callbacks evaluated

end Solcore.Frontend.RustHull.RuntimeChildCallEffectsFrameCorrespondence
end

section
-- leanmerge: from Solcore.Frontend.RustHull.ContractChildCallCorrespondence
/-! Message calls and their shared state reach actual message
completion with or without linked code cells. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.ContractChildCallCorrespondence
open Correspondence ScalarExecution CodeBuilder

def supported (withCode : Bool) (name : String) : Prop :=
  ContractReturnDataCorrespondence.supported withCode name ∨ name = "call" ∨ name = "staticcall"

theorem supported_actual {slots : List EffectSlot} {withCode : Bool}
    (signature : RuntimeEffectsFrameCorrespondence.slotTypes slots = RuntimeExtendedInitializedEffects.slots withCode) :
    RuntimeCallEffectsCorrespondence.supported slots withCode = supported withCode := by
  funext name
  apply propext
  simp only [RuntimeCallEffectsCorrespondence.supported, supported,
    ContractReturnDataCorrespondence.supported_actual signature]

def messageValue (result : Semantics.Result Semantics.Value) (state : RuntimeCallEffectsSemantics.State)
    (accounts : StorageCorrespondence.Accounts) (target : Core.Word) : Core.Value :=
  ContractAccountCorrespondence.messageValue result state.runtime.runtime accounts target

def MessageRel (result : Semantics.Result Semantics.Value) (state : RuntimeCallEffectsSemantics.State)
    (target : Core.Word) (value : Core.Value) : Prop :=
  ContractAccountCorrespondence.MessageRel result state.runtime.runtime target value

theorem frameCall_message_evaluates {program : Program} {code : CodeBlock} {slots : List EffectSlot}
    {fuel : Nat} {compiled : Core.Expr} {withCode : Bool}
    (accepted : AccountRuntime.compileFrame program code (RuntimeLogEffectsFrameCorrespondence.slotTypes slots) fuel = .ok compiled)
    (eligible : DerivationCorrespondence.ExecutableProgram (RuntimeCallEffectsCorrespondence.supported slots withCode)
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code]))
    {layout : RuntimeCallEffectsCorrespondence.Layout} {image : Option (List UInt8)}
    {handlers : RuntimeCallEffectsCorrespondence.Handlers layout}
    {anchors : RuntimeChildCallEffectsCorrespondence.Anchors}
    {context : RuntimeChildCallEffectsCorrespondence.Context layout}
    {children : RuntimeCallEffectsSemantics.State → AccountCallSemantics.Children}
    {initial : RuntimeCallEffectsSemantics.State}
    {before initialStore store : Core.Store} {values environment captured : Core.Environment}
    {function argument target deploying : Code} {depth : Nat}
    {shared : AccountRuntime.References} {images : List (Nat × List UInt8)} {closure : Core.Value}
    (closureRelated : CapturedClosure compiled captured closure)
    (resolved : Core.Evaluates environment before (function depth) closure initialStore)
    (supplied : Core.Evaluates environment initialStore (argument depth) (bundleValues values) store)
    (length : values.length = slots.length)
    (runtime : EffectEnvironmentRel slots (AccountRuntime.frameScope (RuntimeLogEffectsFrameCorrespondence.slotTypes slots)) Core.Renaming.id
      (values.reverse ++ .unit :: bundleValues values :: captured))
    (separated : EffectSlotsSeparate slots)
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
      ⟨"code", Core.WordMapping.type, cells.code⟩ ∈ slots ∧ ⟨"codeKnown", .bool, cells.known⟩ ∈ slots)
    (dataMember : ⟨"returnData", Core.WordMapping.type, layout.returnData⟩ ∈ slots)
    (dataSizeMember : ⟨"returnDataSize", .word, layout.returnDataSize⟩ ∈ slots)
    (mode : layout.codeCells.isSome = withCode)
    (callDepthMember : ⟨"callDepth", .word, layout.callDepth⟩ ∈ slots)
    (callHandlerMember : ⟨"callHandler", Core.OptionalCell.cellType Calls.callbackType, layout.callHandler⟩ ∈ slots)
    (initialRelated : StateRel (RuntimeChildCallEffectsCorrespondence.model layout (prefixRead layout.boundary store) slots image handlers anchors context) [] ⟨[], initial⟩ store)
    (passive : RuntimeLogEffectsCorrespondence.Passive layout.toLogLayout slots)
    (callPassive : RuntimeCallEffectsCorrespondence.CallPassive layout slots)
    (callbacks : ∀ {world state current},
      StateRel (RuntimeChildCallEffectsCorrespondence.model layout (prefixRead layout.boundary store) slots image handlers anchors context) world state current →
      RuntimeChildCallEffectsCorrespondence.CallbackPreservation layout handlers anchors context children state.external)
    {final : Semantics.State RuntimeCallEffectsSemantics.State} {result : Semantics.Result Semantics.Value}
    (evaluated : Semantics.EvalFunction
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code]) (RuntimeCallEffectsSemantics.effectsWith children image)
      (AccountRuntime.frameFunction code) [] ⟨[], initial⟩ result final)
    (address : Core.Word)
    (worldReference : CodeValue depth environment (AccountRuntime.reference shared "world")
      (.cellRef AccountState.type layout.storage.world))
    (balancesReference : CodeValue depth environment (AccountRuntime.reference shared "balances")
      (.cellRef Core.WordMapping.type layout.balances))
    (targetValue : CodeValue depth environment target (.word address))
    (deployingValue : CodeValue depth environment deploying (.bool false)) :
    ∃ value finalStore, Core.Evaluates environment before
      (bind (apply function argument) (fun framed => AccountRuntime.completeMessage shared images target deploying framed) depth)
      value finalStore ∧ MessageRel result final.external address value := by
  obtain ⟨extension, status, accounts, bodyStore, represented, statusRelated, executed, related, worldFinal⟩ :=
    RuntimeChildCallEffectsFrameCorrespondence.compileFrame_call_preserves_observed accepted eligible closureRelated resolved supplied length
      runtime separated memoryMember worldMember addressMember completeMember staticMember memorySizeMember exitMember offsetMember sizeMember
      logsMember logSizeMember balancesMember codeMembers dataMember dataSizeMember mode callDepthMember callHandlerMember initialRelated passive callPassive callbacks evaluated
  have balancesFinal := RuntimeAccountEffectsCorrespondence.balances_related (RuntimeCallEffectsCorrespondence.account_related (RuntimeChildCallEffectsCorrespondence.base_related related))
  let frameResult := frameCompletionValue status (ContractLogCorrespondence.snapshotValues final.external.runtime.runtime.runtime accounts final.external.runtime.runtime.balances)
    (StorageCorrespondence.get accounts final.external.runtime.runtime.runtime.runtime.runtime.storage.address final.external.runtime.runtime.runtime.runtime.runtime.storage.complete)
  obtain ⟨finalStore, completed⟩ := ContractLogCorrespondence.message_evaluates result final.external.runtime.runtime.runtime accounts address final.external.runtime.runtime.balances
    statusRelated (worldReference.prepend [frameResult]) (balancesReference.prepend [frameResult])
    (targetValue.prepend [frameResult]) (deployingValue.prepend [frameResult])
    (CodeValue.bound depth environment frameResult) worldFinal balancesFinal
  exact ⟨_, finalStore, .letE executed completed, accounts, represented, rfl⟩

end Solcore.Frontend.RustHull.ContractChildCallCorrespondence
end
