import Solcore.Frontend.RustHull.LifecycleBuiltinCorrespondence
import Solcore.Frontend.RustHull.RuntimeCallModeSupported
import Solcore.Frontend.RustHull.RuntimeCallModeCompatibility
import Solcore.Frontend.RustHull.CallModeBuiltinCorrespondence
import Solcore.Frontend.RustHull.ChildCallBuiltinCorrespondence
import Solcore.Frontend.RustHull.RuntimeLinkedReturnDataEffectsCorrespondence
import Solcore.Frontend.RustHull.CreationBuiltinCorrespondence
import Solcore.Frontend.RustHull.RevertBuiltinCorrespondence
import Solcore.Frontend.RustHull.YulBuiltinCorrespondence

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
      (RuntimeCallModeSemantics.effectsWith children image) := by
  intro functions sourceEnvironment body initial control final _ assembled signatures codes locations captured span
  intro fuel scope result loops expression compiled covered world mapping environment store _ _ runtime heap installed
  obtain ⟨external, executed, rfl⟩ := assembled
  cases fuel with
  | zero => simp [lowerStatement, fail] at compiled
  | succ fuel =>
      simp only [lowerStatement] at compiled
      obtain ⟨target, finalStore, related, evaluated, finalRelated, closures⟩ :=
        YulBuiltinCorrespondence.preserves passive memoryMember memorySizeMember exitMember offsetMember sizeMember
          executed compiled runtime heap
      exact ⟨[], target, finalStore, related, evaluated, by rw [List.append_nil]; exact finalRelated,
        installed.preserved closures, closures⟩

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
