import Solcore.Frontend.RustHull.ContractAccountCorrespondence
import Solcore.Frontend.RustHull.RuntimeCodeEffectsFrameCorrespondence

/-! Code-image operations pass through the actual message finalizer with the
existing account, memory, environment and event observations. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.ContractCodeCorrespondence
open Correspondence ScalarExecution CodeBuilder

def supported (name : String) : Prop := ContractAccountCorrespondence.supported name ∨
  name = "codesize" ∨ ∃ operation : CodeImageSemantics.Operation, operation.name = name

abbrev messageValue := ContractAccountCorrespondence.messageValue
abbrev MessageRel := ContractAccountCorrespondence.MessageRel

private theorem slot_available {slots : List EffectSlot}
    (signature : RuntimeEffectsFrameCorrespondence.slotTypes slots = Effects.slots ++ Effects.codeSlots)
    {name : String} {type : Core.Ty} (present : (name, type) ∈ Effects.slots ++ Effects.codeSlots) :
    ∃ location, ⟨name, type, location⟩ ∈ slots := by
  rw [← signature] at present
  obtain ⟨slot, member, same⟩ := List.mem_map.mp present
  rcases slot with ⟨actualName, actualType, location⟩
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj same
  exact ⟨location, member⟩

private theorem base_inputs (operation : EnvironmentSemantics.Operation) :
    (∀ input ∈ EnvironmentBuiltinCorrespondence.inputs operation, input ∈ Effects.slots) ↔
      operation ≠ .codeSize := by
  cases operation <;> (try first | cases ‹EnvironmentSemantics.Direct› | cases ‹EnvironmentSemantics.AmbientWord›)
  all_goals simp [EnvironmentBuiltinCorrespondence.inputs, EnvironmentSemantics.Direct.slot,
    EnvironmentSemantics.Direct.name, EnvironmentSemantics.AmbientWord.name, Effects.slots, Ambient.slots,
    EnvironmentBuiltinCorrespondence.optionalWord, EnvironmentBuiltinCorrespondence.optionalHashes,
    Ambient.optionalWord, Ambient.optionalHashes]

theorem environment_available {slots : List EffectSlot}
    (signature : RuntimeEffectsFrameCorrespondence.slotTypes slots = Effects.slots ++ Effects.codeSlots)
    (operation : EnvironmentSemantics.Operation) : EnvironmentBuiltinCorrespondence.Available slots operation := by
  have included : ∀ input ∈ EnvironmentBuiltinCorrespondence.inputs operation,
      input ∈ Effects.slots ++ Effects.codeSlots := by
    cases operation <;> (try first | cases ‹EnvironmentSemantics.Direct› | cases ‹EnvironmentSemantics.AmbientWord›)
    all_goals simp [EnvironmentBuiltinCorrespondence.inputs, EnvironmentSemantics.Direct.slot,
      EnvironmentSemantics.Direct.name, EnvironmentSemantics.AmbientWord.name, Effects.slots, Effects.codeSlots,
      Ambient.slots, EnvironmentBuiltinCorrespondence.optionalWord, EnvironmentBuiltinCorrespondence.optionalHashes,
      Ambient.optionalWord, Ambient.optionalHashes]
  intro name type member
  exact slot_available signature (included (name, type) member)

private theorem environment_supported {slots : List EffectSlot}
    (signature : RuntimeEffectsFrameCorrespondence.slotTypes slots = Effects.slots ++ Effects.codeSlots)
    (name : String) : RuntimeEnvironmentEffectsCorrespondence.supported slots name ↔
      ContractEnvironmentCorrespondence.supported name ∨ name = "codesize" := by
  constructor
  · rintro (runtime | ⟨operation, named, _⟩)
    · exact .inl (.inl runtime)
    · by_cases codeSize : operation = .codeSize
      · subst operation
        exact .inr named.symm
      · exact .inl (.inr ⟨operation, named, (base_inputs operation).mpr codeSize⟩)
  · rintro ((runtime | ⟨operation, named, _⟩) | rfl)
    · exact .inl runtime
    · exact .inr ⟨operation, named, environment_available signature operation⟩
    · exact .inr ⟨.codeSize, rfl, environment_available signature .codeSize⟩

private theorem copy_available {slots : List EffectSlot}
    (signature : RuntimeEffectsFrameCorrespondence.slotTypes slots = Effects.slots ++ Effects.codeSlots)
    (operation : MemoryCopySemantics.Operation) : RuntimeCopyEffectsCorrespondence.Available slots operation := by
  intro _
  exact slot_available signature (by simp [Effects.slots])

theorem supported_actual {slots : List EffectSlot}
    (signature : RuntimeEffectsFrameCorrespondence.slotTypes slots = Effects.slots ++ Effects.codeSlots) :
    RuntimeCodeEffectsCorrespondence.supported slots = supported := by
  funext name
  apply propext
  simp only [RuntimeCodeEffectsCorrespondence.supported, RuntimeAccountEffectsCorrespondence.supported,
    RuntimeHashEffectsCorrespondence.supported, RuntimeCopyEffectsCorrespondence.supported,
    RuntimeFullEffectsCorrespondence.supported, RuntimeLogEffectsCorrespondence.supported,
    environment_supported signature name, copy_available signature, and_true, supported,
    ContractAccountCorrespondence.supported, ContractHashCorrespondence.supported,
    ContractCopyCorrespondence.supported, ContractFullCorrespondence.supported, ContractLogCorrespondence.supported]
  simp only [or_assoc, or_left_comm, or_comm]

theorem frameCall_message_evaluates {program : Program} {code : CodeBlock} {slots : List EffectSlot}
    {fuel : Nat} {compiled : Core.Expr}
    (accepted : AccountRuntime.compileFrame program code (RuntimeLogEffectsFrameCorrespondence.slotTypes slots) fuel = .ok compiled)
    (eligible : DerivationCorrespondence.ExecutableProgram (RuntimeCodeEffectsCorrespondence.supported slots)
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code]))
    {layout : RuntimeCodeEffectsCorrespondence.Layout} {image : Option (List UInt8)}
    {initial : RuntimeCodeEffectsSemantics.State}
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
    (codeMember : ⟨"code", Core.WordMapping.type, layout.code⟩ ∈ slots)
    (knownMember : ⟨"codeKnown", .bool, layout.known⟩ ∈ slots)
    (initialRelated : StateRel (RuntimeCodeEffectsCorrespondence.model layout (prefixRead layout.boundary store) slots image) [] ⟨[], initial⟩ store)
    (passive : RuntimeLogEffectsCorrespondence.Passive layout.toLogLayout slots)
    {final : Semantics.State RuntimeCodeEffectsSemantics.State} {result : Semantics.Result Semantics.Value}
    (evaluated : Semantics.EvalFunction
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code]) (RuntimeCodeEffectsSemantics.effects image)
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
    RuntimeCodeEffectsFrameCorrespondence.compileFrame_call_preserves_observed accepted eligible closureRelated resolved supplied length
      runtime separated memoryMember worldMember addressMember completeMember staticMember memorySizeMember exitMember offsetMember sizeMember
      logsMember logSizeMember balancesMember codeMember knownMember initialRelated passive evaluated
  have balancesFinal := RuntimeAccountEffectsCorrespondence.balances_related (RuntimeCodeEffectsCorrespondence.account_related related)
  let frameResult := frameCompletionValue status (ContractLogCorrespondence.snapshotValues final.external.runtime accounts final.external.balances)
    (StorageCorrespondence.get accounts final.external.runtime.runtime.runtime.storage.address final.external.runtime.runtime.runtime.storage.complete)
  obtain ⟨finalStore, completed⟩ := ContractLogCorrespondence.message_evaluates result final.external.runtime accounts address final.external.balances
    statusRelated (worldReference.prepend [frameResult]) (balancesReference.prepend [frameResult])
    (targetValue.prepend [frameResult]) (deployingValue.prepend [frameResult])
    (CodeValue.bound depth environment frameResult) worldFinal balancesFinal
  exact ⟨_, finalStore, .letE executed completed, accounts, represented, rfl⟩

end Solcore.Frontend.RustHull.ContractCodeCorrespondence
