import Solcore.Frontend.RustHull.YulLowering
import Solcore.Frontend.RustHull.LoweringSafety
import Solcore.Frontend.RustHull.LiteralCorrespondence
import Solcore.Frontend.RustHull.YulSemantics
import Solcore.Frontend.RustHull.RevertBuiltinCorrespondence

/-! The connected inline Yul fragment through the actual
`YulLowering.lowerStatements` code. The lowering of a one-call block binds the
two literal words from right to left and runs the actual builtin code over
them; the memory writes and terminations match `YulSemantics` in the frame
model, and catalog links and the captured context survive. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.YulBuiltinCorrespondence
open Core Correspondence ScalarExecution EffectBuiltinCorrespondence
open RuntimeCallEffectsCorrespondence (Layout Handlers account_related runtime_related)
open RuntimeChildCallEffectsCorrespondence

/-- The accepted lowering of a one-call block: both literal words, the actual
builtin code over two pushed word temporaries, and the right-to-left argument
binds. -/
theorem call_components {fuel : Nat} {scope : Scope} {resultType : Core.Ty} {signatures : List Signature}
    {name : String} {nameSpan callSpan statementSpan firstSpan secondSpan : Option Span} {first second : YulLit}
    {expression : Core.Expr}
    (reservedFree : name.startsWith Effects.reservedPrefix = false)
    (notUser : name.startsWith "usr$" = false) (builtin : Effects.supports name = true)
    (compiled : YulLowering.lowerStatements fuel scope resultType
      [⟨.expression ⟨.call ⟨name, nameSpan⟩ [⟨.literal first, firstSpan⟩, ⟨.literal second, secondSpan⟩],
        callSpan⟩, statementSpan⟩] signatures = .ok expression) :
    ∃ firstWord secondWord effect, YulLowering.literalWord first = .ok firstWord ∧
      YulLowering.literalWord second = .ok secondWord ∧
      Effects.lowerBuiltin ((scope.temporary .word).temporary .word) name [.var 0, .var 1] = .ok effect ∧
      effect.type = .unit ∧
      expression = LocalSequence.discard (LocalLoop.controlType resultType)
        (LanguageResult.bind .unit (LanguageResult.success (.word secondWord))
          (LanguageResult.bind .unit (LanguageResult.success (.word firstWord)) effect.expression))
        (LocalLoop.fallthrough resultType) := by
  rcases fuel with _ | _ | _ | _ | fuel
  all_goals try (change Except.error _ = _ at compiled; cases compiled; done)
  all_goals
    unfold YulLowering.lowerStatements at compiled
    obtain ⟨_, _, compiled⟩ := lower_bind_eq_ok.mp compiled
    change Except.bind _ _ = _ at compiled
    obtain ⟨body, sequenced, compiled⟩ := lower_bind_eq_ok.mp compiled
    change Except.bind _ _ = _ at sequenced
    obtain ⟨call, called, sequenced⟩ := lower_bind_eq_ok.mp sequenced
    change (if name.startsWith Effects.reservedPrefix = true then _ else _) = _ at called
    rw [if_neg (by simp [reservedFree])] at called
  · change Except.error _ = _ at called
    cases called
  change Except.bind _ _ = _ at called
  obtain ⟨arguments, argumentsLowered, called⟩ := lower_bind_eq_ok.mp called
  change Except.bind _ _ = _ at argumentsLowered
  obtain ⟨firstLowered, firstCompiled, argumentsLowered⟩ := lower_bind_eq_ok.mp argumentsLowered
  change Except.bind _ _ = _ at firstCompiled
  obtain ⟨firstWord, firstParsed, firstCompiled⟩ := lower_bind_eq_ok.mp firstCompiled
  cases firstCompiled
  change Except.bind _ _ = _ at argumentsLowered
  obtain ⟨secondLowered, secondCompiled, argumentsLowered⟩ := lower_bind_eq_ok.mp argumentsLowered
  change Except.bind _ _ = _ at secondCompiled
  obtain ⟨secondWord, secondParsed, secondCompiled⟩ := lower_bind_eq_ok.mp secondCompiled
  cases secondCompiled
  cases argumentsLowered
  change (if name.startsWith "usr$" = true then _ else _) = _ at called
  rw [if_neg (by simp [notUser])] at called
  change (if (signatures.any fun signature => signature.name == name) = true then _ else _) = _ at called
  split at called
  · cases called
  change Except.bind (Effects.lowerBuiltin _ _ _) _ = _ at called
  obtain ⟨effect, effectCompiled, called⟩ := lower_bind_eq_ok.mp called
  cases called
  change Effects.lowerBuiltin ((scope.temporary .word).temporary .word) name [.var 0, .var 1] = .ok effect
    at effectCompiled
  change Except.bind _ _ = _ at sequenced
  obtain ⟨_, typed, sequenced⟩ := lower_bind_eq_ok.mp sequenced
  have unitType : effect.type = .unit := (expectType_eq_of_ok typed).symm
  change Except.ok (LocalSequence.discard (LocalLoop.controlType resultType)
    (LanguageResult.bind effect.type (LanguageResult.success (.word secondWord))
      (LanguageResult.bind effect.type (LanguageResult.success (.word firstWord)) effect.expression))
    (LocalLoop.fallthrough resultType)) = Except.ok body at sequenced
  change Except.ok body = Except.ok expression at compiled
  refine ⟨firstWord, secondWord, effect, firstParsed, secondParsed, effectCompiled, unitType, ?_⟩
  rw [← Except.ok.inj compiled, ← Except.ok.inj sequenced, unitType]

theorem literal_word {literal : YulLit} {lowered source : Word}
    (compiled : YulLowering.literalWord literal = .ok lowered)
    (evaluated : YulSemantics.literalWord? literal = some source) : lowered = source := by
  cases literal with
  | number text | hex text =>
      have parsed := Correspondence.parseWord_some_of_ok compiled
      exact Option.some.inj (parsed.symm.trans evaluated)
  | bool value =>
      exact (Except.ok.inj compiled).symm.trans (Option.some.inj evaluated)
  | string text => cases evaluated

theorem mstore8_components {scope : Scope} {offset value : Core.Expr} {lowered : Lowered}
    (compiled : Effects.lowerBuiltin scope "mstore8" [offset, value] = .ok lowered) :
    ∃ memory size, Effects.reference scope "memory" WordMapping.type = .ok memory ∧
      Effects.reference scope "memorySize" .word = .ok size ∧
      lowered = ⟨.unit, Memory.mstore8 memory size offset value⟩ := by
  change (do
    let raw ← (do
      let memory ← Effects.reference scope "memory" WordMapping.type
      let size ← Effects.reference scope "memorySize" .word
      pure (Lowered.mk .unit (Memory.mstore8 memory size offset value)) : LowerM Lowered)
    pure raw) = .ok lowered at compiled
  obtain ⟨memory, memoryCompiled, compiled⟩ := lower_bind_eq_ok.mp compiled
  obtain ⟨size, sizeCompiled, returned⟩ := lower_bind_eq_ok.mp compiled
  exact ⟨memory, size, memoryCompiled, sizeCompiled, (Except.ok.inj returned).symm⟩

theorem terminate_components {scope : Scope} {name : String} {kind : Nat} {offset length : Core.Expr}
    {lowered : Lowered} (named : name = "return" ∧ kind = 1 ∨ name = "revert" ∧ kind = 2)
    (compiled : Effects.lowerBuiltin scope name [offset, length] = .ok lowered) :
    ∃ expression, Effects.terminate scope kind offset length = .ok expression ∧ lowered = ⟨.unit, expression⟩ := by
  have expanded : Effects.lowerBuiltin scope name [offset, length] = (do
      let raw ← (do
        let expression ← Effects.terminate scope kind offset length
        pure (Lowered.mk .unit expression) : LowerM Lowered)
      pure raw) := by
    rcases named with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rfl
  rw [expanded] at compiled
  obtain ⟨expression, terminated, returned⟩ := lower_bind_eq_ok.mp compiled
  exact ⟨expression, terminated, (Except.ok.inj returned).symm⟩

theorem arguments_evaluate {environment : Environment} {store final : Store} {mapping : Renaming}
    {first second : Word} {code : Core.Expr} {result : Value}
    (evaluated : Evaluates (.word first :: .word second :: environment) store (code.rename mapping.lift.lift)
      result final) :
    Evaluates environment store ((LanguageResult.bind .unit (LanguageResult.success (.word second))
      (LanguageResult.bind .unit (LanguageResult.success (.word first)) code)).rename mapping) result final :=
  LanguageResult.bind_success .unit (.inRight .word) (LanguageResult.bind_success .unit (.inRight .word) evaluated)

/-- A returning builtin continues the block and a fault stops it. -/
theorem statement_result {environment : Environment} {store final : Store} {mapping : Renaming}
    {resultType : Core.Ty} {call : Core.Expr} {source : Semantics.Result Semantics.Value} {target : Value}
    (related : ResultRel .unit source target)
    (evaluated : Evaluates environment store (call.rename mapping) target final) :
    ∃ targetValue, StatementCorrespondence.ControlRel resultType (YulSemantics.control source) targetValue ∧
      Evaluates environment store
        ((LocalSequence.discard (LocalLoop.controlType resultType) call (LocalLoop.fallthrough resultType)).rename mapping)
        targetValue final := by
  cases related with
  | value related =>
      cases related
      exact ⟨_, .fallthrough, LanguageResult.bind_success _ evaluated
        (by simpa only [LocalLoop.weaken_zero, LocalLoop.fallthrough_rename] using LocalLoop.fallthrough_evaluates _ _ _)⟩
  | language reason =>
      exact ⟨_, .language reason, LanguageResult.bind_failure _ evaluated⟩

theorem stable_first (first second : Word) (environment : Environment) (mapping : Renaming) :
    TerminationBuiltinCorrespondence.StableWord (.word first :: .word second :: environment) mapping.lift.lift
      (.var 0) first := by
  intro extra store
  apply Evaluates.var
  simp [Renaming.lift]

theorem stable_second (first second : Word) (environment : Environment) (mapping : Renaming) :
    TerminationBuiltinCorrespondence.StableWord (.word first :: .word second :: environment) mapping.lift.lift
      (.var 1) second := by
  intro extra store
  apply Evaluates.var
  simp [Renaming.lift]

section
variable {slots : List EffectSlot} {mapping : Renaming} {environment : Environment} {store : Store}
variable {layout : Layout} {baseline : Nat → Option Value} {image : Option (List UInt8)}
variable {handlers : Handlers layout} {anchors : Anchors} {context : Context layout} {world : World}
variable {state : Semantics.State RuntimeCallEffectsSemantics.State}

/-- A memory write of the fragment publishes the frame's new memory; the world
cell and source world are unchanged. -/
private theorem memory_related (passive : RuntimeLogEffectsCorrespondence.Passive layout.toLogLayout slots)
    (stateRelated : StateRel (model layout baseline slots image handlers anchors context) world state store)
    {memory : MemorySemantics.State} {final : Store}
    (memoryFinal : MemoryCorrespondence.StateRel layout.memory layout.storage.memorySize memory final)
    (frame : MemoryCorrespondence.Frame layout.memory layout.storage.memorySize store final) :
    StateRel (model layout baseline slots image handlers anchors context) world
      {state with external := {state.external with runtime := (RuntimeReturnDataEffectsSemantics.withRuntime
        state.external.runtime {state.external.runtime.runtime.runtime.runtime.runtime with memory := memory})}}
      final := by
  have base := base_related stateRelated
  have beforeRuntime := RuntimeEnvironmentEffectsCorrespondence.runtime_related
    (RuntimeLogEffectsCorrespondence.runtime_related (RuntimeAccountEffectsCorrespondence.runtime_related (account_related base)))
  have storageBefore : StorageBuiltinCorrespondence.StateRel layout.storage
      state.external.runtime.runtime.runtime.runtime.runtime.storage store :=
    RuntimeEffectsCorrespondence.storage_related beforeRuntime
  have returnDataFinal := RuntimeReturnDataEffectsCorrespondence.runtime_updated passive (runtime_related base)
    (runtime := {state.external.runtime.runtime.runtime.runtime.runtime with memory := memory}) memoryFinal
    (RuntimeEffectsCorrespondence.memory_preserves_storage storageBefore frame)
    (RuntimeEffectsCorrespondence.Frame.of_memory (layout := layout.toLayout) frame)
  have finalRelated := RuntimeCallEffectsCorrespondence.runtime_updated base returnDataFinal rfl
  obtain ⟨notMemory, notSize, _⟩ := RevertBuiltinCorrespondence.world_separate layout.toLayout
  exact of_base finalRelated
    ((linked_related stateRelated).read_preserved (fun value found => frame.read _ value notMemory notSize found))
    (context.updated base finalRelated stateRelated.external.2.2.1.2)

/-- A termination of the fragment publishes the exit registers and memory
size; the world cell and source world are unchanged. -/
private theorem terminated_related (passive : RuntimeLogEffectsCorrespondence.Passive layout.toLogLayout slots)
    (stateRelated : StateRel (model layout baseline slots image handlers anchors context) world state store)
    (kind : Nat) (offset length : Word) :
    StateRel (model layout baseline slots image handlers anchors context) world
      {state with external := {state.external with runtime := (RuntimeReturnDataEffectsSemantics.withRuntime
        state.external.runtime (TerminationSemantics.terminate state.external.runtime.runtime.runtime.runtime.runtime
          kind offset length).2)}}
      (TerminationBuiltinCorrespondence.finalStore layout.storage state.external.runtime.runtime.runtime.runtime.runtime
        kind offset length store) := by
  have base := base_related stateRelated
  have beforeRuntime := RuntimeEnvironmentEffectsCorrespondence.runtime_related
    (RuntimeLogEffectsCorrespondence.runtime_related (RuntimeAccountEffectsCorrespondence.runtime_related (account_related base)))
  have memoryBefore : MemoryCorrespondence.StateRel layout.memory layout.storage.memorySize
      state.external.runtime.runtime.runtime.runtime.runtime.memory store :=
    RuntimeEffectsCorrespondence.memory_related beforeRuntime
  have storageBefore : StorageBuiltinCorrespondence.StateRel layout.storage
      state.external.runtime.runtime.runtime.runtime.runtime.storage store :=
    RuntimeEffectsCorrespondence.storage_related beforeRuntime
  obtain ⟨_, memoryFinal, storageFinal, haltFrame⟩ :=
    TerminationBuiltinCorrespondence.terminate_state memoryBefore storageBefore kind offset length
  have returnDataFinal := RuntimeReturnDataEffectsCorrespondence.runtime_updated passive (runtime_related base)
    memoryFinal storageFinal haltFrame
  have finalRelated := RuntimeCallEffectsCorrespondence.runtime_updated base returnDataFinal rfl
  have sameWorld : (TerminationSemantics.terminate state.external.runtime.runtime.runtime.runtime.runtime
      kind offset length).2.storage.world = state.external.runtime.runtime.runtime.runtime.runtime.storage.world := by
    unfold TerminationSemantics.terminate
    split <;> rfl
  have linked : RuntimeLinkedWorldCorrespondence.StateRel anchors
      (sourceWorld {state.external with runtime := (RuntimeReturnDataEffectsSemantics.withRuntime state.external.runtime
        (TerminationSemantics.terminate state.external.runtime.runtime.runtime.runtime.runtime kind offset length).2)})
      layout.storage.world
      (TerminationBuiltinCorrespondence.finalStore layout.storage state.external.runtime.runtime.runtime.runtime.runtime
        kind offset length store) := by
    change RuntimeLinkedWorldCorrespondence.StateRel anchors
      (TerminationSemantics.terminate state.external.runtime.runtime.runtime.runtime.runtime kind offset length).2.storage.world
      layout.storage.world _
    rw [sameWorld]
    exact (linked_related stateRelated).read_preserved
      (fun value found => RevertBuiltinCorrespondence.finalStore_world (layout := layout.toLayout) found)
  exact of_base finalRelated linked (context.updated base finalRelated stateRelated.external.2.2.1.2)

/-- The fragment's block simulates its actual lowering in the frame model. -/
theorem preserves (passive : RuntimeLogEffectsCorrespondence.Passive layout.toLogLayout slots)
    (memoryMember : ⟨"memory", WordMapping.type, layout.memory⟩ ∈ slots)
    (memorySizeMember : ⟨"memorySize", .word, layout.storage.memorySize⟩ ∈ slots)
    (exitMember : ⟨"exit", .word, layout.storage.exit⟩ ∈ slots)
    (offsetMember : ⟨"returnOffset", .word, layout.storage.returnOffset⟩ ∈ slots)
    (sizeMember : ⟨"returnSize", .word, layout.storage.returnSize⟩ ∈ slots)
    {body : List YulStmt} {control : Semantics.Control} {final : RuntimeCallEffectsSemantics.State}
    (executed : YulSemantics.Executed body state.external control final)
    {fuel : Nat} {scope : Scope} {resultType : Core.Ty} {signatures : List Signature} {expression : Core.Expr}
    (compiled : YulLowering.lowerStatements fuel scope resultType body signatures = .ok expression)
    (runtime : EffectEnvironmentRel slots scope mapping environment)
    (stateRelated : StateRel (model layout baseline slots image handlers anchors context) world state store) :
    ∃ targetValue finalStore, StatementCorrespondence.ControlRel resultType control targetValue ∧
      Evaluates environment store (expression.rename mapping) targetValue finalStore ∧
      StateRel (model layout baseline slots image handlers anchors context) world {state with external := final}
        finalStore ∧
      ClosuresPreserved store finalStore := by
  cases executed with
  | call secondEvaluated firstEvaluated computed =>
  rename_i name first second firstSpan secondSpan callSpan statementSpan firstWord secondWord result frame
  obtain ⟨nameText, nameSpan⟩ := name
  have base := base_related stateRelated
  have beforeRuntime := RuntimeEnvironmentEffectsCorrespondence.runtime_related
    (RuntimeLogEffectsCorrespondence.runtime_related (RuntimeAccountEffectsCorrespondence.runtime_related (account_related base)))
  have memoryBefore : MemoryCorrespondence.StateRel layout.memory layout.storage.memorySize
      state.external.runtime.runtime.runtime.runtime.runtime.memory store :=
    RuntimeEffectsCorrespondence.memory_related beforeRuntime
  have storageBefore : StorageBuiltinCorrespondence.StateRel layout.storage
      state.external.runtime.runtime.runtime.runtime.runtime.storage store :=
    RuntimeEffectsCorrespondence.storage_related beforeRuntime
  have inner := (runtime.temporary .word (.word secondWord)).temporary .word (.word firstWord)
  cases computed with
  | mstore =>
      obtain ⟨firstLowered, secondLowered, effect, firstCompiled, secondCompiled, effectCompiled, _, rfl⟩ :=
        call_components (by decide +kernel) (by decide +kernel) (by decide +kernel) compiled
      cases literal_word firstCompiled firstEvaluated
      cases literal_word secondCompiled secondEvaluated
      obtain ⟨memoryReference, sizeReference, memoryCompiled, sizeCompiled, rfl⟩ :=
        RevertBuiltinCorrespondence.store_components effectCompiled
      obtain ⟨storedResult, memoryStored, storedFrame⟩ := MemoryCorrespondence.mstore_preserves memoryBefore
        firstWord secondWord (.word firstWord :: .word secondWord :: environment)
      have stored : Evaluates (.word firstWord :: .word secondWord :: environment) store
          ((Memory.mstore memoryReference sizeReference (.var 0) (.var 1)).rename mapping.lift.lift)
          (MemoryCorrespondence.mstoreResult state.external.runtime.runtime.runtime.runtime.runtime.memory firstWord)
          (MemoryCorrespondence.mstoreStore store layout.memory layout.storage.memorySize
            state.external.runtime.runtime.runtime.runtime.runtime.memory firstWord secondWord
            (.word firstWord :: .word secondWord :: environment)) := by
        rw [MemoryCorrespondence.mstore_rename]
        exact MemoryCorrespondence.mstore_evaluates _ firstWord secondWord
          (reference_evaluates inner memoryMember memoryCompiled store)
          (reference_evaluates inner memorySizeMember sizeCompiled store) (.var rfl) (.var rfl)
          memoryBefore.memory memoryBefore.size memoryBefore.distinct
      obtain ⟨targetValue, controlRelated, evaluated⟩ := statement_result (resultType := resultType)
        storedResult (arguments_evaluate stored)
      exact ⟨targetValue, _, controlRelated, evaluated, memory_related passive stateRelated memoryStored storedFrame,
        MemoryEffectCorrespondence.closures_preserved memoryBefore storedFrame⟩
  | mstore8 =>
      obtain ⟨firstLowered, secondLowered, effect, firstCompiled, secondCompiled, effectCompiled, _, rfl⟩ :=
        call_components (by decide +kernel) (by decide +kernel) (by decide +kernel) compiled
      cases literal_word firstCompiled firstEvaluated
      cases literal_word secondCompiled secondEvaluated
      obtain ⟨memoryReference, sizeReference, memoryCompiled, sizeCompiled, rfl⟩ := mstore8_components effectCompiled
      obtain ⟨storedResult, memoryStored, storedFrame⟩ := MemoryCorrespondence.mstore8_preserves memoryBefore
        firstWord secondWord (.word firstWord :: .word secondWord :: environment)
      have stored : Evaluates (.word firstWord :: .word secondWord :: environment) store
          ((Memory.mstore8 memoryReference sizeReference (.var 0) (.var 1)).rename mapping.lift.lift)
          (MemoryCorrespondence.mstore8Result state.external.runtime.runtime.runtime.runtime.runtime.memory firstWord)
          (MemoryCorrespondence.mstore8Store store layout.memory layout.storage.memorySize
            state.external.runtime.runtime.runtime.runtime.runtime.memory firstWord secondWord
            (.word firstWord :: .word secondWord :: environment)) := by
        rw [MemoryCorrespondence.mstore8_rename]
        exact MemoryCorrespondence.mstore8_evaluates _ firstWord secondWord
          (reference_evaluates inner memoryMember memoryCompiled store)
          (reference_evaluates inner memorySizeMember sizeCompiled store) (.var rfl) (.var rfl)
          memoryBefore.memory memoryBefore.size memoryBefore.distinct
      obtain ⟨targetValue, controlRelated, evaluated⟩ := statement_result (resultType := resultType)
        storedResult (arguments_evaluate stored)
      exact ⟨targetValue, _, controlRelated, evaluated, memory_related passive stateRelated memoryStored storedFrame,
        MemoryEffectCorrespondence.closures_preserved memoryBefore storedFrame⟩
  | returned =>
      obtain ⟨firstLowered, secondLowered, effect, firstCompiled, secondCompiled, effectCompiled, _, rfl⟩ :=
        call_components (by decide +kernel) (by decide +kernel) (by decide +kernel) compiled
      cases literal_word firstCompiled firstEvaluated
      cases literal_word secondCompiled secondEvaluated
      obtain ⟨halt, haltCompiled, rfl⟩ := terminate_components (.inl ⟨rfl, rfl⟩) effectCompiled
      have haltEvaluated := TerminationBuiltinCorrespondence.terminate_evaluates haltCompiled inner
        memorySizeMember exitMember offsetMember sizeMember storageBefore memoryBefore.size firstWord secondWord
        (stable_first firstWord secondWord environment mapping)
        (stable_second firstWord secondWord environment mapping)
      obtain ⟨haltResult, _, _, _⟩ :=
        TerminationBuiltinCorrespondence.terminate_state memoryBefore storageBefore 1 firstWord secondWord
      obtain ⟨targetValue, controlRelated, evaluated⟩ := statement_result (resultType := resultType)
        haltResult (arguments_evaluate haltEvaluated)
      exact ⟨targetValue, _, controlRelated, evaluated, terminated_related passive stateRelated 1 firstWord secondWord,
        TerminationBuiltinCorrespondence.terminate_closures memoryBefore storageBefore 1 firstWord secondWord⟩
  | reverted =>
      obtain ⟨firstLowered, secondLowered, effect, firstCompiled, secondCompiled, effectCompiled, _, rfl⟩ :=
        call_components (by decide +kernel) (by decide +kernel) (by decide +kernel) compiled
      cases literal_word firstCompiled firstEvaluated
      cases literal_word secondCompiled secondEvaluated
      obtain ⟨halt, haltCompiled, rfl⟩ := terminate_components (.inr ⟨rfl, rfl⟩) effectCompiled
      have haltEvaluated := TerminationBuiltinCorrespondence.terminate_evaluates haltCompiled inner
        memorySizeMember exitMember offsetMember sizeMember storageBefore memoryBefore.size firstWord secondWord
        (stable_first firstWord secondWord environment mapping)
        (stable_second firstWord secondWord environment mapping)
      obtain ⟨haltResult, _, _, _⟩ :=
        TerminationBuiltinCorrespondence.terminate_state memoryBefore storageBefore 2 firstWord secondWord
      obtain ⟨targetValue, controlRelated, evaluated⟩ := statement_result (resultType := resultType)
        haltResult (arguments_evaluate haltEvaluated)
      exact ⟨targetValue, _, controlRelated, evaluated, terminated_related passive stateRelated 2 firstWord secondWord,
        TerminationBuiltinCorrespondence.terminate_closures memoryBefore storageBefore 2 firstWord secondWord⟩

end

end Solcore.Frontend.RustHull.YulBuiltinCorrespondence
