import Solcore.Frontend.RustHull.ReturnDataSemantics
import Solcore.Frontend.RustHull.MemoryCopyBuiltinCorrespondence
import Solcore.Frontend.RustHull.TerminationBuiltinCorrespondence

/-! The actual return-data source guards preserve their order before copying.
Both invalid-source branches use the existing termination proof, while a valid
source reaches packed copying and retains unrelated cells and closures. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.ReturnDataBuiltinCorrespondence
open Core Correspondence PureCallCorrespondence EffectBuiltinCorrespondence

private theorem inner_arity {scope : Scope} {arguments : List Core.Expr} {lowered : Lowered}
    (compiled : Effects.lowerBuiltin scope "returndatacopy" arguments = .ok lowered) :
    arguments.length = 3 := by
  rcases arguments with _ | ⟨first, _ | ⟨second, _ | ⟨third, _ | ⟨fourth, rest⟩⟩⟩⟩
  all_goals first
    | rfl
    | change Except.error _ = Except.ok lowered at compiled
      cases compiled

private theorem components {scope : Scope} {destination source length : Core.Expr} {lowered : Lowered}
    (compiled : Effects.lowerBuiltin scope "returndatacopy" [destination, source, length] = .ok lowered) :
    ∃ dataSize invalid memory size data,
      Effects.reference scope "returnDataSize" .word = .ok dataSize ∧
      Effects.terminate scope 3 (.word Word.zero) (.word Word.zero) = .ok invalid ∧
      Effects.reference scope "memory" WordMapping.type = .ok memory ∧
      Effects.reference scope "memorySize" .word = .ok size ∧
      Effects.reference scope "returnData" WordMapping.type = .ok data ∧
      lowered = ⟨.unit, .ifE (.binary .wordGt source (.loadCell dataSize)) invalid
        (.ifE (.binary .wordGt length (.binary .wordSub (.loadCell dataSize) source)) invalid
          (Memory.copyPackedFrom memory size destination (.loadCell data) source length))⟩ := by
  have expanded : (do
      let raw ← (do
        let dataSize ← Effects.reference scope "returnDataSize" .word
        let invalid ← Effects.terminate scope 3 (.word Word.zero) (.word Word.zero)
        let memory ← Effects.reference scope "memory" WordMapping.type
        let size ← Effects.reference scope "memorySize" .word
        let data ← Effects.reference scope "returnData" WordMapping.type
        pure (Lowered.mk .unit (.ifE (.binary .wordGt source (.loadCell dataSize)) invalid
          (.ifE (.binary .wordGt length (.binary .wordSub (.loadCell dataSize) source)) invalid
            (Memory.copyPackedFrom memory size destination (.loadCell data) source length)))) : LowerM Lowered)
      pure raw) = .ok lowered := compiled
  obtain ⟨dataSize, dataSizeCompiled, expanded⟩ := lower_bind_eq_ok.mp expanded
  obtain ⟨invalid, invalidCompiled, expanded⟩ := lower_bind_eq_ok.mp expanded
  obtain ⟨memory, memoryCompiled, expanded⟩ := lower_bind_eq_ok.mp expanded
  obtain ⟨size, sizeCompiled, expanded⟩ := lower_bind_eq_ok.mp expanded
  obtain ⟨data, dataCompiled, returned⟩ := lower_bind_eq_ok.mp expanded
  exact ⟨dataSize, invalid, memory, size, data, dataSizeCompiled, invalidCompiled,
    memoryCompiled, sizeCompiled, dataCompiled, (Except.ok.inj returned).symm⟩

theorem preserves {scope : Scope} {expected : Core.Ty} {arguments : List Lowered} {lowered : Lowered}
    (compiled : lowerBuiltin scope "returndatacopy" expected arguments = .ok lowered)
    {entries : MemorySemantics.Entries} {dataSize : Word} {sourceType : Ty} {sources : List Semantics.Value}
    {state finalState : RuntimeEffectsSemantics.State} {result : Semantics.Result Semantics.Value}
    (called : ReturnDataSemantics.Builtin entries dataSize "returndatacopy" sourceType sources state result finalState)
    {targets : List Core.Value} (related : ArgumentsRel arguments sources targets)
    {slots : List EffectSlot} {mapping : Renaming} {environment : Environment}
    {initial store : Store} {layout : RuntimeEffectsCorrespondence.Layout} {dataLocation dataSizeLocation : Nat}
    (runtime : EffectEnvironmentRel slots scope mapping environment)
    (memoryMember : ⟨"memory", WordMapping.type, layout.memory⟩ ∈ slots)
    (memorySizeMember : ⟨"memorySize", .word, layout.storage.memorySize⟩ ∈ slots)
    (exitMember : ⟨"exit", .word, layout.storage.exit⟩ ∈ slots)
    (offsetMember : ⟨"returnOffset", .word, layout.storage.returnOffset⟩ ∈ slots)
    (sizeMember : ⟨"returnSize", .word, layout.storage.returnSize⟩ ∈ slots)
    (dataMember : ⟨"returnData", WordMapping.type, dataLocation⟩ ∈ slots)
    (dataSizeMember : ⟨"returnDataSize", .word, dataSizeLocation⟩ ∈ slots)
    (dataRead : store.read? dataLocation = some (WordMapping.encode entries))
    (dataSizeRead : store.read? dataSizeLocation = some (.word dataSize))
    (memory : MemoryCorrespondence.StateRel layout.memory layout.storage.memorySize state.memory store)
    (storage : StorageBuiltinCorrespondence.StateRel layout.storage state.storage store)
    (packed : Evaluates environment initial ((packArguments arguments).expression.rename mapping)
      (.inRight .word (ScalarExecution.bundleValues targets)) store) :
    ∃ target final,
      ResultRel lowered.type result target ∧
      Evaluates environment initial (lowered.expression.rename mapping) target final ∧
      MemoryCorrespondence.StateRel layout.memory layout.storage.memorySize finalState.memory final ∧
      StorageBuiltinCorrespondence.StateRel layout.storage finalState.storage final ∧
      RuntimeEffectsCorrespondence.Frame layout store final ∧ ClosuresPreserved store final := by
  obtain ⟨words, raw, rawCompiled, typed, loweredEqual⟩ := outer_components (by rfl) compiled
  have arity : arguments.length = 3 := by
    simpa only [List.length_map, List.length_range] using inner_arity rawCompiled
  obtain ⟨destinationExpr, sourceExpr, lengthExpr, destination, source, length, rfl, rfl, rfl⟩ :=
    MemoryCopyBuiltinCorrespondence.three_words related words arity
  obtain ⟨dataSizeRef, invalid, memoryRef, sizeRef, dataRef,
    dataSizeCompiled, invalidCompiled, memoryCompiled, sizeCompiled, dataCompiled, rfl⟩ := components rawCompiled
  cases typed
  cases loweredEqual
  let input := Value.pair (.word destination) (.pair (.word source) (.word length))
  let inputType := Core.Ty.product .word (.product .word .word)
  have runtime' := runtime.temporary inputType input
  have terminated := TerminationBuiltinCorrespondence.terminate_evaluates invalidCompiled runtime'
    memorySizeMember exitMember offsetMember sizeMember storage memory.size Word.zero Word.zero
    (fun _ _ => .word) (fun _ _ => .word)
  have terminatedState := TerminationBuiltinCorrespondence.terminate_state memory storage 3 Word.zero Word.zero
  have terminatedClosures : ClosuresPreserved store
      (TerminationBuiltinCorrespondence.finalStore layout.storage state 3 Word.zero Word.zero store) :=
    TerminationBuiltinCorrespondence.terminate_closures memory storage 3 Word.zero Word.zero
  have sourceEvaluated : Evaluates (input :: environment) store
      ((projectArgument 1 3 (.var 0)).rename mapping.lift) (.word source) store :=
    .first (.second (.var rfl))
  have lengthEvaluated : Evaluates (input :: environment) store
      ((projectArgument 2 3 (.var 0)).rename mapping.lift) (.word length) store :=
    .second (.second (.var rfl))
  have dataSizeEvaluated := Evaluates.loadCell (reference_evaluates runtime' dataSizeMember dataSizeCompiled store) dataSizeRead
  cases called with
  | copy executed =>
      cases executed with
      | sourceOverflow invalidSource =>
          obtain ⟨resultRelated, memoryFinal, storageFinal, frame⟩ := terminatedState
          refine ⟨_, _, resultRelated, ?_, memoryFinal, storageFinal, frame, terminatedClosures⟩
          apply LanguageResult.bind_success .unit packed
          exact .ifTrue (.binary sourceEvaluated dataSizeEvaluated (by simp [BinaryOp.apply, invalidSource])) terminated
      | lengthOverflow validSource invalidLength =>
          obtain ⟨resultRelated, memoryFinal, storageFinal, frame⟩ := terminatedState
          refine ⟨_, _, resultRelated, ?_, memoryFinal, storageFinal, frame, terminatedClosures⟩
          apply LanguageResult.bind_success .unit packed
          apply Evaluates.ifFalse (.binary sourceEvaluated dataSizeEvaluated (by simp [BinaryOp.apply, validSource]))
          exact .ifTrue (.binary lengthEvaluated (.binary dataSizeEvaluated sourceEvaluated rfl)
            (by simp [BinaryOp.apply, invalidLength])) terminated
      | copied validSource validLength executed =>
          obtain ⟨target, final, resultRelated, evaluated, finalRelated, frame⟩ :=
            MemoryCopyCorrespondence.copyPackedFrom_preserves executed memory
              (reference_evaluates runtime' memoryMember memoryCompiled store)
              (reference_evaluates runtime' memorySizeMember sizeCompiled store)
              (.first (.var (index := 0) rfl))
              (.loadCell (reference_evaluates runtime' dataMember dataCompiled store) dataRead)
              sourceEvaluated lengthEvaluated
          refine ⟨target, final, resultRelated, ?_, finalRelated,
            RuntimeEffectsCorrespondence.memory_preserves_storage storage frame,
            RuntimeEffectsCorrespondence.Frame.of_memory frame,
            MemoryEffectCorrespondence.closures_preserved memory frame⟩
          apply LanguageResult.bind_success .unit packed
          apply Evaluates.ifFalse (.binary sourceEvaluated dataSizeEvaluated (by simp [BinaryOp.apply, validSource]))
          apply Evaluates.ifFalse (.binary lengthEvaluated (.binary dataSizeEvaluated sourceEvaluated rfl)
            (by simp [BinaryOp.apply, validLength]))
          rw [MemoryCopyCorrespondence.copyPackedFrom_rename]
          exact evaluated

end Solcore.Frontend.RustHull.ReturnDataBuiltinCorrespondence
