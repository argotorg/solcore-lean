import Solcore.Frontend.RustHull.TerminationBuiltinCorrespondence
import Solcore.Frontend.RustHull.ReturnDataBuiltinCorrespondence

/-! Termination and return-data copying retain the exact encoded world,
including catalog identities hidden by the ordinary resource projection. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.ReadOnlyWorldBuiltinCorrespondence
open Core Correspondence PureCallCorrespondence EffectBuiltinCorrespondence ScalarExecution

namespace Termination
open TerminationSemantics TerminationBuiltinCorrespondence

theorem finalStore_world {locations : StorageBuiltinCorrespondence.Locations}
    {state : RuntimeEffectsSemantics.State} {store : Store}
    (storage : StorageBuiltinCorrespondence.StateRel locations state.storage store)
    (kind : Nat) (offset length : Word) :
    ∀ value, store.read? locations.world = some value →
      (finalStore locations state kind offset length store).read? locations.world = some value := by
  intro value read
  have distinct := storage.distinct
  simp [StorageBuiltinCorrespondence.Locations.all] at distinct
  unfold finalStore
  split
  · exact read
  · apply finishStore_other (by intro same; simp_all) (by intro same; simp_all) (by intro same; simp_all)
    exact (MemoryCorrespondence.touchStore_other store (by intro same; simp_all) _ _ _).trans read

private theorem inner_arity (operation : Operation) {scope : Scope}
    {arguments : List Core.Expr} {lowered : Lowered}
    (compiled : Effects.lowerBuiltin scope operation.name arguments = .ok lowered) :
    arguments.length = operation.arity := by
  cases operation <;>
    rcases arguments with _ | ⟨first, _ | ⟨second, _ | ⟨third, rest⟩⟩⟩
  all_goals first
    | rfl
    | change Except.error _ = Except.ok lowered at compiled
      cases compiled

private theorem zero_components (operation : Operation) (zero : operation.arity = 0)
    {scope : Scope} {lowered : Lowered}
    (compiled : Effects.lowerBuiltin scope operation.name [] = .ok lowered) :
    ∃ expression, Effects.terminate scope operation.kind (.word Word.zero) (.word Word.zero) = .ok expression ∧
      lowered = ⟨.unit, expression⟩ := by
  have expanded : Effects.lowerBuiltin scope operation.name [] = (do
      let raw ← (do
        let expression ← Effects.terminate scope operation.kind (.word Word.zero) (.word Word.zero)
        pure (Lowered.mk .unit expression) : LowerM Lowered)
      pure raw) := by
    cases operation <;> first | rfl | cases zero
  rw [expanded] at compiled
  obtain ⟨expression, terminated, returned⟩ := lower_bind_eq_ok.mp compiled
  exact ⟨expression, terminated, (Except.ok.inj returned).symm⟩

private theorem two_components (operation : Operation) (two : operation.arity = 2)
    {scope : Scope} {offset length : Core.Expr} {lowered : Lowered}
    (compiled : Effects.lowerBuiltin scope operation.name [offset, length] = .ok lowered) :
    ∃ expression, Effects.terminate scope operation.kind offset length = .ok expression ∧
      lowered = ⟨.unit, expression⟩ := by
  have expanded : Effects.lowerBuiltin scope operation.name [offset, length] = (do
      let raw ← (do
        let expression ← Effects.terminate scope operation.kind offset length
        pure (Lowered.mk .unit expression) : LowerM Lowered)
      pure raw) := by
    cases operation <;> first | rfl | cases two
  rw [expanded] at compiled
  obtain ⟨expression, terminated, returned⟩ := lower_bind_eq_ok.mp compiled
  exact ⟨expression, terminated, (Except.ok.inj returned).symm⟩

/-- Argument typing and arity are derived from the accepted outer compiler.
The range and exit registers, including overflow and zero-length behavior,
correspond to the independent source operation at the final actual store. -/
theorem preserves (operation : Operation)
    {scope : Scope} {expected : Core.Ty} {arguments : List Lowered} {lowered : Lowered}
    (compiled : lowerBuiltin scope operation.name expected arguments = .ok lowered)
    {sources : List Semantics.Value} {targets : List Core.Value}
    (related : ArgumentsRel arguments sources targets)
    {slots : List EffectSlot} {mapping : Renaming} {environment : Environment}
    {initial store : Store} {state : RuntimeEffectsSemantics.State} {layout : RuntimeEffectsCorrespondence.Layout}
    (runtime : EffectEnvironmentRel slots scope mapping environment)
    (memorySizeMember : ⟨"memorySize", .word, layout.storage.memorySize⟩ ∈ slots)
    (exitMember : ⟨"exit", .word, layout.storage.exit⟩ ∈ slots)
    (offsetMember : ⟨"returnOffset", .word, layout.storage.returnOffset⟩ ∈ slots)
    (sizeMember : ⟨"returnSize", .word, layout.storage.returnSize⟩ ∈ slots)
    (memory : MemoryCorrespondence.StateRel layout.memory layout.storage.memorySize state.memory store)
    (storage : StorageBuiltinCorrespondence.StateRel layout.storage state.storage store)
    (packed : Evaluates environment initial ((packArguments arguments).expression.rename mapping)
      (.inRight .word (bundleValues targets)) store) (sourceType : Ty) :
    ∃ result finalState target final,
      builtin operation.name sourceType sources state = some (result, finalState) ∧
      ResultRel lowered.type result target ∧
      Evaluates environment initial (lowered.expression.rename mapping) target final ∧
      MemoryCorrespondence.StateRel layout.memory layout.storage.memorySize finalState.memory final ∧
      StorageBuiltinCorrespondence.StateRel layout.storage finalState.storage final ∧
      RuntimeEffectsCorrespondence.Frame layout store final ∧ ClosuresPreserved store final ∧
      ∀ value, store.read? layout.storage.world = some value → final.read? layout.storage.world = some value := by
  obtain ⟨words, raw, rawCompiled, typed, loweredEqual⟩ :=
    outer_components (by cases operation <;> rfl) compiled
  have arity : arguments.length = operation.arity := by
    simpa only [List.length_map, List.length_range] using inner_arity operation rawCompiled
  by_cases zero : operation.arity = 0
  · have empty : arguments = [] := List.eq_nil_of_length_eq_zero (arity.trans zero)
    subst arguments
    cases related
    obtain ⟨expression, terminated, rfl⟩ := zero_components operation zero rawCompiled
    cases typed
    cases loweredEqual
    obtain ⟨resultRelated, memoryFinal, storageFinal, frame⟩ := terminate_state memory storage operation.kind Word.zero Word.zero
    refine ⟨_, _, _, _, ?_, resultRelated, ?_, memoryFinal, storageFinal, frame,
      terminate_closures memory storage operation.kind Word.zero Word.zero, finalStore_world storage _ _ _⟩
    · cases operation <;> first | rfl | cases zero
    · apply LanguageResult.bind_success .unit packed
      exact terminate_evaluates terminated (runtime.temporary .unit .unit)
        memorySizeMember exitMember offsetMember sizeMember storage memory.size Word.zero Word.zero
        (fun _ _ => .word) (fun _ _ => .word)
  · have two : operation.arity = 2 := by cases operation <;> simp_all [Operation.arity]
    obtain ⟨offsetExpr, lengthExpr, offset, length, rfl, rfl, rfl⟩ := two_words related words (arity.trans two)
    obtain ⟨expression, terminated, rfl⟩ := two_components operation two rawCompiled
    cases typed
    cases loweredEqual
    obtain ⟨resultRelated, memoryFinal, storageFinal, frame⟩ := terminate_state memory storage operation.kind offset length
    refine ⟨_, _, _, _, ?_, resultRelated, ?_, memoryFinal, storageFinal, frame,
      terminate_closures memory storage operation.kind offset length, finalStore_world storage _ _ _⟩
    · cases operation <;> first | rfl | cases two
    · apply LanguageResult.bind_success .unit packed
      apply terminate_evaluates terminated
        (runtime.temporary (.product .word .word) (.pair (.word offset) (.word length)))
        memorySizeMember exitMember offsetMember sizeMember storage memory.size offset length
      · intro extra store
        exact .first (rightValue := .word length) (.var (by simp [Renaming.lift]))
      · intro extra store
        exact .second (leftValue := .word offset) (.var (by simp [Renaming.lift]))

end Termination

namespace ReturnData
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
      RuntimeEffectsCorrespondence.Frame layout store final ∧ ClosuresPreserved store final ∧
      ∀ value, store.read? layout.storage.world = some value → final.read? layout.storage.world = some value := by
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
          refine ⟨_, _, resultRelated, ?_, memoryFinal, storageFinal, frame, terminatedClosures, Termination.finalStore_world storage _ _ _⟩
          apply LanguageResult.bind_success .unit packed
          exact .ifTrue (.binary sourceEvaluated dataSizeEvaluated (by simp [BinaryOp.apply, invalidSource])) terminated
      | lengthOverflow validSource invalidLength =>
          obtain ⟨resultRelated, memoryFinal, storageFinal, frame⟩ := terminatedState
          refine ⟨_, _, resultRelated, ?_, memoryFinal, storageFinal, frame, terminatedClosures, Termination.finalStore_world storage _ _ _⟩
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
            MemoryEffectCorrespondence.closures_preserved memory frame, ?_⟩
          · apply LanguageResult.bind_success .unit packed
            apply Evaluates.ifFalse (.binary sourceEvaluated dataSizeEvaluated (by simp [BinaryOp.apply, validSource]))
            apply Evaluates.ifFalse (.binary lengthEvaluated (.binary dataSizeEvaluated sourceEvaluated rfl)
              (by simp [BinaryOp.apply, validLength]))
            rw [MemoryCopyCorrespondence.copyPackedFrom_rename]
            exact evaluated
          · intro value found
            have distinct := layout.distinct
            simp [StorageBuiltinCorrespondence.Locations.all] at distinct
            exact frame.read _ _ (by intro same; simp_all) (by intro same; simp_all) found

end ReturnData
end Solcore.Frontend.RustHull.ReadOnlyWorldBuiltinCorrespondence
