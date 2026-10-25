import Solcore.Frontend.RustHull.CallBuiltinArguments
import Solcore.Frontend.RustHull.ChildCallBuiltinEvaluation
import Solcore.Frontend.RustHull.RuntimeChildCallTerminationCorrespondence

/-! Ordinary and static calls preserve their independent source results through
actual argument packing, ordered guards, callback dispatch, and caller updates. -/
set_option autoImplicit false
set_option linter.unusedSimpArgs false
namespace Solcore.Frontend.RustHull.ChildCallBuiltinCorrespondence
open Core Correspondence ScalarExecution PureCallCorrespondence EffectBuiltinCorrespondence
open RuntimeCallEffectsCorrespondence (Layout Handlers CallPassive account_related runtime_related)
open RuntimeChildCallEffectsCorrespondence
open CallBuiltinCorrespondence

section
variable {scope : Scope} {expected : Core.Ty} {arguments : List Lowered} {lowered : Lowered}
variable {gas target value inputOffset inputLength outputOffset outputLength : Word}
variable {result : Semantics.Result Semantics.Value} {finalState : RuntimeCallEffectsSemantics.State}
variable {targets : List Core.Value} {slots : List EffectSlot} {mapping : Renaming} {environment : Environment}
variable {initial store : Store} {layout : Layout} {baseline : Nat → Option Value}
variable {image : Option (List UInt8)} {handlers : Handlers layout} {anchors : Anchors} {context : Context layout} {world : World}
variable {children : RuntimeCallEffectsSemantics.State → AccountCallSemantics.Children}
variable {state : Semantics.State RuntimeCallEffectsSemantics.State}

theorem ordinary_preserves
    (compiled : lowerBuiltin scope "call" expected arguments = .ok lowered)
    (computed : RuntimeCallEffectsSemantics.Call children .ordinary
      gas target value inputOffset inputLength outputOffset outputLength state.external result finalState)
    (related : ArgumentsRel arguments [.word gas, .word target, .word value, .word inputOffset,
      .word inputLength, .word outputOffset, .word outputLength] targets)
    (runtime : EffectEnvironmentRel slots scope mapping environment)
    (passive : RuntimeLogEffectsCorrespondence.Passive layout.toLogLayout slots)
    (callPassive : CallPassive layout slots)
    (memoryMember : ⟨"memory", WordMapping.type, layout.memory⟩ ∈ slots)
    (memorySizeMember : ⟨"memorySize", .word, layout.storage.memorySize⟩ ∈ slots)
    (dataMember : ⟨"returnData", WordMapping.type, layout.returnData⟩ ∈ slots)
    (dataSizeMember : ⟨"returnDataSize", .word, layout.returnDataSize⟩ ∈ slots)
    (handlerMember : ⟨"callHandler", OptionalCell.cellType Calls.callbackType, layout.callHandler⟩ ∈ slots)
    (addressMember : ⟨"address", .word, layout.storage.address⟩ ∈ slots)
    (depthMember : ⟨"callDepth", .word, layout.callDepth⟩ ∈ slots)
    (staticMember : ⟨"isStatic", .bool, layout.storage.isStatic⟩ ∈ slots)
    (exitMember : ⟨"exit", .word, layout.storage.exit⟩ ∈ slots)
    (offsetMember : ⟨"returnOffset", .word, layout.storage.returnOffset⟩ ∈ slots)
    (sizeMember : ⟨"returnSize", .word, layout.storage.returnSize⟩ ∈ slots)
    (stateRelated : StateRel (model layout baseline slots image handlers anchors context) world state store)
    (callback : CallbackPreservation layout handlers anchors context children state.external)
    (packed : Evaluates environment initial ((packArguments arguments).expression.rename mapping)
      (.inRight .word (bundleValues targets)) store) :
    ∃ resultValue final, ResultRel lowered.type result resultValue ∧
      Evaluates environment initial (lowered.expression.rename mapping) resultValue final ∧
      StateRel (model layout baseline slots image handlers anchors context) world {state with external := finalState} final ∧
      ClosuresPreserved store final := by
  obtain ⟨words, raw, rawCompiled, typed, loweredEqual⟩ := outer_components (by rfl) compiled
  have arity : arguments.length = 7 := by
    simpa only [List.length_map, List.length_range, RuntimeCallEffectsSemantics.Operation.arity] using inner_arity .ordinary rawCompiled
  obtain ⟨gasExpr, targetExpr, valueExpr, inputOffsetExpr, inputLengthExpr, outputOffsetExpr, outputLengthExpr,
    gas', target', value', inputOffset', inputLength', outputOffset', outputLength', rfl, same, rfl⟩ := seven_words related words arity
  cases same
  obtain ⟨references, invalid, referencesCompiled, invalidCompiled, rfl⟩ := ordinary_components rawCompiled
  cases typed
  cases loweredEqual
  let input := bundleValues [.word gas, .word target, .word value, .word inputOffset,
    .word inputLength, .word outputOffset, .word outputLength]
  let inputType := bundleType [.word, .word, .word, .word, .word, .word, .word]
  have runtime' := runtime.temporary inputType input
  have inputs := inputs referencesCompiled runtime' memoryMember memorySizeMember dataMember dataSizeMember
    handlerMember addressMember depthMember staticMember (base_related stateRelated)
  have gasEvaluated : Evaluates (input :: environment) store ((projectArgument 0 7 (.var 0)).rename mapping.lift) (.word gas) store := .first (.var rfl)
  have targetEvaluated : Evaluates (input :: environment) store ((projectArgument 1 7 (.var 0)).rename mapping.lift) (.word target) store := .first (.second (.var rfl))
  have valueEvaluated : Evaluates (input :: environment) store ((projectArgument 2 7 (.var 0)).rename mapping.lift) (.word value) store := .first (.second (.second (.var rfl)))
  have inputOffsetEvaluated : Evaluates (input :: environment) store ((projectArgument 3 7 (.var 0)).rename mapping.lift) (.word inputOffset) store := .first (.second (.second (.second (.var rfl))))
  have inputLengthEvaluated : Evaluates (input :: environment) store ((projectArgument 4 7 (.var 0)).rename mapping.lift) (.word inputLength) store := .first (.second (.second (.second (.second (.var rfl)))))
  have outputOffsetEvaluated : Evaluates (input :: environment) store ((projectArgument 5 7 (.var 0)).rename mapping.lift) (.word outputOffset) store := .first (.second (.second (.second (.second (.second (.var rfl))))))
  have outputLengthEvaluated : Evaluates (input :: environment) store ((projectArgument 6 7 (.var 0)).rename mapping.lift) (.word outputLength) store := .second (.second (.second (.second (.second (.second (.var rfl))))))
  have beforeRuntime := RuntimeEnvironmentEffectsCorrespondence.runtime_related
    (RuntimeLogEffectsCorrespondence.runtime_related (RuntimeAccountEffectsCorrespondence.runtime_related (account_related (base_related stateRelated))))
  have memory := RuntimeEffectsCorrespondence.memory_related beforeRuntime
  have storage := RuntimeEffectsCorrespondence.storage_related beforeRuntime
  cases computed with
  | staticValue _ isStatic nonzero =>
      have terminated := TerminationBuiltinCorrespondence.terminate_evaluates invalidCompiled runtime'
        memorySizeMember exitMember offsetMember sizeMember storage memory.size Word.zero Word.zero
        (fun _ _ => .word) (fun _ _ => .word)
      obtain ⟨_, memoryFinal, storageFinal, frame⟩ := TerminationBuiltinCorrespondence.terminate_state memory storage 3 Word.zero Word.zero
      have finalRelated := RuntimeCallEffectsCorrespondence.runtime_updated (base_related stateRelated)
        (RuntimeReturnDataEffectsCorrespondence.runtime_updated passive (runtime_related (base_related stateRelated)) memoryFinal storageFinal frame) rfl
      have strengthened := of_base finalRelated (invalid_linked stateRelated)
        (context.updated (base_related stateRelated) finalRelated stateRelated.external.2.2.1.2)
      refine ⟨.inLeft .word (.word Word.maximum), _, .language _, ?_, strengthened,
        TerminationBuiltinCorrespondence.terminate_closures memory storage 3 Word.zero Word.zero⟩
      apply LanguageResult.bind_success .word packed
      apply Evaluates.ifTrue (isStatic ▸ inputs.isStatic)
      apply Evaluates.ifFalse (.binary valueEvaluated .word (by simp [BinaryOp.apply, nonzero]))
      exact LanguageResult.bind_failure .word terminated
  | gasOverflow _ notStatic nonzero overflow =>
      refine ⟨.inLeft .word (.word (Word.ofNatModulo 13)), store, .language _, ?_, stateRelated, ClosuresPreserved.refl _⟩
      apply LanguageResult.bind_success .word packed
      apply Evaluates.ifFalse (notStatic ▸ inputs.isStatic)
      apply Evaluates.ifFalse (.binary valueEvaluated .word (by simp [BinaryOp.apply, nonzero]))
      exact .ifTrue (.binary gasEvaluated .word (by simp [BinaryOp.apply, overflow])) (.inLeft .word)
  | invoked permitted stipend executed =>
      have gasSupplied : Evaluates (input :: environment) store
          ((Core.Expr.ifE (.binary .wordEq (projectArgument 2 7 (.var 0)) (.word Word.zero))
            (projectArgument 0 7 (.var 0)) (.binary .wordAdd (projectArgument 0 7 (.var 0)) (.word (Word.ofNatModulo 2300)))).rename mapping.lift)
          (.word (RuntimeCallEffectsSemantics.arguments .ordinary state.external gas target value inputOffset inputLength outputOffset outputLength).gas) store := by
        by_cases zero : value = Word.zero
        · simpa only [Core.Expr.rename, RuntimeCallEffectsSemantics.arguments, zero, ne_eq, not_true_eq_false, and_false, ↓reduceIte] using
            Evaluates.ifTrue (.binary valueEvaluated .word (by simp [BinaryOp.apply, zero])) gasEvaluated
        · simpa only [Core.Expr.rename, RuntimeCallEffectsSemantics.arguments, zero, ne_eq, not_false_eq_true, and_self, ↓reduceIte] using
            Evaluates.ifFalse (.binary valueEvaluated .word (by simp [BinaryOp.apply, zero])) (.binary gasEvaluated .word rfl)
      obtain ⟨resultValue, final, resultRelated, evaluated, finalRelated, retained⟩ :=
        inputs.invoke_linked_evaluates callPassive stateRelated callback executed inputs.isStatic gasSupplied targetEvaluated valueEvaluated
          inputOffsetEvaluated inputLengthEvaluated outputOffsetEvaluated outputLengthEvaluated
      refine ⟨resultValue, final, resultRelated, ?_, finalRelated, retained⟩
      apply LanguageResult.bind_success .word packed
      by_cases zero : value = Word.zero
      · cases static : state.external.runtime.runtime.runtime.runtime.runtime.storage.isStatic
        · exact .ifFalse (static ▸ inputs.isStatic) (.ifTrue (.binary valueEvaluated .word (by simp [BinaryOp.apply, zero])) evaluated)
        · exact .ifTrue (static ▸ inputs.isStatic) (.ifTrue (.binary valueEvaluated .word (by simp [BinaryOp.apply, zero])) evaluated)
      · have notStatic : state.external.runtime.runtime.runtime.runtime.runtime.storage.isStatic = false := by
          rcases permitted with impossible | zero' | notStatic
          · cases impossible
          · exact False.elim (zero zero')
          · exact notStatic
        apply Evaluates.ifFalse (notStatic ▸ inputs.isStatic)
        apply Evaluates.ifFalse (.binary valueEvaluated .word (by simp [BinaryOp.apply, zero]))
        exact .ifFalse (.binary gasEvaluated .word (by simp [BinaryOp.apply, stipend rfl zero])) evaluated

theorem static_preserves
    (compiled : lowerBuiltin scope "staticcall" expected arguments = .ok lowered)
    (computed : RuntimeCallEffectsSemantics.Call children .staticCall
      gas target Word.zero inputOffset inputLength outputOffset outputLength state.external result finalState)
    (related : ArgumentsRel arguments [.word gas, .word target, .word inputOffset,
      .word inputLength, .word outputOffset, .word outputLength] targets)
    (runtime : EffectEnvironmentRel slots scope mapping environment)
    (_passive : RuntimeLogEffectsCorrespondence.Passive layout.toLogLayout slots)
    (callPassive : CallPassive layout slots)
    (memoryMember : ⟨"memory", WordMapping.type, layout.memory⟩ ∈ slots)
    (memorySizeMember : ⟨"memorySize", .word, layout.storage.memorySize⟩ ∈ slots)
    (dataMember : ⟨"returnData", WordMapping.type, layout.returnData⟩ ∈ slots)
    (dataSizeMember : ⟨"returnDataSize", .word, layout.returnDataSize⟩ ∈ slots)
    (handlerMember : ⟨"callHandler", OptionalCell.cellType Calls.callbackType, layout.callHandler⟩ ∈ slots)
    (addressMember : ⟨"address", .word, layout.storage.address⟩ ∈ slots)
    (depthMember : ⟨"callDepth", .word, layout.callDepth⟩ ∈ slots)
    (staticMember : ⟨"isStatic", .bool, layout.storage.isStatic⟩ ∈ slots)
    (_exitMember : ⟨"exit", .word, layout.storage.exit⟩ ∈ slots)
    (_offsetMember : ⟨"returnOffset", .word, layout.storage.returnOffset⟩ ∈ slots)
    (_sizeMember : ⟨"returnSize", .word, layout.storage.returnSize⟩ ∈ slots)
    (stateRelated : StateRel (model layout baseline slots image handlers anchors context) world state store)
    (callback : CallbackPreservation layout handlers anchors context children state.external)
    (packed : Evaluates environment initial ((packArguments arguments).expression.rename mapping)
      (.inRight .word (bundleValues targets)) store) :
    ∃ resultValue final, ResultRel lowered.type result resultValue ∧
      Evaluates environment initial (lowered.expression.rename mapping) resultValue final ∧
      StateRel (model layout baseline slots image handlers anchors context) world {state with external := finalState} final ∧
      ClosuresPreserved store final := by
  obtain ⟨words, raw, rawCompiled, typed, loweredEqual⟩ := outer_components (by rfl) compiled
  have arity : arguments.length = 6 := by
    simpa only [List.length_map, List.length_range, RuntimeCallEffectsSemantics.Operation.arity] using inner_arity .staticCall rawCompiled
  obtain ⟨gasExpr, targetExpr, inputOffsetExpr, inputLengthExpr, outputOffsetExpr, outputLengthExpr,
    gas', target', inputOffset', inputLength', outputOffset', outputLength', rfl, same, rfl⟩ := six_words related words arity
  cases same
  obtain ⟨references, referencesCompiled, rfl⟩ := static_components rawCompiled
  cases typed
  cases loweredEqual
  let input := bundleValues [.word gas, .word target, .word inputOffset,
    .word inputLength, .word outputOffset, .word outputLength]
  let inputType := bundleType [.word, .word, .word, .word, .word, .word]
  have runtime' := runtime.temporary inputType input
  have inputs := inputs referencesCompiled runtime' memoryMember memorySizeMember dataMember dataSizeMember
    handlerMember addressMember depthMember staticMember (base_related stateRelated)
  have gasEvaluated : Evaluates (input :: environment) store ((projectArgument 0 6 (.var 0)).rename mapping.lift) (.word gas) store := .first (.var rfl)
  have targetEvaluated : Evaluates (input :: environment) store ((projectArgument 1 6 (.var 0)).rename mapping.lift) (.word target) store := .first (.second (.var rfl))
  have inputOffsetEvaluated : Evaluates (input :: environment) store ((projectArgument 2 6 (.var 0)).rename mapping.lift) (.word inputOffset) store := .first (.second (.second (.var rfl)))
  have inputLengthEvaluated : Evaluates (input :: environment) store ((projectArgument 3 6 (.var 0)).rename mapping.lift) (.word inputLength) store := .first (.second (.second (.second (.var rfl))))
  have outputOffsetEvaluated : Evaluates (input :: environment) store ((projectArgument 4 6 (.var 0)).rename mapping.lift) (.word outputOffset) store := .first (.second (.second (.second (.second (.var rfl)))))
  have outputLengthEvaluated : Evaluates (input :: environment) store ((projectArgument 5 6 (.var 0)).rename mapping.lift) (.word outputLength) store := .second (.second (.second (.second (.second (.var rfl)))))
  cases computed with
  | staticValue ordinary _ _ => cases ordinary
  | gasOverflow ordinary _ _ _ => cases ordinary
  | invoked _ _ executed =>
      obtain ⟨resultValue, final, resultRelated, evaluated, finalRelated, retained⟩ :=
        inputs.invoke_linked_evaluates callPassive stateRelated callback executed (staticExpr := .bool true) .bool gasEvaluated targetEvaluated
          (valueExpr := .word Word.zero) .word inputOffsetEvaluated inputLengthEvaluated outputOffsetEvaluated outputLengthEvaluated
      exact ⟨resultValue, final, resultRelated, LanguageResult.bind_success .word packed evaluated, finalRelated, retained⟩

end
end Solcore.Frontend.RustHull.ChildCallBuiltinCorrespondence
