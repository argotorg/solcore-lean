import Solcore.Frontend.RustHull.CallModeBuiltinEvaluation
import Solcore.Frontend.RustHull.CallModeBuiltinArguments

/-! CALLCODE and DELEGATECALL follow actual lowering, including the stipend
check and inherited message observations, before invoking their captured handler. -/
set_option autoImplicit false
set_option linter.unusedSimpArgs false
namespace Solcore.Frontend.RustHull.CallModeBuiltinCorrespondence
open Core Correspondence ScalarExecution PureCallCorrespondence EffectBuiltinCorrespondence
open RuntimeCallEffectsCorrespondence (Layout CallPassive)
open RuntimeChildCallEffectsCorrespondence (Anchors Context)
open RuntimeCallModeEffectsCorrespondence
open CallBuiltinCorrespondence (seven_words six_words)

section
variable {scope : Scope} {expected : Core.Ty} {arguments : List Lowered} {lowered : Lowered}
variable {gas target value inputOffset inputLength outputOffset outputLength : Word}
variable {result : Semantics.Result Semantics.Value} {finalState : RuntimeCallModeSemantics.State}
variable {targets : List Core.Value} {slots : List EffectSlot} {mapping : Renaming} {environment : Environment}
variable {initial store : Store} {layout : Layout} {baseline : Nat → Option Value}
variable {image : Option (List UInt8)} {handlers : ModeHandlers layout} {anchors : Anchors} {context : Context layout} {world : World}
variable {children : RuntimeCallModeSemantics.State → AccountCallSemantics.Children}
variable {state : Semantics.State RuntimeCallModeSemantics.State}

theorem callCode_preserves
    (compiled : lowerBuiltin scope "callcode" expected arguments = .ok lowered)
    (computed : RuntimeCallModeSemantics.Call children .callCode
      gas target value inputOffset inputLength outputOffset outputLength state.external result finalState)
    (related : ArgumentsRel arguments [.word gas, .word target, .word value, .word inputOffset,
      .word inputLength, .word outputOffset, .word outputLength] targets)
    (runtime : EffectEnvironmentRel slots scope mapping environment)
    (callPassive : CallPassive layout slots)
    (memoryMember : ⟨"memory", WordMapping.type, layout.memory⟩ ∈ slots)
    (memorySizeMember : ⟨"memorySize", .word, layout.storage.memorySize⟩ ∈ slots)
    (dataMember : ⟨"returnData", WordMapping.type, layout.returnData⟩ ∈ slots)
    (dataSizeMember : ⟨"returnDataSize", .word, layout.returnDataSize⟩ ∈ slots)
    (handlerMember : ⟨"callCodeHandler", OptionalCell.cellType Calls.callbackType, handlers.callCode.location⟩ ∈ slots)
    (addressMember : ⟨"address", .word, layout.storage.address⟩ ∈ slots)
    (depthMember : ⟨"callDepth", .word, layout.callDepth⟩ ∈ slots)
    (staticMember : ⟨"isStatic", .bool, layout.storage.isStatic⟩ ∈ slots)
    (stateRelated : StateRel (model layout baseline slots image handlers anchors context) world state store)
    (callback : CallbackPreservation layout handlers anchors context children .callCode state.external)
    (packed : Evaluates environment initial ((packArguments arguments).expression.rename mapping)
      (.inRight .word (bundleValues targets)) store) :
    ∃ resultValue final, ResultRel lowered.type result resultValue ∧
      Evaluates environment initial (lowered.expression.rename mapping) resultValue final ∧
      StateRel (model layout baseline slots image handlers anchors context) world {state with external := finalState} final ∧
      ClosuresPreserved store final := by
  obtain ⟨words, raw, rawCompiled, typed, loweredEqual⟩ := outer_components (by rfl) compiled
  have arity : arguments.length = 7 := by
    simpa only [List.length_map, List.length_range, RuntimeCallModeSemantics.Operation.arity] using CallModeBuiltinCorrespondence.inner_arity .callCode rawCompiled
  obtain ⟨gasExpr, targetExpr, valueExpr, inputOffsetExpr, inputLengthExpr, outputOffsetExpr, outputLengthExpr,
    gas', target', value', inputOffset', inputLength', outputOffset', outputLength', rfl, same, rfl⟩ := seven_words related words arity
  cases same
  obtain ⟨references, invalid, referencesCompiled, invalidCompiled, rfl⟩ := callCode_components rawCompiled
  cases typed
  cases loweredEqual
  let input := bundleValues [.word gas, .word target, .word value, .word inputOffset,
    .word inputLength, .word outputOffset, .word outputLength]
  let inputType := bundleType [.word, .word, .word, .word, .word, .word, .word]
  have runtime' := runtime.temporary inputType input
  have storageBefore := RuntimeEffectsCorrespondence.storage_related
    (RuntimeEnvironmentEffectsCorrespondence.runtime_related
    (RuntimeLogEffectsCorrespondence.runtime_related
    (RuntimeAccountEffectsCorrespondence.runtime_related (RuntimeCallEffectsCorrespondence.account_related (base_related stateRelated)))))
  have inputs := inputs (operation := .callCode) referencesCompiled runtime' memoryMember memorySizeMember dataMember dataSizeMember
    handlerMember addressMember storageBefore.address depthMember staticMember stateRelated
  have gasEvaluated : Evaluates (input :: environment) store ((projectArgument 0 7 (.var 0)).rename mapping.lift) (.word gas) store := .first (.var rfl)
  have targetEvaluated : Evaluates (input :: environment) store ((projectArgument 1 7 (.var 0)).rename mapping.lift) (.word target) store := .first (.second (.var rfl))
  have valueEvaluated : Evaluates (input :: environment) store ((projectArgument 2 7 (.var 0)).rename mapping.lift) (.word value) store := .first (.second (.second (.var rfl)))
  have inputOffsetEvaluated : Evaluates (input :: environment) store ((projectArgument 3 7 (.var 0)).rename mapping.lift) (.word inputOffset) store := .first (.second (.second (.second (.var rfl))))
  have inputLengthEvaluated : Evaluates (input :: environment) store ((projectArgument 4 7 (.var 0)).rename mapping.lift) (.word inputLength) store := .first (.second (.second (.second (.second (.var rfl)))))
  have outputOffsetEvaluated : Evaluates (input :: environment) store ((projectArgument 5 7 (.var 0)).rename mapping.lift) (.word outputOffset) store := .first (.second (.second (.second (.second (.second (.var rfl))))))
  have outputLengthEvaluated : Evaluates (input :: environment) store ((projectArgument 6 7 (.var 0)).rename mapping.lift) (.word outputLength) store := .second (.second (.second (.second (.second (.second (.var rfl))))))
  cases computed with
  | staticValue ordinary _ _ => cases ordinary
  | gasOverflow _ _ nonzero overflow =>
      refine ⟨.inLeft .word (.word (Word.ofNatModulo 13)), store, .language _, ?_, stateRelated, ClosuresPreserved.refl _⟩
      apply LanguageResult.bind_success .word packed
      apply Evaluates.ifFalse (.binary valueEvaluated .word (by simp [BinaryOp.apply, nonzero]))
      exact .ifTrue (.binary gasEvaluated .word (by simp [BinaryOp.apply, overflow])) (.inLeft .word)
  | invoked permitted stipend executed =>
      have gasSupplied : Evaluates (input :: environment) store
          ((Core.Expr.ifE (.binary .wordEq (projectArgument 2 7 (.var 0)) (.word Word.zero))
            (projectArgument 0 7 (.var 0)) (.binary .wordAdd (projectArgument 0 7 (.var 0)) (.word (Word.ofNatModulo 2300)))).rename mapping.lift)
          (.word (RuntimeCallModeSemantics.arguments .callCode state.external gas target value inputOffset inputLength outputOffset outputLength).gas) store := by
        by_cases zero : value = Word.zero
        · simpa only [Core.Expr.rename, RuntimeCallModeSemantics.arguments, RuntimeCallModeSemantics.Operation.hasStipend, zero, ne_eq, not_true_eq_false, and_false, ↓reduceIte] using
            Evaluates.ifTrue (.binary valueEvaluated .word (by simp [BinaryOp.apply, zero])) gasEvaluated
        · simpa only [Core.Expr.rename, RuntimeCallModeSemantics.arguments, RuntimeCallModeSemantics.Operation.hasStipend, zero, ne_eq, not_false_eq_true, and_self, ↓reduceIte] using
            Evaluates.ifFalse (.binary valueEvaluated .word (by simp [BinaryOp.apply, zero])) (.binary gasEvaluated .word rfl)
      obtain ⟨resultValue, final, resultRelated, evaluated, finalRelated, retained⟩ :=
        inputs.invoke_evaluates callPassive stateRelated callback executed inputs.isStatic gasSupplied targetEvaluated valueEvaluated
          inputOffsetEvaluated inputLengthEvaluated outputOffsetEvaluated outputLengthEvaluated
      refine ⟨resultValue, final, resultRelated, ?_, finalRelated, retained⟩
      apply LanguageResult.bind_success .word packed
      by_cases zero : value = Word.zero
      · exact .ifTrue (.binary valueEvaluated .word (by simp [BinaryOp.apply, zero])) evaluated
      · apply Evaluates.ifFalse (.binary valueEvaluated .word (by simp [BinaryOp.apply, zero]))
        exact .ifFalse (.binary gasEvaluated .word (by simp [BinaryOp.apply, stipend rfl zero])) evaluated

theorem delegate_preserves
    (compiled : lowerBuiltin scope "delegatecall" expected arguments = .ok lowered)
    (computed : RuntimeCallModeSemantics.Call children .delegateCall
      gas target ((RuntimeCallModeSemantics.observations state.external).direct .callvalue) inputOffset inputLength outputOffset outputLength state.external result finalState)
    (related : ArgumentsRel arguments [.word gas, .word target, .word inputOffset,
      .word inputLength, .word outputOffset, .word outputLength] targets)
    (runtime : EffectEnvironmentRel slots scope mapping environment)
    (callPassive : CallPassive layout slots)
    (memoryMember : ⟨"memory", WordMapping.type, layout.memory⟩ ∈ slots)
    (memorySizeMember : ⟨"memorySize", .word, layout.storage.memorySize⟩ ∈ slots)
    (dataMember : ⟨"returnData", WordMapping.type, layout.returnData⟩ ∈ slots)
    (dataSizeMember : ⟨"returnDataSize", .word, layout.returnDataSize⟩ ∈ slots)
    (handlerMember : ⟨"delegateCallHandler", OptionalCell.cellType Calls.callbackType, handlers.delegateCall.location⟩ ∈ slots)
    {callerLocation valueLocation : Nat}
    (callerMember : ⟨"caller", .word, callerLocation⟩ ∈ slots)
    (valueMember : ⟨"callvalue", .word, valueLocation⟩ ∈ slots)
    (depthMember : ⟨"callDepth", .word, layout.callDepth⟩ ∈ slots)
    (staticMember : ⟨"isStatic", .bool, layout.storage.isStatic⟩ ∈ slots)
    (stateRelated : StateRel (model layout baseline slots image handlers anchors context) world state store)
    (callback : CallbackPreservation layout handlers anchors context children .delegateCall state.external)
    (packed : Evaluates environment initial ((packArguments arguments).expression.rename mapping)
      (.inRight .word (bundleValues targets)) store) :
    ∃ resultValue final, ResultRel lowered.type result resultValue ∧
      Evaluates environment initial (lowered.expression.rename mapping) resultValue final ∧
      StateRel (model layout baseline slots image handlers anchors context) world {state with external := finalState} final ∧
      ClosuresPreserved store final := by
  obtain ⟨words, raw, rawCompiled, typed, loweredEqual⟩ := outer_components (by rfl) compiled
  have arity : arguments.length = 6 := by
    simpa only [List.length_map, List.length_range, RuntimeCallModeSemantics.Operation.arity] using inner_arity .delegateCall rawCompiled
  obtain ⟨gasExpr, targetExpr, inputOffsetExpr, inputLengthExpr, outputOffsetExpr, outputLengthExpr,
    gas', target', inputOffset', inputLength', outputOffset', outputLength', rfl, same, rfl⟩ := six_words related words arity
  cases same
  obtain ⟨references, inheritedValue, referencesCompiled, valueCompiled, rfl⟩ := delegate_components rawCompiled
  cases typed
  cases loweredEqual
  let input := bundleValues [.word gas, .word target, .word inputOffset,
    .word inputLength, .word outputOffset, .word outputLength]
  let inputType := bundleType [.word, .word, .word, .word, .word, .word]
  have runtime' := runtime.temporary inputType input
  have observed := RuntimeEnvironmentEffectsCorrespondence.observations_related
    (RuntimeLogEffectsCorrespondence.runtime_related
    (RuntimeAccountEffectsCorrespondence.runtime_related (RuntimeCallEffectsCorrespondence.account_related (base_related stateRelated))))
  have callerRead := observed _ callerMember _ (show EnvironmentBuiltinCorrespondence.observation
    (RuntimeCallModeSemantics.observations state.external) "caller" .word = some (.word ((RuntimeCallModeSemantics.observations state.external).direct .caller)) from rfl)
  have valueRead := observed _ valueMember _ (show EnvironmentBuiltinCorrespondence.observation
    (RuntimeCallModeSemantics.observations state.external) "callvalue" .word = some (.word ((RuntimeCallModeSemantics.observations state.external).direct .callvalue)) from rfl)
  have inputs := inputs (operation := .delegateCall) referencesCompiled runtime' memoryMember memorySizeMember dataMember dataSizeMember
    handlerMember callerMember callerRead depthMember staticMember stateRelated
  have valueEvaluated : Evaluates (input :: environment) store ((Core.Expr.loadCell inheritedValue).rename mapping.lift)
      (.word ((RuntimeCallModeSemantics.observations state.external).direct .callvalue)) store :=
    .loadCell (reference_evaluates runtime' valueMember valueCompiled store) valueRead
  have gasEvaluated : Evaluates (input :: environment) store ((projectArgument 0 6 (.var 0)).rename mapping.lift) (.word gas) store := .first (.var rfl)
  have targetEvaluated : Evaluates (input :: environment) store ((projectArgument 1 6 (.var 0)).rename mapping.lift) (.word target) store := .first (.second (.var rfl))
  have inputOffsetEvaluated : Evaluates (input :: environment) store ((projectArgument 2 6 (.var 0)).rename mapping.lift) (.word inputOffset) store := .first (.second (.second (.var rfl)))
  have inputLengthEvaluated : Evaluates (input :: environment) store ((projectArgument 3 6 (.var 0)).rename mapping.lift) (.word inputLength) store := .first (.second (.second (.second (.var rfl))))
  have outputOffsetEvaluated : Evaluates (input :: environment) store ((projectArgument 4 6 (.var 0)).rename mapping.lift) (.word outputOffset) store := .first (.second (.second (.second (.second (.var rfl)))))
  have outputLengthEvaluated : Evaluates (input :: environment) store ((projectArgument 5 6 (.var 0)).rename mapping.lift) (.word outputLength) store := .second (.second (.second (.second (.second (.var rfl)))))
  cases computed with
  | staticValue ordinary _ _ => cases ordinary
  | gasOverflow stipend _ _ _ => cases stipend
  | invoked _ _ executed =>
      obtain ⟨resultValue, final, resultRelated, evaluated, finalRelated, retained⟩ :=
        inputs.invoke_evaluates callPassive stateRelated callback executed inputs.isStatic gasEvaluated targetEvaluated
          valueEvaluated inputOffsetEvaluated inputLengthEvaluated outputOffsetEvaluated outputLengthEvaluated
      exact ⟨resultValue, final, resultRelated, LanguageResult.bind_success .word packed evaluated, finalRelated, retained⟩

end
end Solcore.Frontend.RustHull.CallModeBuiltinCorrespondence
