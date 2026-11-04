import Solcore.Frontend.RustHull.Internal.CallTransport
import Solcore.Frontend.RustHull.Internal.CallStates
import Solcore.Frontend.RustHull.Internal.TerminationLayers
import Solcore.Frontend.RustHull.Internal.StorageState
import Solcore.Frontend.RustHull.Internal.AccountCalls
import Solcore.Frontend.RustHull.Internal.Derivations
import Solcore.Frontend.RustHull.Semantics.Frames
import Solcore.Frontend.RustHull.Internal.RuntimeObjects

/-!
# Call builtins

CALL, STATICCALL, CALLCODE, DELEGATECALL, SELFDESTRUCT, revert and inline Yul through the actual
builtin compiler.
-/

section
-- leanmerge: from Solcore.Frontend.RustHull.CallBuiltinEvaluation
/-! Reserved call references evaluate to the concrete initialized caller cells.
Argument values are then assembled for the actual transport entry. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.CallBuiltinCorrespondence
open Core Correspondence ScalarExecution EffectBuiltinCorrespondence
open RuntimeCallEffectsCorrespondence

structure Inputs (references : References) (mapping : Renaming) (environment : Environment)
    (store : Store) (layout : Layout) (state : RuntimeCallEffectsSemantics.State) : Prop where
  memory : Evaluates environment store (references.memory.rename mapping) (.cellRef WordMapping.type layout.memory) store
  memorySize : Evaluates environment store (references.memorySize.rename mapping) (.cellRef .word layout.storage.memorySize) store
  data : Evaluates environment store (references.returnData.rename mapping) (.cellRef WordMapping.type layout.returnData) store
  dataSize : Evaluates environment store (references.returnDataSize.rename mapping) (.cellRef .word layout.returnDataSize) store
  handler : Evaluates environment store (references.handler.rename mapping) (.cellRef (OptionalCell.cellType Calls.callbackType) layout.callHandler) store
  caller : Evaluates environment store ((Core.Expr.loadCell references.caller).rename mapping)
    (.word state.runtime.runtime.runtime.runtime.runtime.storage.address) store
  depth : Evaluates environment store ((Core.Expr.loadCell references.depth).rename mapping) (.word state.callDepth) store
  isStatic : Evaluates environment store ((Core.Expr.loadCell references.isStatic).rename mapping)
    (.bool state.runtime.runtime.runtime.runtime.runtime.storage.isStatic) store

theorem inputs {scope : Scope} {references : References} (compiled : CompiledReferences scope references)
    {slots : List EffectSlot} {mapping : Renaming} {environment : Environment}
    {layout : Layout} {baseline : Nat → Option Core.Value} {image : Option (List UInt8)} {handlers : Handlers layout}
    {world : World} {state : Semantics.State RuntimeCallEffectsSemantics.State} {store : Store}
    (runtime : EffectEnvironmentRel slots scope mapping environment)
    (memoryMember : ⟨"memory", WordMapping.type, layout.memory⟩ ∈ slots)
    (memorySizeMember : ⟨"memorySize", .word, layout.storage.memorySize⟩ ∈ slots)
    (dataMember : ⟨"returnData", WordMapping.type, layout.returnData⟩ ∈ slots)
    (dataSizeMember : ⟨"returnDataSize", .word, layout.returnDataSize⟩ ∈ slots)
    (handlerMember : ⟨"callHandler", OptionalCell.cellType Calls.callbackType, layout.callHandler⟩ ∈ slots)
    (addressMember : ⟨"address", .word, layout.storage.address⟩ ∈ slots)
    (depthMember : ⟨"callDepth", .word, layout.callDepth⟩ ∈ slots)
    (staticMember : ⟨"isStatic", .bool, layout.storage.isStatic⟩ ∈ slots)
    (related : StateRel (model layout baseline slots image handlers) world state store) :
    Inputs references mapping environment store layout state.external := by
  have storage := RuntimeEffectsCorrespondence.storage_related
    (RuntimeEnvironmentEffectsCorrespondence.runtime_related
    (RuntimeLogEffectsCorrespondence.runtime_related
    (RuntimeAccountEffectsCorrespondence.runtime_related (account_related related))))
  exact ⟨reference_evaluates runtime memoryMember compiled.memory store,
    reference_evaluates runtime memorySizeMember compiled.memorySize store,
    reference_evaluates runtime dataMember compiled.returnData store,
    reference_evaluates runtime dataSizeMember compiled.returnDataSize store,
    reference_evaluates runtime handlerMember compiled.handler store,
    .loadCell (reference_evaluates runtime addressMember compiled.caller store) storage.address,
    .loadCell (reference_evaluates runtime depthMember compiled.depth store) (depth_related related),
    .loadCell (reference_evaluates runtime staticMember compiled.isStatic store) storage.isStatic⟩

theorem Inputs.invoke_evaluates {references : References} {mapping : Renaming} {environment : Environment}
    {store : Store} {layout : Layout} {baseline : Nat → Option Value} {slots : List EffectSlot}
    {image : Option (List UInt8)} {handlers : Handlers layout} {world : World}
    {state : Semantics.State RuntimeCallEffectsSemantics.State}
    (inputs : Inputs references mapping environment store layout state.external)
    (passive : CallPassive layout slots)
    (related : StateRel (model layout baseline slots image handlers) world state store)
    {operation : RuntimeCallEffectsSemantics.Operation}
    {gas target value inputOffset inputLength outputOffset outputLength : Word}
    {result : Semantics.Result Semantics.Value} {next : CallTransportSemantics.State} {shared : AccountCallSemantics.Shared}
    (executed : CallTransportSemantics.Execute
      (AccountCallSemantics.Dispatch AccountCallSemantics.noChildren .ordinary state.external.runtime.runtime.runtime.runtime.runtime.storage.address)
      true (RuntimeCallEffectsSemantics.arguments operation state.external gas target value inputOffset inputLength outputOffset outputLength)
      (RuntimeCallEffectsSemantics.transport state.external) (RuntimeCallEffectsSemantics.shared state.external) result next shared)
    {staticExpr gasExpr targetExpr valueExpr inputOffsetExpr inputLengthExpr outputOffsetExpr outputLengthExpr : Core.Expr}
    (staticEvaluated : Evaluates environment store (staticExpr.rename mapping)
      (.bool (RuntimeCallEffectsSemantics.arguments operation state.external gas target value inputOffset inputLength outputOffset outputLength).isStatic) store)
    (gasEvaluated : Evaluates environment store (gasExpr.rename mapping)
      (.word (RuntimeCallEffectsSemantics.arguments operation state.external gas target value inputOffset inputLength outputOffset outputLength).gas) store)
    (targetEvaluated : Evaluates environment store (targetExpr.rename mapping) (.word target) store)
    (valueEvaluated : Evaluates environment store (valueExpr.rename mapping) (.word value) store)
    (inputOffsetEvaluated : Evaluates environment store (inputOffsetExpr.rename mapping) (.word inputOffset) store)
    (inputLengthEvaluated : Evaluates environment store (inputLengthExpr.rename mapping) (.word inputLength) store)
    (outputOffsetEvaluated : Evaluates environment store (outputOffsetExpr.rename mapping) (.word outputOffset) store)
    (outputLengthEvaluated : Evaluates environment store (outputLengthExpr.rename mapping) (.word outputLength) store) :
    ∃ resultValue final, ResultRel .word result resultValue ∧
      Evaluates environment store
        ((invoke references staticExpr gasExpr targetExpr valueExpr inputOffsetExpr inputLengthExpr outputOffsetExpr outputLengthExpr).rename mapping)
        resultValue final ∧
      StateRel (model layout baseline slots image handlers) world
        {state with external := RuntimeCallEffectsSemantics.withTransport state.external next shared} final ∧
      ClosuresPreserved store final := by
  have packed := Evaluates.pair inputs.memory (.pair inputs.memorySize (.pair inputs.data (.pair inputs.dataSize
    (.pair inputs.handler (.pair inputs.caller (.pair inputs.depth (.pair staticEvaluated (.pair gasEvaluated
    (.pair targetEvaluated (.pair valueEvaluated (.pair inputOffsetEvaluated (.pair inputLengthEvaluated
    (.pair outputOffsetEvaluated outputLengthEvaluated)))))))))))))
  obtain ⟨resultValue, final, resultRelated, evaluated, finalRelated, retained⟩ :=
    RuntimeCallEffectsCorrespondence.invoke_preserves executed passive related packed
  refine ⟨resultValue, final, resultRelated, ?_, finalRelated, retained⟩
  unfold invoke
  rw [CallTransportCorrespondence.invoke_rename]
  exact evaluated

end Solcore.Frontend.RustHull.CallBuiltinCorrespondence
end

section
-- leanmerge: from Solcore.Frontend.RustHull.ChildCallBuiltinEvaluation
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.CallBuiltinCorrespondence
open Core Correspondence ScalarExecution
open RuntimeCallEffectsCorrespondence (Layout Handlers CallPassive)
open RuntimeChildCallEffectsCorrespondence (Anchors model CallbackPreservation)

theorem Inputs.invoke_linked_evaluates {references : References} {mapping : Renaming} {environment : Environment}
    {store : Store} {layout : Layout} {baseline : Nat → Option Value} {slots : List EffectSlot}
    {image : Option (List UInt8)} {handlers : Handlers layout} {anchors : Anchors} {context : RuntimeChildCallEffectsCorrespondence.Context layout} {world : World}
    {children : RuntimeCallEffectsSemantics.State → AccountCallSemantics.Children}
    {state : Semantics.State RuntimeCallEffectsSemantics.State}
    (inputs : Inputs references mapping environment store layout state.external)
    (passive : CallPassive layout slots)
    (related : StateRel (model layout baseline slots image handlers anchors context) world state store)
    (callback : CallbackPreservation layout handlers anchors context children state.external)
    {operation : RuntimeCallEffectsSemantics.Operation}
    {gas target value inputOffset inputLength outputOffset outputLength : Word}
    {result : Semantics.Result Semantics.Value} {next : CallTransportSemantics.State} {shared : AccountCallSemantics.Shared}
    (executed : CallTransportSemantics.Execute
      (AccountCallSemantics.Dispatch (children state.external) .ordinary state.external.runtime.runtime.runtime.runtime.runtime.storage.address)
      true (RuntimeCallEffectsSemantics.arguments operation state.external gas target value inputOffset inputLength outputOffset outputLength)
      (RuntimeCallEffectsSemantics.transport state.external) (RuntimeCallEffectsSemantics.shared state.external) result next shared)
    {staticExpr gasExpr targetExpr valueExpr inputOffsetExpr inputLengthExpr outputOffsetExpr outputLengthExpr : Core.Expr}
    (staticEvaluated : Evaluates environment store (staticExpr.rename mapping)
      (.bool (RuntimeCallEffectsSemantics.arguments operation state.external gas target value inputOffset inputLength outputOffset outputLength).isStatic) store)
    (gasEvaluated : Evaluates environment store (gasExpr.rename mapping)
      (.word (RuntimeCallEffectsSemantics.arguments operation state.external gas target value inputOffset inputLength outputOffset outputLength).gas) store)
    (targetEvaluated : Evaluates environment store (targetExpr.rename mapping) (.word target) store)
    (valueEvaluated : Evaluates environment store (valueExpr.rename mapping) (.word value) store)
    (inputOffsetEvaluated : Evaluates environment store (inputOffsetExpr.rename mapping) (.word inputOffset) store)
    (inputLengthEvaluated : Evaluates environment store (inputLengthExpr.rename mapping) (.word inputLength) store)
    (outputOffsetEvaluated : Evaluates environment store (outputOffsetExpr.rename mapping) (.word outputOffset) store)
    (outputLengthEvaluated : Evaluates environment store (outputLengthExpr.rename mapping) (.word outputLength) store) :
    ∃ resultValue final, ResultRel .word result resultValue ∧
      Evaluates environment store
        ((invoke references staticExpr gasExpr targetExpr valueExpr inputOffsetExpr inputLengthExpr outputOffsetExpr outputLengthExpr).rename mapping)
        resultValue final ∧
      StateRel (model layout baseline slots image handlers anchors context) world
        {state with external := RuntimeCallEffectsSemantics.withTransport state.external next shared} final ∧
      ClosuresPreserved store final := by
  have packed := Evaluates.pair inputs.memory (.pair inputs.memorySize (.pair inputs.data (.pair inputs.dataSize
    (.pair inputs.handler (.pair inputs.caller (.pair inputs.depth (.pair staticEvaluated (.pair gasEvaluated
    (.pair targetEvaluated (.pair valueEvaluated (.pair inputOffsetEvaluated (.pair inputLengthEvaluated
    (.pair outputOffsetEvaluated outputLengthEvaluated)))))))))))))
  obtain ⟨resultValue, final, resultRelated, evaluated, finalRelated, retained⟩ :=
    RuntimeChildCallEffectsCorrespondence.invoke_preserves executed passive related callback packed
  refine ⟨resultValue, final, resultRelated, ?_, finalRelated, retained⟩
  unfold invoke
  rw [CallTransportCorrespondence.invoke_rename]
  exact evaluated

end Solcore.Frontend.RustHull.CallBuiltinCorrespondence
end

section
-- leanmerge: from Solcore.Frontend.RustHull.ChildCallBuiltinCorrespondence
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
end

section
-- leanmerge: from Solcore.Frontend.RustHull.CallBuiltinCorrespondence
/-! Ordinary and static calls preserve their independent source results through
actual argument packing, ordered guards, callback dispatch, and caller updates. -/
set_option autoImplicit false
set_option linter.unusedSimpArgs false
namespace Solcore.Frontend.RustHull.CallBuiltinCorrespondence
open Core Correspondence ScalarExecution PureCallCorrespondence EffectBuiltinCorrespondence
open RuntimeCallEffectsCorrespondence

section
variable {scope : Scope} {expected : Core.Ty} {arguments : List Lowered} {lowered : Lowered}
variable {gas target value inputOffset inputLength outputOffset outputLength : Word}
variable {result : Semantics.Result Semantics.Value} {finalState : RuntimeCallEffectsSemantics.State}
variable {targets : List Core.Value} {slots : List EffectSlot} {mapping : Renaming} {environment : Environment}
variable {initial store : Store} {layout : Layout} {baseline : Nat → Option Value}
variable {image : Option (List UInt8)} {handlers : Handlers layout} {world : World}
variable {state : Semantics.State RuntimeCallEffectsSemantics.State}

theorem ordinary_preserves
    (compiled : lowerBuiltin scope "call" expected arguments = .ok lowered)
    (computed : RuntimeCallEffectsSemantics.Call (fun _ => AccountCallSemantics.noChildren) .ordinary
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
    (stateRelated : StateRel (model layout baseline slots image handlers) world state store)
    (packed : Evaluates environment initial ((packArguments arguments).expression.rename mapping)
      (.inRight .word (bundleValues targets)) store) :
    ∃ resultValue final, ResultRel lowered.type result resultValue ∧
      Evaluates environment initial (lowered.expression.rename mapping) resultValue final ∧
      StateRel (model layout baseline slots image handlers) world {state with external := finalState} final ∧
      ClosuresPreserved store final := by
  obtain ⟨resultValue, final, resultRelated, evaluated, finalRelated, retained⟩ :=
    ChildCallBuiltinCorrespondence.ordinary_preserves compiled computed related runtime passive callPassive
      memoryMember memorySizeMember dataMember dataSizeMember handlerMember addressMember depthMember staticMember
      exitMember offsetMember sizeMember (RuntimeChildCallEffectsCorrespondence.empty_state stateRelated)
      (RuntimeChildCallEffectsCorrespondence.empty_callback layout handlers state.external (source_eq stateRelated)) packed
  exact ⟨resultValue, final, resultRelated, evaluated,
    RuntimeChildCallEffectsCorrespondence.base_related finalRelated, retained⟩

theorem static_preserves
    (compiled : lowerBuiltin scope "staticcall" expected arguments = .ok lowered)
    (computed : RuntimeCallEffectsSemantics.Call (fun _ => AccountCallSemantics.noChildren) .staticCall
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
    (stateRelated : StateRel (model layout baseline slots image handlers) world state store)
    (packed : Evaluates environment initial ((packArguments arguments).expression.rename mapping)
      (.inRight .word (bundleValues targets)) store) :
    ∃ resultValue final, ResultRel lowered.type result resultValue ∧
      Evaluates environment initial (lowered.expression.rename mapping) resultValue final ∧
      StateRel (model layout baseline slots image handlers) world {state with external := finalState} final ∧
      ClosuresPreserved store final := by
  obtain ⟨resultValue, final, resultRelated, evaluated, finalRelated, retained⟩ :=
    ChildCallBuiltinCorrespondence.static_preserves compiled computed related runtime _passive callPassive
      memoryMember memorySizeMember dataMember dataSizeMember handlerMember addressMember depthMember staticMember
      _exitMember _offsetMember _sizeMember (RuntimeChildCallEffectsCorrespondence.empty_state stateRelated)
      (RuntimeChildCallEffectsCorrespondence.empty_callback layout handlers state.external (source_eq stateRelated)) packed
  exact ⟨resultValue, final, resultRelated, evaluated,
    RuntimeChildCallEffectsCorrespondence.base_related finalRelated, retained⟩

end
end Solcore.Frontend.RustHull.CallBuiltinCorrespondence
end

section
-- leanmerge: from Solcore.Frontend.RustHull.CallModeBuiltinEvaluation
/-! Actual mode references supply the selected immutable handler and the caller
observation required by the independent message arguments. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.CallModeBuiltinCorrespondence
open Core Correspondence ScalarExecution EffectBuiltinCorrespondence
open RuntimeCallEffectsCorrespondence (Layout CallPassive)
open RuntimeChildCallEffectsCorrespondence (Anchors Context)
open RuntimeCallModeEffectsCorrespondence
open RuntimeCallModeSemantics (Operation)
open CallBuiltinCorrespondence (References invoke)

structure Inputs (references : References) (mapping : Renaming) (environment : Environment)
    (store : Store) (layout : Layout) (handlers : ModeHandlers layout) (operation : Operation) (state : RuntimeCallModeSemantics.State) : Prop where
  memory : Evaluates environment store (references.memory.rename mapping) (.cellRef WordMapping.type layout.memory) store
  memorySize : Evaluates environment store (references.memorySize.rename mapping) (.cellRef .word layout.storage.memorySize) store
  data : Evaluates environment store (references.returnData.rename mapping) (.cellRef WordMapping.type layout.returnData) store
  dataSize : Evaluates environment store (references.returnDataSize.rename mapping) (.cellRef .word layout.returnDataSize) store
  handler : Evaluates environment store (references.handler.rename mapping) (.cellRef (OptionalCell.cellType Calls.callbackType) (handlers.location operation)) store
  caller : Evaluates environment store ((Core.Expr.loadCell references.caller).rename mapping)
    (.word (if operation = .delegateCall then (RuntimeCallModeSemantics.observations state).direct .caller else state.runtime.runtime.runtime.runtime.runtime.storage.address)) store
  depth : Evaluates environment store ((Core.Expr.loadCell references.depth).rename mapping) (.word state.callDepth) store
  isStatic : Evaluates environment store ((Core.Expr.loadCell references.isStatic).rename mapping)
    (.bool state.runtime.runtime.runtime.runtime.runtime.storage.isStatic) store

theorem inputs {scope : Scope} {references : References} {handlerName callerName : String}
    (compiled : CompiledReferences scope handlerName callerName references)
    {slots : List EffectSlot} {mapping : Renaming} {environment : Environment}
    {layout : Layout} {baseline : Nat → Option Core.Value} {image : Option (List UInt8)} {handlers : ModeHandlers layout}
    {anchors : Anchors} {context : Context layout} {world : World}
    {state : Semantics.State RuntimeCallModeSemantics.State} {store : Store} {operation : Operation}
    (runtime : EffectEnvironmentRel slots scope mapping environment)
    (memoryMember : ⟨"memory", WordMapping.type, layout.memory⟩ ∈ slots)
    (memorySizeMember : ⟨"memorySize", .word, layout.storage.memorySize⟩ ∈ slots)
    (dataMember : ⟨"returnData", WordMapping.type, layout.returnData⟩ ∈ slots)
    (dataSizeMember : ⟨"returnDataSize", .word, layout.returnDataSize⟩ ∈ slots)
    (handlerMember : ⟨handlerName, OptionalCell.cellType Calls.callbackType, handlers.location operation⟩ ∈ slots)
    {callerLocation : Nat} (callerMember : ⟨callerName, .word, callerLocation⟩ ∈ slots)
    (callerRead : store.read? callerLocation = some (.word (if operation = .delegateCall then
      (RuntimeCallModeSemantics.observations state.external).direct .caller else state.external.runtime.runtime.runtime.runtime.runtime.storage.address)))
    (depthMember : ⟨"callDepth", .word, layout.callDepth⟩ ∈ slots)
    (staticMember : ⟨"isStatic", .bool, layout.storage.isStatic⟩ ∈ slots)
    (related : StateRel (model layout baseline slots image handlers anchors context) world state store) :
    Inputs references mapping environment store layout handlers operation state.external := by
  have storage := RuntimeEffectsCorrespondence.storage_related
    (RuntimeEnvironmentEffectsCorrespondence.runtime_related
    (RuntimeLogEffectsCorrespondence.runtime_related
    (RuntimeAccountEffectsCorrespondence.runtime_related (RuntimeCallEffectsCorrespondence.account_related (base_related related)))))
  exact ⟨reference_evaluates runtime memoryMember compiled.memory store,
    reference_evaluates runtime memorySizeMember compiled.memorySize store,
    reference_evaluates runtime dataMember compiled.returnData store,
    reference_evaluates runtime dataSizeMember compiled.returnDataSize store,
    reference_evaluates runtime handlerMember compiled.handler store,
    .loadCell (reference_evaluates runtime callerMember compiled.caller store) callerRead,
    .loadCell (reference_evaluates runtime depthMember compiled.depth store) (RuntimeCallEffectsCorrespondence.depth_related (base_related related)),
    .loadCell (reference_evaluates runtime staticMember compiled.isStatic store) storage.isStatic⟩

theorem Inputs.invoke_evaluates {references : References} {mapping : Renaming} {environment : Environment}
    {store : Store} {layout : Layout} {baseline : Nat → Option Value} {slots : List EffectSlot}
    {image : Option (List UInt8)} {handlers : ModeHandlers layout} {anchors : Anchors} {context : RuntimeChildCallEffectsCorrespondence.Context layout} {world : World}
    {children : RuntimeCallEffectsSemantics.State → AccountCallSemantics.Children}
    {state : Semantics.State RuntimeCallEffectsSemantics.State}
    {operation : Operation}
    (inputs : Inputs references mapping environment store layout handlers operation state.external)
    (passive : CallPassive layout slots)
    (related : StateRel (model layout baseline slots image handlers anchors context) world state store)
    (callback : CallbackPreservation layout handlers anchors context children operation state.external)
    {gas target value inputOffset inputLength outputOffset outputLength : Word}
    {result : Semantics.Result Semantics.Value} {next : CallTransportSemantics.State} {shared : AccountCallSemantics.Shared}
    (executed : CallTransportSemantics.Execute
      (AccountCallSemantics.Dispatch (children state.external) operation.mode state.external.runtime.runtime.runtime.runtime.runtime.storage.address)
      true (RuntimeCallModeSemantics.arguments operation state.external gas target value inputOffset inputLength outputOffset outputLength)
      (RuntimeCallEffectsSemantics.transport state.external) (RuntimeCallEffectsSemantics.shared state.external) result next shared)
    {staticExpr gasExpr targetExpr valueExpr inputOffsetExpr inputLengthExpr outputOffsetExpr outputLengthExpr : Core.Expr}
    (staticEvaluated : Evaluates environment store (staticExpr.rename mapping)
      (.bool (RuntimeCallModeSemantics.arguments operation state.external gas target value inputOffset inputLength outputOffset outputLength).isStatic) store)
    (gasEvaluated : Evaluates environment store (gasExpr.rename mapping)
      (.word (RuntimeCallModeSemantics.arguments operation state.external gas target value inputOffset inputLength outputOffset outputLength).gas) store)
    (targetEvaluated : Evaluates environment store (targetExpr.rename mapping) (.word target) store)
    (valueEvaluated : Evaluates environment store (valueExpr.rename mapping) (.word value) store)
    (inputOffsetEvaluated : Evaluates environment store (inputOffsetExpr.rename mapping) (.word inputOffset) store)
    (inputLengthEvaluated : Evaluates environment store (inputLengthExpr.rename mapping) (.word inputLength) store)
    (outputOffsetEvaluated : Evaluates environment store (outputOffsetExpr.rename mapping) (.word outputOffset) store)
    (outputLengthEvaluated : Evaluates environment store (outputLengthExpr.rename mapping) (.word outputLength) store) :
    ∃ resultValue final, ResultRel .word result resultValue ∧
      Evaluates environment store
        ((invoke references staticExpr gasExpr targetExpr valueExpr inputOffsetExpr inputLengthExpr outputOffsetExpr outputLengthExpr).rename mapping)
        resultValue final ∧
      StateRel (model layout baseline slots image handlers anchors context) world
        {state with external := RuntimeCallEffectsSemantics.withTransport state.external next shared} final ∧
      ClosuresPreserved store final := by
  have packed := Evaluates.pair inputs.memory (.pair inputs.memorySize (.pair inputs.data (.pair inputs.dataSize
    (.pair inputs.handler (.pair inputs.caller (.pair inputs.depth (.pair staticEvaluated (.pair gasEvaluated
    (.pair targetEvaluated (.pair valueEvaluated (.pair inputOffsetEvaluated (.pair inputLengthEvaluated
    (.pair outputOffsetEvaluated outputLengthEvaluated)))))))))))))
  obtain ⟨resultValue, final, resultRelated, evaluated, finalRelated, retained⟩ :=
    RuntimeCallModeEffectsCorrespondence.invoke_preserves executed passive related callback packed
  refine ⟨resultValue, final, resultRelated, ?_, finalRelated, retained⟩
  unfold invoke
  rw [CallTransportCorrespondence.invoke_rename]
  exact evaluated

end Solcore.Frontend.RustHull.CallModeBuiltinCorrespondence
end

section
-- leanmerge: from Solcore.Frontend.RustHull.CallModeBuiltinCorrespondence
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
end

section
-- leanmerge: from Solcore.Frontend.RustHull.LifecycleBuiltinCompiler
/-! Successful SELFDESTRUCT lowering resolves account references and both
termination branches before it emits the static guard and shared updates. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.LifecycleBuiltinCorrespondence
open Core Correspondence PureCallCorrespondence EffectBuiltinCorrespondence

structure References where
  world : Core.Expr
  balances : Core.Expr
  address : Core.Expr
  complete : Core.Expr
  isStatic : Core.Expr

structure CompiledReferences (scope : Scope) (references : References) : Prop where
  world : Effects.reference scope "world" AccountState.type = .ok references.world
  balances : Effects.reference scope "balances" WordMapping.type = .ok references.balances
  address : Effects.reference scope "address" .word = .ok references.address
  complete : Effects.reference scope "worldComplete" .bool = .ok references.complete
  isStatic : Effects.reference scope "isStatic" .bool = .ok references.isStatic

def expression (references : References) (beneficiary invalid stopped : Core.Expr) : Core.Expr :=
  .ifE (.loadCell references.isStatic) invalid
    (LocalSequence.discard .unit
      (AccountLifecycle.destroy references.world references.balances (.loadCell references.address)
        beneficiary (.loadCell references.complete)) stopped)

theorem inner_arity {scope : Scope} {arguments : List Core.Expr} {lowered : Lowered}
    (compiled : Effects.lowerBuiltin scope "selfdestruct" arguments = .ok lowered) :
    arguments.length = 1 := by
  rcases arguments with _ | ⟨first, _ | ⟨second, rest⟩⟩
  all_goals first
    | rfl
    | change Except.error _ = Except.ok lowered at compiled
      cases compiled

theorem inner_components {scope : Scope} {beneficiary : Core.Expr} {lowered : Lowered}
    (compiled : Effects.lowerBuiltin scope "selfdestruct" [beneficiary] = .ok lowered) :
    ∃ references invalid stopped, CompiledReferences scope references ∧
      Effects.terminate scope 3 (.word Word.zero) (.word Word.zero) = .ok invalid ∧
      Effects.terminate scope 1 (.word Word.zero) (.word Word.zero) = .ok stopped ∧
      lowered = ⟨.unit, expression references beneficiary invalid stopped⟩ := by
  change (do
    let world ← Effects.reference scope "world" AccountState.type
    let balances ← Effects.reference scope "balances" WordMapping.type
    let address ← Effects.reference scope "address" .word
    let complete ← Effects.reference scope "worldComplete" .bool
    let isStatic ← Effects.reference scope "isStatic" .bool
    let invalid ← Effects.terminate scope 3 (.word Word.zero) (.word Word.zero)
    let stopped ← Effects.terminate scope 1 (.word Word.zero) (.word Word.zero)
    pure (Lowered.mk .unit (expression ⟨world, balances, address, complete, isStatic⟩ beneficiary invalid stopped))) = .ok lowered at compiled
  obtain ⟨world, worldCompiled, compiled⟩ := lower_bind_eq_ok.mp compiled
  obtain ⟨balances, balancesCompiled, compiled⟩ := lower_bind_eq_ok.mp compiled
  obtain ⟨address, addressCompiled, compiled⟩ := lower_bind_eq_ok.mp compiled
  obtain ⟨complete, completeCompiled, compiled⟩ := lower_bind_eq_ok.mp compiled
  obtain ⟨isStatic, staticCompiled, compiled⟩ := lower_bind_eq_ok.mp compiled
  obtain ⟨invalid, invalidCompiled, compiled⟩ := lower_bind_eq_ok.mp compiled
  obtain ⟨stopped, stoppedCompiled, returned⟩ := lower_bind_eq_ok.mp compiled
  exact ⟨⟨world, balances, address, complete, isStatic⟩, invalid, stopped,
    ⟨worldCompiled, balancesCompiled, addressCompiled, completeCompiled, staticCompiled⟩,
    invalidCompiled, stoppedCompiled, (Except.ok.inj returned).symm⟩

def References.rename (references : References) (mapping : Renaming) : References :=
  ⟨references.world.rename mapping, references.balances.rename mapping, references.address.rename mapping,
    references.complete.rename mapping, references.isStatic.rename mapping⟩

open CodeBuilder in
private def destroyCode (worldReference balancesReference currentAddress beneficiary complete : Core.Expr) : Core.Expr :=
  (bind (constant (bundle [worldReference, balancesReference, currentAddress, beneficiary, complete])) fun args =>
    let world := part 0 5 args
    let balances := part 1 5 args
    bind (address (part 2 5 args)) fun current =>
    bind (address (part 3 5 args)) fun recipient =>
    bindResult .unit (fun depth => AccountState.get (load world depth) (current depth)
      (part 4 5 args depth)) fun record =>
    let finish := AccountLifecycleCorrespondence.publishCode world balances current record
    bindResult .unit (lookup (load balances) current) fun amount =>
    choose (binary .wordEq current recipient)
      (choose (part 7 9 record)
        (choose (binary .wordEq amount (number 0)) (finish (load balances))
          (bindResult .unit (insert (load balances) current (number 0)) finish))
        (success unit))
      (choose (binary .wordEq amount (number 0)) (finish (load balances))
        (bindResult .unit (lookup (load balances) recipient) fun recipientBalance =>
          choose (binary .wordGt recipientBalance (binary .wordSub (number (wordModulus - 1)) amount))
            (failure .unit (constant (.word AccountLifecycle.balanceOverflowReason)))
            (bindResult .unit (insert (load balances) current (number 0)) fun debited =>
              bindResult .unit (insert debited recipient (binary .wordAdd recipientBalance amount)) finish)))) 0


set_option linter.unusedSimpArgs false in
set_option maxRecDepth 10000 in
set_option maxHeartbeats 800000 in
theorem destroy_rename (world balances address beneficiary complete : Core.Expr) (mapping : Renaming) :
    (AccountLifecycle.destroy world balances address beneficiary complete).rename mapping =
      AccountLifecycle.destroy (world.rename mapping) (balances.rename mapping) (address.rename mapping)
        (beneficiary.rename mapping) (complete.rename mapping) := by
  change (destroyCode world balances address beneficiary complete).rename mapping =
    destroyCode (world.rename mapping) (balances.rename mapping) (address.rename mapping)
      (beneficiary.rename mapping) (complete.rename mapping)
  simp only [destroyCode, CodeBuilder.bind, CodeBuilder.constant, bundle, Core.Expr.rename]
  congr 1
  simp [CodeBuilder.bind, CodeBuilder.bindResult, CodeBuilder.part, CodeBuilder.load,
    CodeBuilder.address, CodeBuilder.binary, CodeBuilder.number, CodeBuilder.constant,
    CodeBuilder.choose, CodeBuilder.success, CodeBuilder.failure, CodeBuilder.boolean,
    CodeBuilder.lookup, CodeBuilder.insert, CodeBuilder.store, CodeBuilder.unit, projectArgument,
    AccountState.get, AccountState.lookup, AccountState.defaultRecord, AccountState.put,
    AccountLifecycleCorrespondence.publishCode, AccountState.replace, AccountState.field, bundle, LanguageResult.bind, LanguageResult.success, LanguageResult.failure,
    OrderedMapping.lookup, OrderedMapping.lookupBody, OrderedMapping.optionValue, OrderedMapping.invoke,
    OrderedMapping.runHelper, WordMapping.lookup, WordMapping.lookupBody, WordMapping.insert,
    WordMapping.insertBody, WordMapping.runHelper, WordMapping.invoke, WordMapping.empty, WordMapping.cons,
    OrderedMapping.insert, OrderedMapping.insertBody, OrderedMapping.cons,
    AccountState.equal, OptionalCell.allocate, OptionalCell.read, Core.Expr.rename, Core.Expr.renameList,
    Core.Renaming.lift, Core.Expr.weakenAt]
  all_goals (repeat' apply And.intro)
  all_goals rfl

theorem expression_rename (references : References) (beneficiary invalid stopped : Core.Expr) (mapping : Renaming) :
    (expression references beneficiary invalid stopped).rename mapping =
      expression (references.rename mapping) (beneficiary.rename mapping) (invalid.rename mapping) (stopped.rename mapping) := by
  simp only [expression, Core.Expr.rename, LocalSequence.discard, LanguageResult.bind,
    destroy_rename, References.rename]
  congr 2
  rw [← Core.Expr.rename_insertion, ← Core.Expr.rename_insertion, Core.Expr.rename_comp, Core.Expr.rename_comp]
  congr 1

end Solcore.Frontend.RustHull.LifecycleBuiltinCorrespondence
end

section
-- leanmerge: from Solcore.Frontend.RustHull.LifecycleBuiltinInputs
/-! SELFDESTRUCT references use the actual caller account, world and ledger
cells supplied by runtime initialization. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.LifecycleBuiltinCorrespondence
open Core Correspondence ScalarExecution EffectBuiltinCorrespondence
open RuntimeCallEffectsCorrespondence (Layout)
open RuntimeCallModeEffectsCorrespondence (ModeHandlers model base_related)
open RuntimeChildCallEffectsCorrespondence (Anchors Context)

structure Inputs (references : References) (mapping : Renaming) (environment : Environment)
    (store : Store) (layout : Layout) (state : RuntimeCallEffectsSemantics.State) : Prop where
  world : Evaluates environment store (references.world.rename mapping) (.cellRef AccountState.type layout.storage.world) store
  balances : Evaluates environment store (references.balances.rename mapping) (.cellRef WordMapping.type layout.balances) store
  address : Evaluates environment store ((Core.Expr.loadCell references.address).rename mapping)
    (.word state.runtime.runtime.runtime.runtime.runtime.storage.address) store
  complete : Evaluates environment store ((Core.Expr.loadCell references.complete).rename mapping)
    (.bool state.runtime.runtime.runtime.runtime.runtime.storage.complete) store
  isStatic : Evaluates environment store ((Core.Expr.loadCell references.isStatic).rename mapping)
    (.bool state.runtime.runtime.runtime.runtime.runtime.storage.isStatic) store

theorem inputs {scope : Scope} {references : References} (compiled : CompiledReferences scope references)
    {slots : List EffectSlot} {mapping : Renaming} {environment : Environment}
    {layout : Layout} {baseline : Nat → Option Value} {image : Option (List UInt8)} {handlers : ModeHandlers layout}
    {anchors : Anchors} {context : Context layout} {world : World}
    {state : Semantics.State RuntimeCallEffectsSemantics.State} {store : Store}
    (runtime : EffectEnvironmentRel slots scope mapping environment)
    (worldMember : ⟨"world", AccountState.type, layout.storage.world⟩ ∈ slots)
    (balancesMember : ⟨"balances", WordMapping.type, layout.balances⟩ ∈ slots)
    (addressMember : ⟨"address", .word, layout.storage.address⟩ ∈ slots)
    (completeMember : ⟨"worldComplete", .bool, layout.storage.complete⟩ ∈ slots)
    (staticMember : ⟨"isStatic", .bool, layout.storage.isStatic⟩ ∈ slots)
    (related : StateRel (model layout baseline slots image handlers anchors context) world state store) :
    Inputs references mapping environment store layout state.external := by
  have storage := RuntimeEffectsCorrespondence.storage_related
    (RuntimeEnvironmentEffectsCorrespondence.runtime_related
    (RuntimeLogEffectsCorrespondence.runtime_related
    (RuntimeAccountEffectsCorrespondence.runtime_related (RuntimeCallEffectsCorrespondence.account_related (base_related related)))))
  exact ⟨reference_evaluates runtime worldMember compiled.world store,
    reference_evaluates runtime balancesMember compiled.balances store,
    .loadCell (reference_evaluates runtime addressMember compiled.address store) storage.address,
    .loadCell (reference_evaluates runtime completeMember compiled.complete store) storage.complete,
    .loadCell (reference_evaluates runtime staticMember compiled.isStatic store) storage.isStatic⟩

end Solcore.Frontend.RustHull.LifecycleBuiltinCorrespondence
end

section
-- leanmerge: from Solcore.Frontend.RustHull.LifecycleBuiltinCorrespondence
/-! SELFDESTRUCT follows the actual static guard, account update and stopping
branch. Shared state, catalog identities and installed callbacks remain related. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.LifecycleBuiltinCorrespondence
open Core Correspondence ScalarExecution PureCallCorrespondence EffectBuiltinCorrespondence
open RuntimeCallEffectsCorrespondence (Layout CallPassive)
open RuntimeCallModeEffectsCorrespondence (ModeHandlers model base_related)
open RuntimeChildCallEffectsCorrespondence (Anchors Context)

private def destruction (state : RuntimeLifecycleSemantics.State) (beneficiary : Word) :
    Except Word (StorageSemantics.World × StorageSemantics.Words) :=
  AccountLifecycleSemantics.destroy state.runtime.runtime.runtime.runtime.runtime.storage.world
    state.runtime.runtime.balances state.runtime.runtime.runtime.runtime.runtime.storage.address beneficiary
    state.runtime.runtime.runtime.runtime.runtime.storage.complete

private def afterDestruction (state : RuntimeLifecycleSemantics.State) :
    Except Word (StorageSemantics.World × StorageSemantics.Words) → RuntimeLifecycleSemantics.State
  | .error _ => state
  | .ok next => RuntimeLifecycleSemantics.updated state next.1 next.2

private theorem Inputs.destroy_evaluates
    {references : References} {mapping : Renaming} {environment : Environment} {store : Store}
    {layout : Layout} {baseline : Nat → Option Value} {slots : List EffectSlot}
    {image : Option (List UInt8)} {handlers : ModeHandlers layout} {anchors : Anchors} {context : Context layout}
    {world : World} {state : Semantics.State RuntimeLifecycleSemantics.State}
    {beneficiary : Word} {beneficiaryExpr : Core.Expr}
    (inputs : Inputs references mapping environment store layout state.external)
    (passive : CallPassive layout slots)
    (before : StateRel (model layout baseline slots image handlers anchors context) world state store)
    (supplied : Evaluates environment store beneficiaryExpr (.word beneficiary) store) :
    ∃ final, Evaluates environment store
      (AccountLifecycle.destroy (references.world.rename mapping) (references.balances.rename mapping)
        ((Core.Expr.loadCell references.address).rename mapping) beneficiaryExpr
        ((Core.Expr.loadCell references.complete).rename mapping))
      (StorageCorrespondence.unitResult (destruction state.external beneficiary)) final ∧
      StateRel (model layout baseline slots image handlers anchors context) world
        {state with external := afterDestruction state.external (destruction state.external beneficiary)} final ∧
      ClosuresPreserved store final := by
  obtain ⟨accounts, same, linked, worldRead⟩ := RuntimeChildCallEffectsCorrespondence.linked_related before
  have shared := (RuntimeCallEffectsCorrespondence.shared_resources (base_related before)).1
  have separate : layout.storage.world ≠ layout.balances := by
    have distinct := shared.distinct
    simp only [AccountCallCorrespondence.SharedLocations.all, RuntimeCallEffectsCorrespondence.sharedLocations,
      List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at distinct
    exact distinct.1.2.2.1
  obtain ⟨final, evaluated, finalWorld, finalBalances, frame⟩ :=
    AccountLifecycleCorrespondence.destroy_preserves accounts state.external.runtime.runtime.balances
      layout.storage.world layout.balances state.external.runtime.runtime.runtime.runtime.runtime.storage.address
      beneficiary state.external.runtime.runtime.runtime.runtime.runtime.storage.complete
      (.pair inputs.world (.pair inputs.balances (.pair inputs.address (.pair supplied inputs.complete))))
      worldRead shared.balances separate
  have projected := AccountLifecycleCorrespondence.destroy_source accounts state.external.runtime.runtime.balances
    state.external.runtime.runtime.runtime.runtime.runtime.storage.address beneficiary
    state.external.runtime.runtime.runtime.runtime.runtime.storage.complete
  change accounts.map Prod.fst = state.external.runtime.runtime.runtime.runtime.runtime.storage.world at same
  rw [same] at projected
  change _ = destruction state.external beneficiary at projected
  have finalLinked := AccountLifecycleCorrespondence.destroy_links linked state.external.runtime.runtime.balances
    state.external.runtime.runtime.runtime.runtime.runtime.storage.address beneficiary
    state.external.runtime.runtime.runtime.runtime.runtime.storage.complete
  cases outcome : AccountLifecycleCorrespondence.destroyAccounts accounts state.external.runtime.runtime.balances
      state.external.runtime.runtime.runtime.runtime.runtime.storage.address beneficiary
      state.external.runtime.runtime.runtime.runtime.runtime.storage.complete with
  | error reason =>
      have source : destruction state.external beneficiary = .error reason := by simpa only [outcome, Except.map] using projected.symm
      simp only [outcome, AccountLifecycleCorrespondence.nextAccounts, AccountLifecycleCorrespondence.nextBalances] at evaluated finalWorld finalBalances finalLinked
      obtain ⟨related, retained⟩ := RuntimeLifecycleCorrespondence.updated_preserves passive before
        ⟨accounts, same, finalLinked, finalWorld⟩ finalBalances frame
      refine ⟨final, ?_, ?_, retained⟩
      · simpa only [source, Core.Expr.rename, StorageCorrespondence.unitResult] using evaluated
      · simpa only [source, afterDestruction, RuntimeLifecycleSemantics.updated, RuntimeCallEffectsSemantics.withShared, RuntimeCallEffectsSemantics.shared] using related
  | ok next =>
      rcases next with ⟨nextAccounts, nextBalances⟩
      have source : destruction state.external beneficiary = .ok (nextAccounts.map Prod.fst, nextBalances) := by
        simpa only [outcome, Except.map] using projected.symm
      simp only [outcome, AccountLifecycleCorrespondence.nextAccounts, AccountLifecycleCorrespondence.nextBalances] at evaluated finalWorld finalBalances finalLinked
      obtain ⟨related, retained⟩ := RuntimeLifecycleCorrespondence.updated_preserves passive before
        ⟨nextAccounts, rfl, finalLinked, finalWorld⟩ finalBalances frame
      refine ⟨final, ?_, ?_, retained⟩
      · simpa only [source, StorageCorrespondence.unitResult, Core.Expr.rename] using evaluated
      · simpa only [source, afterDestruction, RuntimeLifecycleSemantics.updated, RuntimeCallEffectsSemantics.withShared, RuntimeCallEffectsSemantics.shared] using related

/-- Actual lowering, source destruction and evaluated arguments determine the
Core result and the complete related runtime state. -/
theorem preserves {scope : Scope} {expected : Core.Ty} {arguments : List Lowered} {lowered : Lowered}
    {beneficiary : Word} {result : Semantics.Result Semantics.Value} {finalState : RuntimeLifecycleSemantics.State}
    {targets : List Core.Value} {slots : List EffectSlot} {mapping : Renaming} {environment : Environment}
    {initial store : Store} {layout : Layout} {baseline : Nat → Option Value}
    {image : Option (List UInt8)} {handlers : ModeHandlers layout} {anchors : Anchors} {context : Context layout}
    {world : World} {state : Semantics.State RuntimeLifecycleSemantics.State}
    (compiled : lowerBuiltin scope "selfdestruct" expected arguments = .ok lowered)
    (computed : RuntimeLifecycleSemantics.Destroy beneficiary state.external result finalState)
    (related : ArgumentsRel arguments [.word beneficiary] targets)
    (runtime : EffectEnvironmentRel slots scope mapping environment)
    (passive : RuntimeLogEffectsCorrespondence.Passive layout.toLogLayout slots)
    (callPassive : CallPassive layout slots)
    (worldMember : ⟨"world", AccountState.type, layout.storage.world⟩ ∈ slots)
    (balancesMember : ⟨"balances", WordMapping.type, layout.balances⟩ ∈ slots)
    (addressMember : ⟨"address", .word, layout.storage.address⟩ ∈ slots)
    (completeMember : ⟨"worldComplete", .bool, layout.storage.complete⟩ ∈ slots)
    (staticMember : ⟨"isStatic", .bool, layout.storage.isStatic⟩ ∈ slots)
    (memorySizeMember : ⟨"memorySize", .word, layout.storage.memorySize⟩ ∈ slots)
    (exitMember : ⟨"exit", .word, layout.storage.exit⟩ ∈ slots)
    (offsetMember : ⟨"returnOffset", .word, layout.storage.returnOffset⟩ ∈ slots)
    (sizeMember : ⟨"returnSize", .word, layout.storage.returnSize⟩ ∈ slots)
    (stateRelated : StateRel (model layout baseline slots image handlers anchors context) world state store)
    (packed : Evaluates environment initial ((packArguments arguments).expression.rename mapping)
      (.inRight .word (bundleValues targets)) store) :
    ∃ resultValue final, ResultRel lowered.type result resultValue ∧
      Evaluates environment initial (lowered.expression.rename mapping) resultValue final ∧
      StateRel (model layout baseline slots image handlers anchors context) world {state with external := finalState} final ∧
      ClosuresPreserved store final := by
  obtain ⟨words, raw, rawCompiled, typed, loweredEqual⟩ := outer_components rfl compiled
  have arity : arguments.length = 1 := by
    simpa only [List.length_map, List.length_range] using inner_arity rawCompiled
  obtain ⟨beneficiaryExpr, input, rfl, same, rfl⟩ := one_word related words arity
  cases same
  obtain ⟨references, invalid, stopped, referencesCompiled, invalidCompiled, stoppedCompiled, rfl⟩ := inner_components rawCompiled
  cases typed
  cases loweredEqual
  have runtime' := runtime.temporary .word (.word beneficiary)
  have observed := inputs referencesCompiled runtime' worldMember balancesMember addressMember completeMember staticMember stateRelated
  have supplied : Evaluates (.word beneficiary :: environment) store
      ((projectArgument 0 1 (.var 0)).rename mapping.lift) (.word beneficiary) store := .var rfl
  cases computed with
  | staticFrame isStatic =>
      obtain ⟨target, final, resultRelated, evaluated, finalRelated, retained⟩ :=
        RuntimeLifecycleCorrespondence.terminate_preserves invalidCompiled runtime' passive
          memorySizeMember exitMember offsetMember sizeMember stateRelated
      refine ⟨target, final, resultRelated, ?_, finalRelated, retained⟩
      apply LanguageResult.bind_success .unit packed
      rw [expression_rename]
      exact .ifTrue (by simpa only [isStatic, Core.Expr.rename, References.rename, bundleValues] using observed.isStatic) evaluated
  | rejected reason notStatic destroyed =>
      obtain ⟨final, evaluated, finalRelated, retained⟩ := observed.destroy_evaluates callPassive stateRelated supplied
      change destruction state.external beneficiary = .error reason at destroyed
      simp only [destroyed, afterDestruction, StorageCorrespondence.unitResult] at evaluated finalRelated
      refine ⟨.inLeft .unit (.word reason), final, .language _, ?_, finalRelated, retained⟩
      apply LanguageResult.bind_success .unit packed
      rw [expression_rename]
      apply Evaluates.ifFalse (by simpa only [notStatic, Core.Expr.rename, References.rename, bundleValues] using observed.isStatic)
      exact LocalSequence.discard_failure .unit evaluated
  | completed nextWorld nextBalances notStatic destroyed =>
      obtain ⟨middle, evaluated, middleRelated, firstRetained⟩ := observed.destroy_evaluates callPassive stateRelated supplied
      change destruction state.external beneficiary = .ok (nextWorld, nextBalances) at destroyed
      simp only [destroyed, afterDestruction, StorageCorrespondence.unitResult] at evaluated middleRelated
      obtain ⟨target, final, resultRelated, stoppedEvaluated, finalRelated, secondRetained⟩ :=
        RuntimeLifecycleCorrespondence.terminate_preserves stoppedCompiled (runtime'.prepend [.unit]) passive
          memorySizeMember exitMember offsetMember sizeMember middleRelated
      refine ⟨target, final, resultRelated, ?_, finalRelated, firstRetained.trans secondRetained⟩
      apply LanguageResult.bind_success .unit packed
      rw [expression_rename]
      apply Evaluates.ifFalse (by simpa only [notStatic, Core.Expr.rename, References.rename, bundleValues] using observed.isStatic)
      apply LocalSequence.discard_success .unit evaluated
      rw [← Core.Expr.rename_insertion, Core.Expr.rename_comp]
      have shifted : ((Renaming.insertion 0).comp mapping.lift) = (fun index => 1 + mapping.lift index) := by
        funext index
        simp [Renaming.comp, Renaming.insertion, Nat.add_comm]
      rw [shifted]
      exact stoppedEvaluated

end Solcore.Frontend.RustHull.LifecycleBuiltinCorrespondence
end

section
-- leanmerge: from Solcore.Frontend.RustHull.RevertBuiltinCorrespondence
/-! Hull's explicit revert through the actual `Effects.revertMessage` code. The
message word the lowering computes is the specified left-aligned word, the
actual `mstore` code writes it at offset zero, and the actual revert
termination records the exit and the message range. The frame model, catalog
links and captured context survive. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.RevertBuiltinCorrespondence
open Core Correspondence ScalarExecution EffectBuiltinCorrespondence
open RuntimeCallEffectsCorrespondence (Layout Handlers account_related runtime_related)
open RuntimeChildCallEffectsCorrespondence

theorem foldl_value (bytes : List UInt8) (accumulator : Nat) :
    bytes.foldl (fun value byte => value * 256 + byte.toNat) accumulator =
      accumulator * 256 ^ bytes.length + RevertSemantics.bytesValue bytes := by
  induction bytes generalizing accumulator with
  | nil => simp [RevertSemantics.bytesValue]
  | cons byte rest ih =>
      rw [List.foldl_cons, ih, RevertSemantics.bytesValue, List.length_cons, Nat.pow_succ, Nat.add_mul,
        Nat.mul_assoc, Nat.mul_comm 256 (256 ^ rest.length), Nat.add_assoc]

theorem store_components {scope : Scope} {offset value : Core.Expr} {lowered : Lowered}
    (compiled : Effects.lowerBuiltin scope "mstore" [offset, value] = .ok lowered) :
    ∃ memory size, Effects.reference scope "memory" WordMapping.type = .ok memory ∧
      Effects.reference scope "memorySize" .word = .ok size ∧
      lowered = ⟨.unit, Memory.mstore memory size offset value⟩ := by
  change (do
    let raw ← (do
      let memory ← Effects.reference scope "memory" WordMapping.type
      let size ← Effects.reference scope "memorySize" .word
      pure (Lowered.mk .unit (Memory.mstore memory size offset value)) : LowerM Lowered)
    pure raw) = .ok lowered at compiled
  obtain ⟨memory, memoryCompiled, compiled⟩ := lower_bind_eq_ok.mp compiled
  obtain ⟨size, sizeCompiled, returned⟩ := lower_bind_eq_ok.mp compiled
  exact ⟨memory, size, memoryCompiled, sizeCompiled, (Except.ok.inj returned).symm⟩

private theorem revert_components {scope : Scope} {offset length : Core.Expr} {lowered : Lowered}
    (compiled : Effects.lowerBuiltin scope "revert" [offset, length] = .ok lowered) :
    ∃ expression, Effects.terminate scope 2 offset length = .ok expression ∧ lowered = ⟨.unit, expression⟩ := by
  have expanded : Effects.lowerBuiltin scope "revert" [offset, length] = (do
      let raw ← (do
        let expression ← Effects.terminate scope 2 offset length
        pure (Lowered.mk .unit expression) : LowerM Lowered)
      pure raw) := rfl
  rw [expanded] at compiled
  obtain ⟨expression, terminated, returned⟩ := lower_bind_eq_ok.mp compiled
  exact ⟨expression, terminated, (Except.ok.inj returned).symm⟩

/-- The accepted revert writes the specified message word and exits through
the revert termination over the message bytes. -/
theorem message_components {scope : Scope} {message : String} {exit : Core.Expr}
    (compiled : Effects.revertMessage scope message = .ok exit) :
    ∃ memory size halt, Effects.reference scope "memory" WordMapping.type = .ok memory ∧
      Effects.reference scope "memorySize" .word = .ok size ∧
      Effects.terminate scope 2 (.word Word.zero) (.word (RevertSemantics.messageLength message)) = .ok halt ∧
      exit = LocalSequence.discard .unit
        (Memory.mstore memory size (.word Word.zero) (.word (RevertSemantics.messageWord message))) halt := by
  unfold Effects.revertMessage at compiled
  dsimp only at compiled
  split at compiled
  · cases compiled
  · obtain ⟨write, writeCompiled, compiled⟩ := lower_bind_eq_ok.mp compiled
    obtain ⟨halted, haltCompiled, returned⟩ := lower_bind_eq_ok.mp compiled
    obtain ⟨memory, size, memoryCompiled, sizeCompiled, rfl⟩ := store_components writeCompiled
    obtain ⟨halt, terminated, rfl⟩ := revert_components haltCompiled
    refine ⟨memory, size, halt, memoryCompiled, sizeCompiled, terminated, ?_⟩
    rw [← Except.ok.inj returned]
    simp only [RevertSemantics.messageWord, ← Array.foldl_toList, foldl_value, Nat.zero_mul, Nat.zero_add]

theorem weaken_rename (expression : Core.Expr) (mapping : Renaming) :
    (expression.weakenAt 0).rename mapping.lift =
      expression.rename (fun index => [Value.unit].length + mapping index) := by
  rw [← Core.Expr.rename_insertion, Core.Expr.rename_comp]
  congr 1
  funext index
  change mapping index + 1 = [Value.unit].length + mapping index
  simp only [List.length_cons, List.length_nil]
  omega

theorem exit_rename (memory size halt : Core.Expr) (word : Word) (mapping : Renaming) :
    (LocalSequence.discard .unit (Memory.mstore memory size (.word Word.zero) (.word word)) halt).rename mapping =
      LanguageResult.bind .unit (Memory.mstore (memory.rename mapping) (size.rename mapping) (.word Word.zero) (.word word))
        ((halt.weakenAt 0).rename mapping.lift) := by
  rw [LocalSequence.discard, LanguageResult.bind, Core.Expr.rename, MemoryCorrespondence.mstore_rename]
  rfl

theorem world_separate (layout : RuntimeEffectsCorrespondence.Layout) :
    layout.storage.world ≠ layout.memory ∧ layout.storage.world ≠ layout.storage.memorySize ∧
      layout.storage.exit ≠ layout.storage.world ∧ layout.storage.returnOffset ≠ layout.storage.world ∧
      layout.storage.returnSize ≠ layout.storage.world := by
  have distinct := layout.distinct
  simp only [StorageBuiltinCorrespondence.Locations.all, List.nodup_cons, List.mem_cons,
    List.not_mem_nil, or_false, not_or] at distinct
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp_all [ne_comm]

/-- The revert termination writes only the memory size and the exit registers,
so the world cell survives. -/
theorem finalStore_world {layout : RuntimeEffectsCorrespondence.Layout}
    {state : RuntimeEffectsSemantics.State} {kind : Nat} {offset length : Word} {store : Store} {value : Value}
    (found : store.read? layout.storage.world = some value) :
    (TerminationBuiltinCorrespondence.finalStore layout.storage state kind offset length store).read?
      layout.storage.world = some value := by
  obtain ⟨_, notSize, notExit, notOffset, notLength⟩ := world_separate layout
  unfold TerminationBuiltinCorrespondence.finalStore
  split
  · exact found
  · simp only [TerminationBuiltinCorrespondence.finishStore, Store.read?]
    rw [List.getElem?_set_ne notExit, List.getElem?_set_ne notLength, List.getElem?_set_ne notOffset]
    exact (MemoryCorrespondence.touchStore_other store notSize _ _ _).trans found

section
variable {slots : List EffectSlot} {mapping : Renaming} {environment : Environment} {store : Store}
variable {layout : Layout} {baseline : Nat → Option Value} {image : Option (List UInt8)}
variable {handlers : Handlers layout} {anchors : Anchors} {context : Context layout} {world : World}
variable {state : Semantics.State RuntimeCallEffectsSemantics.State}

/-- Hull's explicit revert simulates its actual lowering in the frame model:
the exit code fails with the termination reason, and the message write and
exit registers are published. -/
theorem preserves (passive : RuntimeLogEffectsCorrespondence.Passive layout.toLogLayout slots)
    (memoryMember : ⟨"memory", WordMapping.type, layout.memory⟩ ∈ slots)
    (memorySizeMember : ⟨"memorySize", .word, layout.storage.memorySize⟩ ∈ slots)
    (exitMember : ⟨"exit", .word, layout.storage.exit⟩ ∈ slots)
    (offsetMember : ⟨"returnOffset", .word, layout.storage.returnOffset⟩ ∈ slots)
    (sizeMember : ⟨"returnSize", .word, layout.storage.returnSize⟩ ∈ slots)
    {message : String} {control : Semantics.Control} {final : RuntimeCallEffectsSemantics.State}
    (reverted : RevertSemantics.Reverted message state.external control final)
    {scope : Scope} {exit : Core.Expr} (compiled : Effects.revertMessage scope message = .ok exit)
    (runtime : EffectEnvironmentRel slots scope mapping environment)
    (stateRelated : StateRel (model layout baseline slots image handlers anchors context) world state store) :
    ∃ reason finalStore, control = .fault (.language reason) ∧
      Evaluates environment store (exit.rename mapping) (.inLeft .unit (.word reason)) finalStore ∧
      StateRel (model layout baseline slots image handlers anchors context) world {state with external := final}
        finalStore ∧
      ClosuresPreserved store finalStore := by
  cases reverted with
  | reverted fits stored terminated =>
  rename_i memory fault halted
  obtain ⟨memoryReference, sizeReference, halt, memoryCompiled, sizeCompiled, haltCompiled, rfl⟩ :=
    message_components compiled
  have base := base_related stateRelated
  have beforeRuntime := RuntimeEnvironmentEffectsCorrespondence.runtime_related
    (RuntimeLogEffectsCorrespondence.runtime_related (RuntimeAccountEffectsCorrespondence.runtime_related (account_related base)))
  have memoryBefore : MemoryCorrespondence.StateRel layout.memory layout.storage.memorySize
      state.external.runtime.runtime.runtime.runtime.runtime.memory store :=
    RuntimeEffectsCorrespondence.memory_related beforeRuntime
  have storageBefore : StorageBuiltinCorrespondence.StateRel layout.storage
      state.external.runtime.runtime.runtime.runtime.runtime.storage store :=
    RuntimeEffectsCorrespondence.storage_related beforeRuntime
  -- the message word at offset zero
  obtain ⟨storedResult, memoryStored, storedFrame⟩ := MemoryCorrespondence.mstore_preserves memoryBefore Word.zero
    (RevertSemantics.messageWord message) environment
  rw [stored] at storedResult memoryStored
  have mstoreEvaluated := MemoryCorrespondence.mstore_evaluates (environment := environment) (initial := store)
    (first := store) (second := store) (third := store) (store := store)
    state.external.runtime.runtime.runtime.runtime.runtime.memory Word.zero (RevertSemantics.messageWord message)
    (reference_evaluates runtime memoryMember memoryCompiled store)
    (reference_evaluates runtime memorySizeMember sizeCompiled store) .word .word
    memoryBefore.memory memoryBefore.size memoryBefore.distinct
  generalize MemoryCorrespondence.mstoreResult state.external.runtime.runtime.runtime.runtime.runtime.memory Word.zero =
    storedValue at storedResult mstoreEvaluated
  generalize MemoryCorrespondence.mstoreStore store layout.memory layout.storage.memorySize
    state.external.runtime.runtime.runtime.runtime.runtime.memory Word.zero (RevertSemantics.messageWord message)
    environment = storedStore at memoryStored storedFrame mstoreEvaluated
  cases storedResult with
  | value related =>
  cases related
  -- the revert exit over the message bytes
  have storageStored := RuntimeEffectsCorrespondence.memory_preserves_storage storageBefore storedFrame
  have haltEvaluated := TerminationBuiltinCorrespondence.terminate_evaluates haltCompiled (runtime.prepend [.unit])
    memorySizeMember exitMember offsetMember sizeMember
    (state := {state.external.runtime.runtime.runtime.runtime.runtime with memory := memory})
    storageStored memoryStored.size Word.zero (RevertSemantics.messageLength message) (fun _ _ => .word) (fun _ _ => .word)
  obtain ⟨haltResult, memoryFinal, storageFinal, haltFrame⟩ := TerminationBuiltinCorrespondence.terminate_state
    (state := {state.external.runtime.runtime.runtime.runtime.runtime with memory := memory})
    memoryStored storageStored 2 Word.zero (RevertSemantics.messageLength message)
  rw [terminated] at haltResult memoryFinal storageFinal
  have storedClosures : ClosuresPreserved store storedStore :=
    MemoryEffectCorrespondence.closures_preserved memoryBefore storedFrame
  have haltClosures : ClosuresPreserved _ _ := TerminationBuiltinCorrespondence.terminate_closures
    (state := {state.external.runtime.runtime.runtime.runtime.runtime with memory := memory})
    memoryStored storageStored 2 Word.zero (RevertSemantics.messageLength message)
  generalize TerminationBuiltinCorrespondence.target
    {state.external.runtime.runtime.runtime.runtime.runtime with memory := memory} Word.zero
    (RevertSemantics.messageLength message) = haltValue at haltResult haltEvaluated
  have worldKept : ∀ value, store.read? layout.storage.world = some value →
      (TerminationBuiltinCorrespondence.finalStore layout.storage
        {state.external.runtime.runtime.runtime.runtime.runtime with memory := memory} 2 Word.zero
        (RevertSemantics.messageLength message) storedStore).read? layout.storage.world = some value := by
    obtain ⟨notMemory, notSize, _⟩ := world_separate layout.toLayout
    intro value found
    exact finalStore_world (layout := layout.toLayout) (storedFrame.read _ value notMemory notSize found)
  generalize TerminationBuiltinCorrespondence.finalStore layout.storage
    {state.external.runtime.runtime.runtime.runtime.runtime with memory := memory} 2 Word.zero
    (RevertSemantics.messageLength message) storedStore = finalStore
    at memoryFinal storageFinal haltFrame haltEvaluated haltClosures worldKept
  cases haltResult with
  | language reason =>
  -- the frame update lifts through the return-data and call layers
  have storedEffects := RuntimeEffectsCorrespondence.Frame.of_memory (layout := layout.toLayout) storedFrame
  have totalFrame : RuntimeEffectsCorrespondence.Frame layout.toLayout store finalStore :=
    ⟨Nat.le_trans storedEffects.length_le haltFrame.length_le, fun location value outside found =>
      haltFrame.read location value outside (storedEffects.read location value outside found)⟩
  have returnDataFinal := RuntimeReturnDataEffectsCorrespondence.runtime_updated passive (runtime_related base)
    memoryFinal storageFinal totalFrame
  have finalRelated := RuntimeCallEffectsCorrespondence.runtime_updated base returnDataFinal rfl
  have linked : RuntimeLinkedWorldCorrespondence.StateRel anchors
      (sourceWorld {state.external with
        runtime := RuntimeReturnDataEffectsSemantics.withRuntime state.external.runtime halted})
      layout.storage.world finalStore := by
    have sameWorld : halted.storage.world = state.external.runtime.runtime.runtime.runtime.runtime.storage.world := by
      unfold TerminationSemantics.terminate at terminated
      split at terminated <;> cases terminated <;> rfl
    change RuntimeLinkedWorldCorrespondence.StateRel anchors halted.storage.world layout.storage.world finalStore
    rw [sameWorld]
    exact (linked_related stateRelated).read_preserved worldKept
  refine ⟨reason, finalStore, rfl, ?_,
    of_base finalRelated linked (context.updated base finalRelated stateRelated.external.2.2.1.2),
    ClosuresPreserved.trans storedClosures haltClosures⟩
  rw [exit_rename]
  apply LanguageResult.bind_success .unit mstoreEvaluated
  rw [weaken_rename]
  exact haltEvaluated
end

end Solcore.Frontend.RustHull.RevertBuiltinCorrespondence
end

section
-- leanmerge: from Solcore.Frontend.RustHull.YulBuiltinCorrespondence
/-! The builtins of the connected inline Yul fragment in the frame model. The
actual code of `mload`, `msize`, `mstore`, `mstore8`, `return` and `revert`
over the argument words matches `YulSemantics.Builtin`; catalog links and the
captured context survive. This meets `YulBlockCorrespondence.BuiltinStep`. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.YulBuiltinCorrespondence
open Core Correspondence ScalarExecution EffectBuiltinCorrespondence
open RuntimeCallEffectsCorrespondence (Layout Handlers account_related runtime_related)
open RuntimeChildCallEffectsCorrespondence

theorem mload_components {scope : Scope} {offset : Core.Expr} {lowered : Lowered}
    (compiled : Effects.lowerBuiltin scope "mload" [offset] = .ok lowered) :
    ∃ memory size, Effects.reference scope "memory" WordMapping.type = .ok memory ∧
      Effects.reference scope "memorySize" .word = .ok size ∧
      lowered = ⟨.word, Memory.mload memory size offset⟩ := by
  change (do
    let raw ← (do
      let memory ← Effects.reference scope "memory" WordMapping.type
      let size ← Effects.reference scope "memorySize" .word
      pure (Lowered.mk .word (Memory.mload memory size offset)) : LowerM Lowered)
    pure raw) = .ok lowered at compiled
  obtain ⟨memory, memoryCompiled, compiled⟩ := lower_bind_eq_ok.mp compiled
  obtain ⟨size, sizeCompiled, returned⟩ := lower_bind_eq_ok.mp compiled
  exact ⟨memory, size, memoryCompiled, sizeCompiled, (Except.ok.inj returned).symm⟩

theorem msize_components {scope : Scope} {lowered : Lowered}
    (compiled : Effects.lowerBuiltin scope "msize" [] = .ok lowered) :
    ∃ size, Effects.reference scope "memorySize" .word = .ok size ∧
      lowered = ⟨.word, LanguageResult.success (.loadCell size)⟩ := by
  change (do
    let raw ← (do
      let size ← Effects.reference scope "memorySize" .word
      pure (Lowered.mk .word (LanguageResult.success (.loadCell size))) : LowerM Lowered)
    pure raw) = .ok lowered at compiled
  obtain ⟨size, sizeCompiled, returned⟩ := lower_bind_eq_ok.mp compiled
  exact ⟨size, sizeCompiled, (Except.ok.inj returned).symm⟩

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

section
variable {slots : List EffectSlot} {store : Store}
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

/-- The fragment's builtins run their actual code over the argument words in the
frame model. -/
theorem step (passive : RuntimeLogEffectsCorrespondence.Passive layout.toLogLayout slots)
    (memoryMember : ⟨"memory", WordMapping.type, layout.memory⟩ ∈ slots)
    (memorySizeMember : ⟨"memorySize", .word, layout.storage.memorySize⟩ ∈ slots)
    (exitMember : ⟨"exit", .word, layout.storage.exit⟩ ∈ slots)
    (offsetMember : ⟨"returnOffset", .word, layout.storage.returnOffset⟩ ∈ slots)
    (sizeMember : ⟨"returnSize", .word, layout.storage.returnSize⟩ ∈ slots) :
    YulBlockCorrespondence.BuiltinStep (model layout baseline slots image handlers anchors context) slots := by
  intro name words state result next scope effect mapping environment world store effectNamed computed compiled runtime
    fixed stateRelated
  have base := base_related stateRelated
  have beforeRuntime := RuntimeEnvironmentEffectsCorrespondence.runtime_related
    (RuntimeLogEffectsCorrespondence.runtime_related (RuntimeAccountEffectsCorrespondence.runtime_related (account_related base)))
  have memoryBefore : MemoryCorrespondence.StateRel layout.memory layout.storage.memorySize
      (YulSemantics.frame state).memory store :=
    RuntimeEffectsCorrespondence.memory_related beforeRuntime
  have storageBefore : StorageBuiltinCorrespondence.StateRel layout.storage (YulSemantics.frame state).storage store :=
    RuntimeEffectsCorrespondence.storage_related beforeRuntime
  have read : ∀ (index : Nat) (word : Word), index < words.length →
      (words.map Value.word ++ environment)[index]? = some (.word word) →
      Evaluates (words.map Value.word ++ environment) store ((Core.Expr.var index).rename mapping) (.word word) store := by
    intro index word below found
    apply Evaluates.var
    show (words.map Value.word ++ environment)[mapping index]? = some (.word word)
    rw [fixed index below]
    exact found
  have stable : ∀ (index : Nat) (word : Word), index < words.length →
      (words.map Value.word ++ environment)[index]? = some (.word word) →
      TerminationBuiltinCorrespondence.StableWord (words.map Value.word ++ environment) mapping (.var index) word := by
    intro index word below found extra other
    apply Evaluates.var
    show (extra ++ (words.map Value.word ++ environment))[extra.length + mapping index]? = some (.word word)
    rw [fixed index below, List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left]
    exact found
  cases computed with
  | @mload _ offset =>
      obtain ⟨memoryReference, sizeReference, memoryCompiled, sizeCompiled, rfl⟩ := mload_components compiled
      obtain ⟨loadedResult, memoryLoaded, loadedFrame⟩ := MemoryCorrespondence.mload_preserves memoryBefore offset
        (Value.word offset :: environment)
      have loaded : Evaluates (Value.word offset :: environment) store
          ((Memory.mload memoryReference sizeReference (.var 0)).rename mapping)
          (MemoryCorrespondence.mloadResult (YulSemantics.frame state).memory offset)
          (MemoryCorrespondence.mloadStore store layout.memory layout.storage.memorySize
            (YulSemantics.frame state).memory offset (Value.word offset :: environment)) := by
        rw [MemoryCorrespondence.mload_rename]
        exact MemoryCorrespondence.mload_evaluates _ offset
          (reference_evaluates runtime memoryMember memoryCompiled store)
          (reference_evaluates runtime memorySizeMember sizeCompiled store) (read 0 offset (by simp) rfl)
          memoryBefore.memory memoryBefore.size memoryBefore.distinct
      exact ⟨_, _, loadedResult, loaded, memory_related passive stateRelated memoryLoaded loadedFrame,
        MemoryEffectCorrespondence.closures_preserved memoryBefore loadedFrame⟩
  | msize =>
      obtain ⟨sizeReference, sizeCompiled, rfl⟩ := msize_components compiled
      exact ⟨_, store, .value (.word _), LanguageResult.success_evaluates
        (.loadCell (reference_evaluates runtime memorySizeMember sizeCompiled store) memoryBefore.size), stateRelated,
        ClosuresPreserved.refl store⟩
  | @mstore _ offset value =>
      obtain ⟨memoryReference, sizeReference, memoryCompiled, sizeCompiled, rfl⟩ :=
        RevertBuiltinCorrespondence.store_components compiled
      obtain ⟨storedResult, memoryStored, storedFrame⟩ := MemoryCorrespondence.mstore_preserves memoryBefore
        offset value (Value.word offset :: Value.word value :: environment)
      have stored : Evaluates (Value.word offset :: Value.word value :: environment) store
          ((Memory.mstore memoryReference sizeReference (.var 0) (.var 1)).rename mapping)
          (MemoryCorrespondence.mstoreResult (YulSemantics.frame state).memory offset)
          (MemoryCorrespondence.mstoreStore store layout.memory layout.storage.memorySize
            (YulSemantics.frame state).memory offset value (Value.word offset :: Value.word value :: environment)) := by
        rw [MemoryCorrespondence.mstore_rename]
        exact MemoryCorrespondence.mstore_evaluates _ offset value
          (reference_evaluates runtime memoryMember memoryCompiled store)
          (reference_evaluates runtime memorySizeMember sizeCompiled store) (read 0 offset (by simp) rfl)
          (read 1 value (by simp) rfl) memoryBefore.memory memoryBefore.size memoryBefore.distinct
      exact ⟨_, _, storedResult, stored, memory_related passive stateRelated memoryStored storedFrame,
        MemoryEffectCorrespondence.closures_preserved memoryBefore storedFrame⟩
  | @mstore8 _ offset value =>
      obtain ⟨memoryReference, sizeReference, memoryCompiled, sizeCompiled, rfl⟩ := mstore8_components compiled
      obtain ⟨storedResult, memoryStored, storedFrame⟩ := MemoryCorrespondence.mstore8_preserves memoryBefore
        offset value (Value.word offset :: Value.word value :: environment)
      have stored : Evaluates (Value.word offset :: Value.word value :: environment) store
          ((Memory.mstore8 memoryReference sizeReference (.var 0) (.var 1)).rename mapping)
          (MemoryCorrespondence.mstore8Result (YulSemantics.frame state).memory offset)
          (MemoryCorrespondence.mstore8Store store layout.memory layout.storage.memorySize
            (YulSemantics.frame state).memory offset value (Value.word offset :: Value.word value :: environment)) := by
        rw [MemoryCorrespondence.mstore8_rename]
        exact MemoryCorrespondence.mstore8_evaluates _ offset value
          (reference_evaluates runtime memoryMember memoryCompiled store)
          (reference_evaluates runtime memorySizeMember sizeCompiled store) (read 0 offset (by simp) rfl)
          (read 1 value (by simp) rfl) memoryBefore.memory memoryBefore.size memoryBefore.distinct
      exact ⟨_, _, storedResult, stored, memory_related passive stateRelated memoryStored storedFrame,
        MemoryEffectCorrespondence.closures_preserved memoryBefore storedFrame⟩
  | @returned _ offset length =>
      obtain ⟨halt, haltCompiled, rfl⟩ := terminate_components (.inl ⟨rfl, rfl⟩) compiled
      have haltEvaluated := TerminationBuiltinCorrespondence.terminate_evaluates haltCompiled runtime
        memorySizeMember exitMember offsetMember sizeMember storageBefore memoryBefore.size offset length
        (stable 0 offset (by simp) rfl) (stable 1 length (by simp) rfl)
      obtain ⟨haltResult, _, _, _⟩ :=
        TerminationBuiltinCorrespondence.terminate_state memoryBefore storageBefore 1 offset length
      exact ⟨_, _, haltResult, haltEvaluated, terminated_related passive stateRelated 1 offset length,
        TerminationBuiltinCorrespondence.terminate_closures memoryBefore storageBefore 1 offset length⟩
  | @reverted _ offset length =>
      obtain ⟨halt, haltCompiled, rfl⟩ := terminate_components (.inr ⟨rfl, rfl⟩) compiled
      have haltEvaluated := TerminationBuiltinCorrespondence.terminate_evaluates haltCompiled runtime
        memorySizeMember exitMember offsetMember sizeMember storageBefore memoryBefore.size offset length
        (stable 0 offset (by simp) rfl) (stable 1 length (by simp) rfl)
      obtain ⟨haltResult, _, _, _⟩ :=
        TerminationBuiltinCorrespondence.terminate_state memoryBefore storageBefore 2 offset length
      exact ⟨_, _, haltResult, haltEvaluated, terminated_related passive stateRelated 2 offset length,
        TerminationBuiltinCorrespondence.terminate_closures memoryBefore storageBefore 2 offset length⟩
  | add => exact absurd effectNamed (by decide)
  | sub => exact absurd effectNamed (by decide)
  | lt => exact absurd effectNamed (by decide)
  | gt => exact absurd effectNamed (by decide)
  | eq => exact absurd effectNamed (by decide)
  | iszero => exact absurd effectNamed (by decide)

end

end Solcore.Frontend.RustHull.YulBuiltinCorrespondence
end
