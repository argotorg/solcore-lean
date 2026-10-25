import Solcore.Frontend.RustHull.CallBuiltinEvaluation
import Solcore.Frontend.RustHull.RuntimeChildCallInvokeCorrespondence

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
