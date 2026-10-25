import Solcore.Frontend.RustHull.CallModeBuiltinCompiler
import Solcore.Frontend.RustHull.RuntimeCallModeInvokeCorrespondence

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
