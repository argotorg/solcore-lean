import Solcore.Frontend.RustHull.CallBuiltinCompiler
import Solcore.Frontend.RustHull.RuntimeCallInvokeCorrespondence
import Solcore.Frontend.RustHull.TerminationBuiltinCorrespondence

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
