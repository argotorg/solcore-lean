import Solcore.Frontend.RustHull.RuntimeCallCallbackCorrespondence
import Solcore.Frontend.RustHull.CallTransportRenamingCorrespondence

/-! The actual caller transport uses concrete callback captures and rebuilds
all caller and shared resources after account dispatch. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.RuntimeCallEffectsCorrespondence
open Core Correspondence ScalarExecution

theorem invoke_preserves {layout : Layout} {baseline : Nat → Option Core.Value} {slots : List EffectSlot}
    {image : Option (List UInt8)} {handlers : Handlers layout} {world : World}
    {state : Semantics.State RuntimeCallEffectsSemantics.State} {initial store : Store}
    {operation : RuntimeCallEffectsSemantics.Operation}
    {gas target value inputOffset inputLength outputOffset outputLength : Word}
    {result : Semantics.Result Semantics.Value} {next : CallTransportSemantics.State}
    {shared : AccountCallSemantics.Shared}
    (executed : CallTransportSemantics.Execute
      (AccountCallSemantics.Dispatch AccountCallSemantics.noChildren .ordinary
        state.external.runtime.runtime.runtime.runtime.runtime.storage.address)
      true (RuntimeCallEffectsSemantics.arguments operation state.external gas target value inputOffset inputLength outputOffset outputLength)
      (RuntimeCallEffectsSemantics.transport state.external) (RuntimeCallEffectsSemantics.shared state.external) result next shared)
    (passive : CallPassive layout slots)
    (stateRelated : StateRel (model layout baseline slots image handlers) world state store)
    {environment : Environment}
    {memoryReference sizeReference returnDataReference returnSizeReference callbackReference
      callerAddress currentDepth staticFlag suppliedGas address transferredValue
      sourceOffset sourceLength destinationOffset destinationLength : Core.Expr}
    (packed : Evaluates environment initial
      (bundle [memoryReference, sizeReference, returnDataReference, returnSizeReference,
        callbackReference, callerAddress, currentDepth, staticFlag, suppliedGas, address,
        transferredValue, sourceOffset, sourceLength, destinationOffset, destinationLength])
      (bundleValues (CallTransportCorrespondence.argumentValues (localLocations layout) layout.callHandler
        (RuntimeCallEffectsSemantics.arguments operation state.external gas target value inputOffset inputLength outputOffset outputLength))) store) :
    ∃ resultValue final, ResultRel .word result resultValue ∧
      Evaluates environment initial
        (Calls.invoke memoryReference sizeReference returnDataReference returnSizeReference callbackReference
          callerAddress currentDepth staticFlag suppliedGas address transferredValue
          sourceOffset sourceLength destinationOffset destinationLength) resultValue final ∧
      StateRel (model layout baseline slots image handlers) world
        {state with external := RuntimeCallEffectsSemantics.withTransport state.external next shared} final ∧
      ClosuresPreserved store final := by
  have sharedRelated := shared_resources stateRelated
  have source := source_eq stateRelated
  have preserved : CallTransportCorrespondence.CallbackPreservation (transportModel layout handlers)
      (AccountCallSemantics.Dispatch AccountCallSemantics.noChildren .ordinary
        state.external.runtime.runtime.runtime.runtime.runtime.storage.address) handlers.handlerValue := by
    rw [source]
    exact callback_preserves layout handlers
  have outside : layout.callHandler ∉ (localLocations layout).all :=
    shared_local_separation layout layout.callHandler (by simp)
  obtain ⟨resultValue, final, resultRelated, evaluated, localFinal, sharedFinal, frame⟩ :=
    CallTransportCorrespondence.invoke_preserves (transportModel layout handlers) executed packed
      (local_related stateRelated) sharedRelated sharedRelated.2.1 outside preserved
  exact ⟨resultValue, final, resultRelated, evaluated,
    transport_updated passive stateRelated localFinal sharedFinal.1 frame, frame_closures stateRelated frame⟩

end Solcore.Frontend.RustHull.RuntimeCallEffectsCorrespondence
