import Solcore.Frontend.RustHull.RuntimeChildCallStateCorrespondence
import Solcore.Frontend.RustHull.RuntimeCallCallbackCorrespondence
import Solcore.Frontend.RustHull.CallTransportRenamingCorrespondence

/-! The actual caller transport uses concrete callback captures and rebuilds
all caller and shared resources after account dispatch. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.RuntimeChildCallEffectsCorrespondence
open Core Correspondence ScalarExecution
open RuntimeCallEffectsCorrespondence (Layout Handlers CallPassive localLocations)

theorem invoke_preserves {layout : Layout} {baseline : Nat → Option Core.Value} {slots : List EffectSlot}
    {image : Option (List UInt8)} {handlers : Handlers layout} {anchors : Anchors} {context : RuntimeChildCallEffectsCorrespondence.Context layout} {world : World}
    {children : RuntimeCallEffectsSemantics.State → AccountCallSemantics.Children}
    {state : Semantics.State RuntimeCallEffectsSemantics.State} {initial store : Store}
    {operation : RuntimeCallEffectsSemantics.Operation}
    {gas target value inputOffset inputLength outputOffset outputLength : Word}
    {result : Semantics.Result Semantics.Value} {next : CallTransportSemantics.State}
    {shared : AccountCallSemantics.Shared}
    (executed : CallTransportSemantics.Execute
      (AccountCallSemantics.Dispatch (children state.external) .ordinary
        state.external.runtime.runtime.runtime.runtime.runtime.storage.address)
      true (RuntimeCallEffectsSemantics.arguments operation state.external gas target value inputOffset inputLength outputOffset outputLength)
      (RuntimeCallEffectsSemantics.transport state.external) (RuntimeCallEffectsSemantics.shared state.external) result next shared)
    (passive : CallPassive layout slots)
    (stateRelated : StateRel (model layout baseline slots image handlers anchors context) world state store)
    (callback : CallbackPreservation layout handlers anchors context children state.external)
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
      StateRel (model layout baseline slots image handlers anchors context) world
        {state with external := RuntimeCallEffectsSemantics.withTransport state.external next shared} final ∧
      ClosuresPreserved store final := by
  have before := base_related stateRelated
  have sharedRelated : (transportModel layout handlers anchors context).related
      (RuntimeCallEffectsSemantics.shared state.external) store :=
    ⟨RuntimeCallEffectsCorrespondence.shared_resources before, linked_related stateRelated,
      stateRelated.external.1, stateRelated.external.2.2.1.2⟩
  have outside : layout.callHandler ∉ (localLocations layout).all :=
    RuntimeCallEffectsCorrespondence.shared_local_separation layout layout.callHandler (by simp)
  obtain ⟨resultValue, final, resultRelated, evaluated, localFinal, sharedFinal, frame⟩ :=
    CallTransportCorrespondence.invoke_preserves (transportModel layout handlers anchors context) executed packed
      (RuntimeCallEffectsCorrespondence.local_related before) sharedRelated sharedRelated.1.2.1 outside callback
  exact ⟨resultValue, final, resultRelated, evaluated,
    of_base (RuntimeCallEffectsCorrespondence.transport_updated passive before localFinal sharedFinal.1.1 frame) sharedFinal.2.1 sharedFinal.2.2.2,
    RuntimeCallEffectsCorrespondence.frame_closures before frame⟩

end Solcore.Frontend.RustHull.RuntimeChildCallEffectsCorrespondence
