import Solcore.Frontend.RustHull.CallTransportCallbackCorrespondence

/-! The complete CALL transport follows the independent range checks, data
reset, depth decision, copied input, callback, and copied response. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.CallTransportCorrespondence
open Core Correspondence ScalarExecution CallTransportSemantics

private theorem clear_evaluates {depth : Nat} {environment : Environment} {store final : Store}
    {locations : Locations} {callback : Nat} {arguments : Arguments} {state : CallTransportSemantics.State}
    {target : Core.Value} {body : Calls.Code}
    (inputs : Inputs depth environment locations callback arguments)
    (related : StateRel locations state store)
    (continued : Evaluates ([Core.Value.unit, .unit] ++ environment)
      (publishStore locations store [] Word.zero) (body (depth + 2)) target final) :
    Evaluates environment store
      (Calls.bind (Calls.store Calls.returnData Calls.empty) (fun _ =>
        Calls.bind (Calls.store Calls.returnSize (Calls.number 0)) (fun _ => body)) depth) target final := by
  let writtenData : Store := store.set locations.returnData (WordMapping.encode [])
  have distinct := related.distinct
  simp [Locations.resources, LogsCorrespondence.Locations.all] at distinct
  have dataWritten : store.write? locations.returnData (WordMapping.encode []) = some writtenData :=
    Store.write?_eq_some_iff.mpr ⟨(List.getElem?_eq_some_iff.mp related.logs).1, rfl⟩
  have sizeFound : writtenData.read? locations.returnDataSize = some (.word state.returnDataSize) := by
    rw [Store.write?_preserves_other dataWritten (by intro same; simp_all)]
    exact related.logSize
  have sizeWritten : writtenData.write? locations.returnDataSize (.word Word.zero) =
      some (publishStore locations store [] Word.zero) :=
    Store.write?_eq_some_iff.mpr ⟨(List.getElem?_eq_some_iff.mp sizeFound).1, rfl⟩
  apply Evaluates.letE (bodyStore := writtenData)
  · exact .storeCell ((input_part inputs (index := 2) rfl).evaluates store) related.logs (.construct .unit) dataWritten
  · apply Evaluates.letE (bodyStore := publishStore locations store [] Word.zero)
    · exact .storeCell ((input_part (inputs.prepend [.unit]) (index := 3) rfl).evaluates writtenData)
        sizeFound .word sizeWritten
    · exact continued

theorem callCode_preserves {Shared : Type} {locations : Locations} (model : Model Shared locations)
    {callback : Request → Shared → Semantics.Result Response → Shared → Prop}
    {available : Bool} {arguments : Arguments}
    {state finalState : CallTransportSemantics.State} {shared finalShared : Shared}
    {result : Semantics.Result Semantics.Value}
    (executed : Execute callback available arguments state shared result finalState finalShared)
    {depth : Nat} {environment : Environment} {store : Store} {callbackLocation : Nat} {function : Core.Value}
    (inputs : Inputs depth environment locations callbackLocation arguments)
    (related : StateRel locations state store)
    (sharedRelated : model.related shared store)
    (handler : store.read? callbackLocation = some (callbackValue available function))
    (outside : callbackLocation ∉ locations.all)
    (preserved : CallbackPreservation model callback function) :
    ∃ target final, ResultRel .word result target ∧
      Evaluates environment store (Calls.callCode depth) target final ∧
      StateRel locations finalState final ∧ model.related finalShared final ∧ model.retains store final := by
  have touched := MemoryCorrespondence.touch_evaluates (size := state.memory.size)
    ((input_part inputs (index := 1) rfl).evaluates store)
    ((input_part inputs (index := 11) rfl).evaluates store)
    ((input_part inputs (index := 12) rfl).evaluates store) related.memorySize
  cases executed with
  | inputOverflow _ invalid =>
      simp only [MemoryCorrespondence.touchResult, invalid, MemoryCorrespondence.touchStore_failure invalid] at touched
      refine ⟨.inLeft .word (.word Memory.overflowReason), store, .language _, ?_, related,
        sharedRelated, model.retainedFrame (.refl _ _)⟩
      exact LanguageResult.bind_failure .word touched
  | outputOverflow _ input invalid =>
      simp only [MemoryCorrespondence.touchResult, input] at touched
      let inputStore := MemoryCorrespondence.touchStore store locations.memorySize state.memory.size arguments.inputOffset arguments.inputLength
      have inputRelated := related.touch input
      have inputFrame := LogsCorrespondence.Frame.touch locations.resources store state.memory.size arguments.inputOffset arguments.inputLength
      have inputs' := inputs.prepend [.unit]
      have outputTouched := MemoryCorrespondence.touch_evaluates
        ((input_part inputs' (index := 1) rfl).evaluates inputStore)
        ((input_part inputs' (index := 13) rfl).evaluates inputStore)
        ((input_part inputs' (index := 14) rfl).evaluates inputStore) inputRelated.memorySize
      simp only [MemoryCorrespondence.touchResult, invalid, MemoryCorrespondence.touchStore_failure invalid] at outputTouched
      refine ⟨.inLeft .word (.word Memory.overflowReason), inputStore, .language _, ?_, inputRelated,
        model.frame inputFrame sharedRelated, model.retainedFrame inputFrame⟩
      exact LanguageResult.bind_success .word touched (LanguageResult.bind_failure .word outputTouched)
  | @ready _ _ _ inputSize outputSize _ input output dispatched =>
      simp only [MemoryCorrespondence.touchResult, input] at touched
      let inputStore := MemoryCorrespondence.touchStore store locations.memorySize state.memory.size arguments.inputOffset arguments.inputLength
      let outputStore := MemoryCorrespondence.touchStore inputStore locations.memorySize inputSize arguments.outputOffset arguments.outputLength
      have inputRelated := related.touch input
      have inputFrame := LogsCorrespondence.Frame.touch locations.resources store state.memory.size arguments.inputOffset arguments.inputLength
      have inputs' := inputs.prepend [.unit]
      have outputTouched := MemoryCorrespondence.touch_evaluates
        ((input_part inputs' (index := 1) rfl).evaluates inputStore)
        ((input_part inputs' (index := 13) rfl).evaluates inputStore)
        ((input_part inputs' (index := 14) rfl).evaluates inputStore) inputRelated.memorySize
      simp only [MemoryCorrespondence.touchResult, output] at outputTouched
      have outputRelated : StateRel locations {state with memory := {state.memory with size := outputSize}} outputStore :=
        inputRelated.touch output
      have outputFrame := LogsCorrespondence.Frame.touch locations.resources inputStore inputSize arguments.outputOffset arguments.outputLength
      have clearedRelated := published outputRelated [] Word.zero
      have clearFrame := LogsCorrespondence.Frame.publish locations.resources outputStore [] Word.zero
      have framed := (inputFrame.trans outputFrame).trans clearFrame
      have handler' := framed.read callbackLocation _ outside handler
      obtain ⟨target, final, resultRelated, evaluated, finalRelated, sharedFinal, retained⟩ :=
        dispatch_preserves model dispatched (inputs.prepend [.unit, .unit, .unit, .unit])
          clearedRelated (model.frame framed sharedRelated) handler' preserved
      refine ⟨target, final, resultRelated, ?_, finalRelated, sharedFinal,
        model.retainedTrans (model.retainedFrame framed) retained⟩
      apply LanguageResult.bind_success .word touched
      apply LanguageResult.bind_success .word outputTouched
      exact clear_evaluates (inputs.prepend [.unit, .unit]) outputRelated evaluated

theorem invoke_preserves {Shared : Type} {locations : Locations} (model : Model Shared locations)
    {callback : Request → Shared → Semantics.Result Response → Shared → Prop}
    {available : Bool} {arguments : Arguments}
    {state finalState : CallTransportSemantics.State} {shared finalShared : Shared}
    {result : Semantics.Result Semantics.Value}
    (executed : Execute callback available arguments state shared result finalState finalShared)
    {environment : Environment} {initial store : Store} {callbackLocation : Nat} {function : Core.Value}
    {memoryReference sizeReference returnDataReference returnSizeReference callbackReference
      callerAddress currentDepth staticFlag suppliedGas address transferredValue
      sourceOffset sourceLength destinationOffset destinationLength : Core.Expr}
    (packed : Evaluates environment initial
      (bundle [memoryReference, sizeReference, returnDataReference, returnSizeReference,
        callbackReference, callerAddress, currentDepth, staticFlag, suppliedGas, address,
        transferredValue, sourceOffset, sourceLength, destinationOffset, destinationLength])
      (bundleValues (argumentValues locations callbackLocation arguments)) store)
    (related : StateRel locations state store)
    (sharedRelated : model.related shared store)
    (handler : store.read? callbackLocation = some (callbackValue available function))
    (outside : callbackLocation ∉ locations.all)
    (preserved : CallbackPreservation model callback function) :
    ∃ target final, ResultRel .word result target ∧
      Evaluates environment initial
        (Calls.invoke memoryReference sizeReference returnDataReference returnSizeReference callbackReference
          callerAddress currentDepth staticFlag suppliedGas address transferredValue
          sourceOffset sourceLength destinationOffset destinationLength) target final ∧
      StateRel locations finalState final ∧ model.related finalShared final ∧ model.retains store final := by
  obtain ⟨target, final, resultRelated, evaluated, finalRelated, sharedFinal, retained⟩ :=
    callCode_preserves model executed (input_initial locations callbackLocation arguments environment)
      related sharedRelated handler outside preserved
  exact ⟨target, final, resultRelated, .letE packed evaluated, finalRelated, sharedFinal, retained⟩

end Solcore.Frontend.RustHull.CallTransportCorrespondence
