import Solcore.Frontend.RustHull.CallTransportStateCorrespondence

/-! Child responses update complete return data before copying the requested
prefix into caller memory. The copied bytes and the returned success word come
from the independent response. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.CallTransportCorrespondence
open Core Correspondence ScalarExecution CallTransportSemantics

private theorem response_part {depth : Nat} {environment : Environment} {code : Calls.Code} {response : Response}
    (related : CodeValue depth environment code (responseValue response)) {index : Nat} {value : Core.Value}
    (found : (responseValues response)[index]? = some value) :
    CodeValue depth environment (fun depth => Calls.responseField index (code depth)) value := related.part found

theorem finish_preserves {depth : Nat} {environment : Environment} {store : Store}
    {locations : Locations} {callback : Nat} {arguments : Arguments} {state : CallTransportSemantics.State}
    {response : Response} {memory : MemorySemantics.State} {result : Semantics.Result Semantics.Value}
    {responseCode : Calls.Code}
    (inputs : Inputs depth environment locations callback arguments)
    (related : StateRel locations state store)
    (responseRelated : CodeValue depth environment responseCode (responseValue response))
    (copied : MemoryCopySemantics.From response.data arguments.outputOffset Word.zero
      (copiedLength arguments response) state.memory result memory) :
    ∃ target final,
      ResultRel .word (finishResult response result) target ∧
      Evaluates environment store (Calls.finish responseCode depth) target final ∧
      StateRel locations ⟨memory, response.data, response.size⟩ final ∧ Frame locations store final := by
  let writtenData : Store := store.set locations.returnData (WordMapping.encode response.data)
  let publishedStore := publishStore locations store response.data response.size
  have distinct := related.distinct
  simp [Locations.resources, LogsCorrespondence.Locations.all] at distinct
  have dataWritten : store.write? locations.returnData (WordMapping.encode response.data) = some writtenData :=
    Store.write?_eq_some_iff.mpr ⟨(List.getElem?_eq_some_iff.mp related.logs).1, rfl⟩
  have sizeFound : writtenData.read? locations.returnDataSize = some (.word state.returnDataSize) := by
    rw [Store.write?_preserves_other dataWritten (by intro same; simp_all)]
    exact related.logSize
  have sizeWritten : writtenData.write? locations.returnDataSize (.word response.size) = some publishedStore :=
    Store.write?_eq_some_iff.mpr ⟨(List.getElem?_eq_some_iff.mp sizeFound).1, rfl⟩
  have publishedRelated := published related response.data response.size
  have input' := inputs.prepend [Core.Value.unit, .unit]
  have response' := responseRelated.prepend [Core.Value.unit, .unit]
  have lengthEvaluated : Evaluates ([Core.Value.unit, .unit] ++ environment) publishedStore
      (Calls.choose (Calls.binary .wordGt (fun depth => Calls.responseField 2 (responseCode depth)) Calls.outputLength)
        Calls.outputLength (fun depth => Calls.responseField 2 (responseCode depth)) (depth + 2))
      (.word (copiedLength arguments response)) publishedStore := by
    have left := (response_part response' (index := 2) rfl).evaluates publishedStore
    have right := (input_part input' (index := 14) rfl).evaluates publishedStore
    by_cases long : response.size > arguments.outputLength
    · simp only [copiedLength, long, ↓reduceIte]
      exact .ifTrue (.binary left right (by simp [BinaryOp.apply, long])) right
    · simp only [copiedLength, long, ↓reduceIte]
      exact .ifFalse (.binary left right (by simp [BinaryOp.apply, long])) left
  obtain ⟨copyTarget, final, copyRelated, evaluated, memoryFinal, copiedFrame⟩ :=
    MemoryCopyCorrespondence.copyPackedFrom_preserves copied (memory_related (state := {state with returnData := response.data, returnDataSize := response.size}) publishedRelated)
      ((input_part input' (index := 0) rfl).evaluates publishedStore)
      ((input_part input' (index := 1) rfl).evaluates publishedStore)
      ((input_part input' (index := 13) rfl).evaluates publishedStore)
      ((response_part response' (index := 1) rfl).evaluates publishedStore) .word lengthEvaluated
  have finalRelated := memory_updated publishedRelated memoryFinal copiedFrame
  have frame := (LogsCorrespondence.Frame.publish locations.resources store response.data response.size).trans
    (memory_frame copiedFrame)
  have enter : ∀ target,
      Evaluates ([Core.Value.unit, .unit] ++ environment) publishedStore
        (Calls.bindResult (Calls.copy Calls.memory Calls.memorySize Calls.outputOffset
          (fun depth => Calls.responseField 1 (responseCode depth)) (Calls.number 0)
          (Calls.choose (Calls.binary .wordGt (fun depth => Calls.responseField 2 (responseCode depth)) Calls.outputLength)
            Calls.outputLength (fun depth => Calls.responseField 2 (responseCode depth))))
          (fun _ => Calls.success (Calls.choose (fun depth => Calls.responseField 0 (responseCode depth))
            (Calls.number 1) (Calls.number 0))) (depth + 2)) target final →
      Evaluates environment store (Calls.finish responseCode depth) target final := by
    intro target completed
    unfold Calls.finish Calls.bind
    apply Evaluates.letE (bodyStore := writtenData)
    · exact .storeCell ((input_part inputs (index := 2) rfl).evaluates store) related.logs
        ((response_part responseRelated (index := 1) rfl).evaluates store) dataWritten
    · apply Evaluates.letE (bodyStore := publishedStore)
      · exact .storeCell ((input_part (inputs.prepend [.unit]) (index := 3) rfl).evaluates writtenData)
          sizeFound ((response_part (responseRelated.prepend [.unit]) (index := 2) rfl).evaluates writtenData) sizeWritten
      · exact completed
  cases copied with
  | overflow _ =>
      cases copyRelated
      refine ⟨.inLeft .word (.word (Word.ofNatModulo 6)), final, .language _, enter _ ?_, finalRelated, frame⟩
      exact LanguageResult.bind_failure .word evaluated
  | done _ _ =>
      cases copyRelated with
      | value copiedValue =>
          cases copiedValue
          refine ⟨.inRight .word (.word (Word.ofNatModulo (if response.success then 1 else 0))), final,
            .value (.word _), enter _ ?_, finalRelated, frame⟩
          apply LanguageResult.bind_success .word evaluated
          apply Evaluates.inRight
          have succeeded := (response_part (responseRelated.prepend [.unit, .unit, .unit]) (index := 0) rfl).evaluates final
          cases success : response.success
          · exact .ifFalse (by simpa only [success, List.length_cons, List.length_nil, List.cons_append, List.nil_append, Nat.add_assoc] using succeeded) .word
          · exact .ifTrue (by simpa only [success, List.length_cons, List.length_nil, List.cons_append, List.nil_append, Nat.add_assoc] using succeeded) .word

end Solcore.Frontend.RustHull.CallTransportCorrespondence
