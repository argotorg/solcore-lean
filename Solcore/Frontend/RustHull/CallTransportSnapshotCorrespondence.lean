import Solcore.Frontend.RustHull.CallTransportFinishCorrespondence
import Solcore.Frontend.RustHull.EffectStateCorrespondence

/-! The emitted dispatch copies caller input into two fresh scratch cells.
Every pre-existing cell is retained before the callback is selected. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.CallTransportCorrespondence
open Core Correspondence ScalarExecution CallTransportSemantics

def dispatchTail (input : Calls.Code) : Calls.Code :=
  Calls.bindResult (fun depth => OptionalCell.read Calls.callbackType (Calls.callback depth) Calls.unavailableReason) fun function =>
  Calls.bindResult (fun depth => .apply (function depth) (bundle [
    Calls.binary .wordAnd Calls.target (Calls.number (2 ^ 160 - 1)) depth,
    Calls.binary .wordAnd Calls.caller (Calls.number (2 ^ 160 - 1)) depth,
    Calls.value depth, Calls.childStatic depth, Calls.binary .wordAdd Calls.depth (Calls.number 1) depth,
    Calls.gas depth, Calls.load input depth, Calls.inputLength depth])) Calls.finish

theorem state_retained {locations : Locations} {state : CallTransportSemantics.State} {initial final : Store}
    (related : StateRel locations state initial) (retained : StoreRetains initial final) : StateRel locations state final := by
  refine ⟨related.distinct, ?_, ?_, ?_, ?_⟩
  all_goals first
    | exact (retained.read _ (List.getElem?_eq_some_iff.mp related.memory).1).trans related.memory
    | exact (retained.read _ (List.getElem?_eq_some_iff.mp related.memorySize).1).trans related.memorySize
    | exact (retained.read _ (List.getElem?_eq_some_iff.mp related.logs).1).trans related.logs
    | exact (retained.read _ (List.getElem?_eq_some_iff.mp related.logSize).1).trans related.logSize

theorem retained_frame (locations : Locations) {initial final : Store} (retained : StoreRetains initial final) :
    Frame locations initial final :=
  ⟨retained.length_le, fun _ _ _ found => (retained.read _ (List.getElem?_eq_some_iff.mp found).1).trans found⟩

theorem snapshot_evaluates {depth : Nat} {environment : Environment} {store : Store}
    {locations : Locations} {callback : Nat} {arguments : Arguments} {state : CallTransportSemantics.State}
    {input : MemorySemantics.State}
    (inputs : Inputs depth environment locations callback arguments)
    (related : StateRel locations state store)
    (copied : MemoryCopySemantics.From state.memory.words Word.zero arguments.inputOffset arguments.inputLength
      {} (.value .unit) input) :
    ∃ extra copiedStore inputCode,
      extra.length = 4 ∧ StoreRetains store copiedStore ∧
      Inputs (depth + 4) (extra ++ environment) locations callback arguments ∧
      CodeValue (depth + 4) (extra ++ environment) inputCode (.cellRef WordMapping.type store.length) ∧
      copiedStore.read? store.length = some (WordMapping.encode input.words) ∧
      ∀ target final,
        Evaluates (extra ++ environment) copiedStore (dispatchTail inputCode (depth + 4)) target final →
        Evaluates environment store (Calls.dispatch depth) target final := by
  let snapshot := WordMapping.encode state.memory.words
  let inputRef := Value.cellRef WordMapping.type store.length
  let sizeRef := Value.cellRef .word (store.length + 1)
  let allocated : Store := store ++ [WordMapping.encode [], .word Word.zero]
  let inputCode : Calls.Code := fun here => .var (here - (depth + 1) - 1)
  let sizeCode : Calls.Code := fun here => .var (here - (depth + 2) - 1)
  let snapshotCode : Calls.Code := fun here => .var (here - depth - 1)
  have snapshotRelated := CodeValue.bound depth environment snapshot
  have inputRelated := CodeValue.bound (depth + 1) (snapshot :: environment) inputRef
  have sizeRelated := CodeValue.bound (depth + 2) (inputRef :: snapshot :: environment) sizeRef
  have scratchRelated : MemoryCorrespondence.StateRel store.length (store.length + 1) {} allocated := by
    refine ⟨by omega, ?_, ?_⟩ <;> simp [allocated, Store.read?]
  let extraInput : Environment := [sizeRef, inputRef, snapshot]
  obtain ⟨target, copiedStore, resultRelated, evaluated, inputMemory, frame⟩ :=
    MemoryCopyCorrespondence.copyPackedFrom_preserves copied scratchRelated
      ((inputRelated.prepend [sizeRef]).evaluates allocated) (sizeRelated.evaluates allocated) .word
      ((snapshotRelated.prepend [sizeRef, inputRef]).evaluates allocated)
      ((input_part (inputs.prepend extraInput) (index := 11) rfl).evaluates allocated)
      ((input_part (inputs.prepend extraInput) (index := 12) rfl).evaluates allocated)
  cases resultRelated with
  | value valueRelated =>
      cases valueRelated
      have retained : StoreRetains store copiedStore := by
        constructor
        · have length := frame.length
          simp only [allocated, List.length_append, List.length_cons, List.length_nil] at length
          omega
        · intro location bounded
          have found : store.read? location = some store[location] := List.getElem?_eq_getElem bounded
          have after : copiedStore.read? location = some store[location] :=
            frame.read location _ (by omega) (by omega)
              (by simpa only [allocated, Store.read?, List.getElem?_append_left bounded] using found)
          exact after.trans found.symm
      refine ⟨.unit :: extraInput, copiedStore, inputCode, rfl, retained, inputs.prepend (.unit :: extraInput),
        inputRelated.prepend [.unit, sizeRef], inputMemory.memory, ?_⟩
      intro target final completed
      unfold Calls.dispatch Calls.bind
      apply Evaluates.letE (.loadCell ((input_part inputs (index := 0) rfl).evaluates store) related.memory)
      apply Evaluates.letE (bodyStore := store ++ [WordMapping.encode []])
      · exact .newCell (.construct .unit)
      · apply Evaluates.letE (bodyStore := allocated)
        · simpa only [allocated, List.length_append, List.length_cons, List.length_nil, List.append_assoc, List.cons_append, List.nil_append, inputRef, snapshot, resources, Calls.allocate, Calls.number, show Word.ofNatModulo 0 = Word.zero from rfl] using
            (Evaluates.newCell (elementType := .word) (environment := inputRef :: snapshot :: environment)
              (initialStore := store ++ [WordMapping.encode []]) Evaluates.word (initialValue := .word Word.zero))
        · exact LanguageResult.bind_success .word evaluated completed

end Solcore.Frontend.RustHull.CallTransportCorrespondence
