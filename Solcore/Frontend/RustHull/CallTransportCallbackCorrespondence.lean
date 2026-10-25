import Solcore.Frontend.RustHull.CallTransportSnapshotCorrespondence

/-! Account callbacks may change shared resources while preserving the four
caller cells. Their store relation composes with ordinary transport frames. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.CallTransportCorrespondence
open Core Correspondence ScalarExecution CallTransportSemantics

structure Model (Shared : Type) (locations : Locations) where
  related : Shared → Store → Prop
  frame : ∀ {state initial final}, Frame locations initial final → related state initial → related state final
  retains : Store → Store → Prop
  retainedFrame : ∀ {initial final}, Frame locations initial final → retains initial final
  retainedTrans : ∀ {initial middle final}, retains initial middle → retains middle final → retains initial final

def CallbackPreservation {Shared : Type} {locations : Locations}
    (model : Model Shared locations)
    (callback : Request → Shared → Semantics.Result Response → Shared → Prop) (function : Core.Value) : Prop :=
  ∀ {request shared finalShared result}, callback request shared result finalShared →
    ∀ {state environment store functionExpr requestExpr},
      model.related shared store → StateRel locations state store →
      Evaluates environment store functionExpr function store →
      Evaluates environment store requestExpr (requestValue request) store →
      ∃ target final, ResponseRel result target ∧
        Evaluates environment store (.apply functionExpr requestExpr) target final ∧
        StateRel locations state final ∧ model.related finalShared final ∧ model.retains store final

def requestExpression (input : Calls.Code) : Calls.Code := fun depth => bundle [
  Calls.binary .wordAnd Calls.target (Calls.number (2 ^ 160 - 1)) depth,
  Calls.binary .wordAnd Calls.caller (Calls.number (2 ^ 160 - 1)) depth,
  Calls.value depth, Calls.childStatic depth, Calls.binary .wordAdd Calls.depth (Calls.number 1) depth,
  Calls.gas depth, Calls.load input depth, Calls.inputLength depth]

theorem request_evaluates {depth : Nat} {environment : Environment} {store : Store} {locations : Locations}
    {callback inputLocation : Nat} {arguments : Arguments} {entries : MemorySemantics.Entries} {input : Calls.Code}
    (inputs : Inputs depth environment locations callback arguments)
    (inputRelated : CodeValue depth environment input (.cellRef WordMapping.type inputLocation))
    (inputRead : store.read? inputLocation = some (WordMapping.encode entries)) :
    Evaluates environment store (requestExpression input depth) (requestValue (request arguments entries)) store := by
  refine .pair (.binary ((input_part inputs (index := 9) rfl).evaluates store) .word rfl) ?_
  refine .pair (.binary ((input_part inputs (index := 5) rfl).evaluates store) .word rfl) ?_
  refine .pair ((input_part inputs (index := 10) rfl).evaluates store) ?_
  refine .pair ((input_part inputs (index := 7) rfl).evaluates store) ?_
  refine .pair (.binary ((input_part inputs (index := 6) rfl).evaluates store) .word rfl) ?_
  refine .pair ((input_part inputs (index := 8) rfl).evaluates store) ?_
  exact .pair (.loadCell (inputRelated.evaluates store) inputRead) ((input_part inputs (index := 12) rfl).evaluates store)

def callbackValue (available : Bool) (function : Core.Value) : Core.Value :=
  if available then .inRight .unit function else .inLeft Calls.callbackType .unit

theorem dispatch_preserves {Shared : Type} {locations : Locations} (model : Model Shared locations)
    {callback : Request → Shared → Semantics.Result Response → Shared → Prop}
    {available : Bool} {arguments : Arguments}
    {state finalState : CallTransportSemantics.State} {shared finalShared : Shared}
    {result : Semantics.Result Semantics.Value}
    (dispatched : Dispatch callback available arguments state shared result finalState finalShared)
    {depth : Nat} {environment : Environment} {store : Store} {callbackLocation : Nat} {function : Core.Value}
    (inputs : Inputs depth environment locations callbackLocation arguments)
    (related : StateRel locations state store)
    (sharedRelated : model.related shared store)
    (handler : store.read? callbackLocation = some (callbackValue available function))
    (preserved : CallbackPreservation model callback function) :
    ∃ target final, ResultRel .word result target ∧
      Evaluates environment store
        (Calls.choose (Calls.binary .wordGt Calls.depth (Calls.number (Calls.depthLimit - 1)))
          (Calls.success (Calls.number 0)) Calls.dispatch depth) target final ∧
      StateRel locations finalState final ∧ model.related finalShared final ∧ model.retains store final := by
  cases dispatched with
  | depth _ exceeded =>
      refine ⟨.inRight .word (.word Word.zero), store, .value (.word _), ?_, related, sharedRelated,
        model.retainedFrame (.refl _ _)⟩
      exact .ifTrue (.binary ((input_part inputs (index := 6) rfl).evaluates store) .word
        (by simp [BinaryOp.apply, Calls.depthLimit, exceeded])) (.inRight .word)
  | unavailable _ allowed copied missing =>
      subst available
      obtain ⟨extra, copiedStore, inputCode, length, retained, inputs', _, _, entered⟩ := snapshot_evaluates inputs related copied
      have frame := retained_frame locations retained
      have read := (retained.read callbackLocation (List.getElem?_eq_some_iff.mp handler).1).trans handler
      refine ⟨.inLeft .word (.word (Word.ofNatModulo 7)), copiedStore, .language _, ?_,
        state_retained related retained, model.frame frame sharedRelated, model.retainedFrame frame⟩
      apply Evaluates.ifFalse (.binary ((input_part inputs (index := 6) rfl).evaluates store) .word
        (by simp [BinaryOp.apply, Calls.depthLimit, allowed]))
      apply entered
      exact LanguageResult.bind_failure .word
        (OptionalCell.read_failure Calls.unavailableReason ((input_part inputs' (index := 4) rfl).evaluates copiedStore) read)
  | fault allowed copied present called =>
      subst available
      obtain ⟨extra, copiedStore, inputCode, length, retained, inputs', inputRelated, inputRead, entered⟩ := snapshot_evaluates inputs related copied
      have frame := retained_frame locations retained
      have read := (retained.read callbackLocation (List.getElem?_eq_some_iff.mp handler).1).trans handler
      have functionRead := OptionalCell.read_success Calls.unavailableReason
        ((input_part inputs' (index := 4) rfl).evaluates copiedStore) read
      have requestRead := request_evaluates (inputs'.prepend [function]) (inputRelated.prepend [function]) inputRead
      obtain ⟨target, after, responseRelated, evaluated, afterRelated, sharedAfter, retainedAfter⟩ :=
        preserved called (model.frame frame sharedRelated) (state_retained related retained)
          ((CodeValue.bound (depth + 4) (extra ++ environment) function).evaluates copiedStore) requestRead
      cases responseRelated with
      | language reason =>
          refine ⟨.inLeft .word (.word reason), after, .language _, ?_, afterRelated, sharedAfter,
            model.retainedTrans (model.retainedFrame frame) retainedAfter⟩
          apply Evaluates.ifFalse (.binary ((input_part inputs (index := 6) rfl).evaluates store) .word
            (by simp [BinaryOp.apply, Calls.depthLimit, allowed]))
          apply entered
          exact LanguageResult.bind_success .word functionRead (LanguageResult.bind_failure .word evaluated)
  | returned allowed copied present called output =>
      rename_i input memory response result
      subst available
      obtain ⟨extra, copiedStore, inputCode, length, retained, inputs', inputRelated, inputRead, entered⟩ := snapshot_evaluates inputs related copied
      have frame := retained_frame locations retained
      have read := (retained.read callbackLocation (List.getElem?_eq_some_iff.mp handler).1).trans handler
      have functionRead := OptionalCell.read_success Calls.unavailableReason
        ((input_part inputs' (index := 4) rfl).evaluates copiedStore) read
      have requestRead := request_evaluates (inputs'.prepend [function]) (inputRelated.prepend [function]) inputRead
      obtain ⟨target, after, responseRelated, evaluated, afterRelated, sharedAfter, retainedAfter⟩ :=
        preserved called (model.frame frame sharedRelated) (state_retained related retained)
          ((CodeValue.bound (depth + 4) (extra ++ environment) function).evaluates copiedStore) requestRead
      cases responseRelated with
      | returned =>
          obtain ⟨target, final, resultRelated, finished, finalRelated, finishFrame⟩ := finish_preserves
            (inputs'.prepend [responseValue response, function]) afterRelated
            (CodeValue.bound (depth + 4 + 1) (function :: extra ++ environment) (responseValue response)) output
          refine ⟨target, final, resultRelated, ?_, finalRelated, model.frame finishFrame sharedAfter,
            model.retainedTrans (model.retainedTrans (model.retainedFrame frame) retainedAfter) (model.retainedFrame finishFrame)⟩
          apply Evaluates.ifFalse (.binary ((input_part inputs (index := 6) rfl).evaluates store) .word
            (by simp [BinaryOp.apply, Calls.depthLimit, allowed]))
          apply entered
          exact LanguageResult.bind_success .word functionRead (LanguageResult.bind_success .word evaluated finished)

end Solcore.Frontend.RustHull.CallTransportCorrespondence
