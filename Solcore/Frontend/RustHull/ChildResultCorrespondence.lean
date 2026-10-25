import Solcore.Frontend.RustHull.ChildResultSemantics
import Solcore.Frontend.RustHull.MemorySnapshotCorrespondence
import Solcore.Frontend.RustHull.CallTransportValues
import Solcore.Frontend.RustHull.AccountRuntime

/-! Actual child completion observes the exit before its status and extracts
complete return or revert bytes without changing any existing resource cell. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.ChildResultCorrespondence
open Core CodeBuilder Correspondence ScalarExecution

def frameValue (status : Value) (state : RuntimeEffectsSemantics.State)
    (storage logs cursor balances world : Value) : Value :=
  .pair status (bundleValues [.word state.storage.exit, .word state.storage.returnOffset,
    .word state.storage.returnSize, WordMapping.encode state.memory.words, storage, logs, cursor, balances, world])

theorem childResult_evaluates {status : Semantics.Result Semantics.Value} {state : RuntimeEffectsSemantics.State}
    {response : Semantics.Result AccountCallSemantics.Response}
    (responded : ChildResultSemantics.Respond status state response)
    {depth : Nat} {environment : Environment} {store : Store} {result : Code}
    {statusValue storage logs cursor balances world : Value}
    (statusRelated : Correspondence.ResultRel .unit status statusValue)
    (framed : CodeValue depth environment result (frameValue statusValue state storage logs cursor balances world)) :
    ∃ target final, CallTransportCorrespondence.ResponseRel response target ∧
      Evaluates environment store (AccountRuntime.childResult result depth) target final ∧
      StoreRetains store final := by
  have snapshotRelated : CodeValue depth environment (AccountRuntime.second result)
      (bundleValues [.word state.storage.exit, .word state.storage.returnOffset,
        .word state.storage.returnSize, WordMapping.encode state.memory.words, storage, logs, cursor, balances, world]) :=
    fun extra here => .second (framed extra here)
  have exitRelated := snapshotRelated.part (index := 0) rfl
  have offsetRelated := snapshotRelated.part (index := 1) rfl
  have lengthRelated := snapshotRelated.part (index := 2) rfl
  have memoryRelated := snapshotRelated.part (index := 3) rfl
  have statusEvaluated : Evaluates environment store (AccountRuntime.first result depth) statusValue store :=
    .first (framed.evaluates store)
  have test (kind : Nat) : Evaluates environment store
      (binary .wordEq (part 0 9 (AccountRuntime.second result)) (number kind) depth)
      (.bool (state.storage.exit == Word.ofNatModulo kind)) store :=
    .binary (exitRelated.evaluates store) .word rfl
  have copied (success : Bool) {data : Semantics.Result MemorySemantics.Entries}
      (extracted : MemorySnapshotSemantics.Extract state.memory.words state.storage.returnOffset state.storage.returnSize data) :
      ∃ target final, CallTransportCorrespondence.ResponseRel (ChildResultSemantics.response success state.storage.returnSize data) target ∧
        Evaluates environment store
          (bindResult Calls.responseType (fun depth => MemorySnapshot.extract
            (part 3 9 (AccountRuntime.second result) depth) (part 1 9 (AccountRuntime.second result) depth)
            (part 2 9 (AccountRuntime.second result) depth)) (fun data =>
              AccountRuntime.callResult (CodeBuilder.boolean success) data (part 2 9 (AccountRuntime.second result))) depth) target final ∧
        StoreRetains store final := by
    obtain ⟨target, final, related, evaluated, retained⟩ := MemorySnapshotCorrespondence.extract_preserves extracted
      (memoryRelated.evaluates store) (offsetRelated.evaluates store) (lengthRelated.evaluates store)
    cases related with
    | language reason =>
        exact ⟨.inLeft Calls.responseType (.word reason), final, .language _, LanguageResult.bind_failure Calls.responseType evaluated, retained⟩
    | returned entries =>
        refine ⟨.inRight .word (CallTransportCorrespondence.responseValue ⟨success, entries, state.storage.returnSize⟩),
          final, .returned _, ?_, retained⟩
        apply LanguageResult.bind_success Calls.responseType evaluated
        exact .inRight (.pair .bool (.pair (.var (by simp)) ((lengthRelated.prepend [WordMapping.encode entries]).evaluates final)))
  cases responded with
  | invalid exit =>
      refine ⟨.inRight .word (CallTransportCorrespondence.responseValue (AccountCallSemantics.emptyResponse false)), store, .returned _, ?_, .refl _⟩
      apply Evaluates.ifTrue (by simpa only [exit, beq_self_eq_true] using test 3)
      exact .inRight (.pair .bool (.pair (.construct .unit) .word))
  | reverted exit extracted =>
      obtain ⟨target, final, related, evaluated, retained⟩ := copied false extracted
      refine ⟨target, final, related, ?_, retained⟩
      apply Evaluates.ifFalse (by simpa only [exit, show (Word.ofNatModulo 2 == Word.ofNatModulo 3) = false from by decide +kernel] using test 3)
      exact .ifTrue (by simpa only [exit, beq_self_eq_true] using test 2) evaluated
  | returned exit extracted =>
      obtain ⟨target, final, related, evaluated, retained⟩ := copied true extracted
      refine ⟨target, final, related, ?_, retained⟩
      apply Evaluates.ifFalse (by simpa only [exit, show (Word.ofNatModulo 1 == Word.ofNatModulo 3) = false from by decide +kernel] using test 3)
      apply Evaluates.ifFalse (by simpa only [exit, show (Word.ofNatModulo 1 == Word.ofNatModulo 2) = false from by decide +kernel] using test 2)
      exact .ifTrue (by simpa only [exit, beq_self_eq_true] using test 1) evaluated
  | failed invalid reverted returned failed =>
      subst status
      cases statusRelated with
      | language reason =>
          refine ⟨.inLeft Calls.responseType (.word reason), store, .language _, ?_, .refl _⟩
          apply Evaluates.ifFalse (by simpa only [beq_eq_false_iff_ne.mpr invalid] using test 3)
          apply Evaluates.ifFalse (by simpa only [beq_eq_false_iff_ne.mpr reverted] using test 2)
          apply Evaluates.ifFalse (by simpa only [beq_eq_false_iff_ne.mpr returned] using test 1)
          exact .caseLeft statusEvaluated (.inLeft (.var rfl))
  | completed invalid reverted returned finished =>
      subst status
      cases statusRelated with
      | value related =>
          cases related
          refine ⟨.inRight .word (CallTransportCorrespondence.responseValue (AccountCallSemantics.emptyResponse true)), store, .returned _, ?_, .refl _⟩
          apply Evaluates.ifFalse (by simpa only [beq_eq_false_iff_ne.mpr invalid] using test 3)
          apply Evaluates.ifFalse (by simpa only [beq_eq_false_iff_ne.mpr reverted] using test 2)
          apply Evaluates.ifFalse (by simpa only [beq_eq_false_iff_ne.mpr returned] using test 1)
          exact .caseRight statusEvaluated (.inRight (.pair .bool (.pair (.construct .unit) .word)))

end Solcore.Frontend.RustHull.ChildResultCorrespondence
