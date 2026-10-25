import Solcore.Frontend.RustHull.ChildResultCorrespondence
import Solcore.Frontend.RustHull.ChildFrameSemantics
import Solcore.Frontend.RustHull.RuntimeReturnDataEffectsFrameCorrespondence

/-! The actual frame completion lookup and child-result wrapper agree with
the independent exit rules, including lookup faults and revert data. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.ChildFrameCorrespondence
open Core Correspondence ScalarExecution CodeBuilder

theorem completion_components {status : Semantics.Result Semantics.Value} {statusValue : Value}
    {state : RuntimeReturnDataEffectsSemantics.State} {accounts : StorageCorrespondence.Accounts}
    (related : ResultRel .unit status statusValue)
    (world : accounts.map Prod.fst = state.runtime.runtime.runtime.runtime.storage.world) :
    ∃ completed storage,
      ResultRel .unit (ChildFrameSemantics.completedStatus status state.runtime.runtime.runtime.runtime) completed ∧
      frameCompletionValue statusValue (RuntimeReturnDataEffectsFrameCorrespondence.snapshotValues state accounts)
        (StorageCorrespondence.get accounts state.runtime.runtime.runtime.runtime.storage.address
          state.runtime.runtime.runtime.runtime.storage.complete) =
      ChildResultCorrespondence.frameValue completed state.runtime.runtime.runtime.runtime storage
        (WordMapping.encode state.runtime.runtime.words) (.word state.runtime.runtime.cursor)
        (WordMapping.encode state.runtime.balances) (StorageCorrespondence.world accounts) := by
  have source := StorageCorrespondence.get_source accounts state.runtime.runtime.runtime.runtime.storage.address
    state.runtime.runtime.runtime.runtime.storage.complete
  rw [world] at source
  cases found : StorageCorrespondence.get accounts state.runtime.runtime.runtime.runtime.storage.address
      state.runtime.runtime.runtime.runtime.storage.complete with
  | error reason =>
      have sourceFound : StorageSemantics.get state.runtime.runtime.runtime.runtime.storage.world
          state.runtime.runtime.runtime.runtime.storage.address state.runtime.runtime.runtime.runtime.storage.complete = .error reason := by
        simpa only [found, Except.map] using source.symm
      refine ⟨.inLeft .unit (.word reason), WordMapping.encode [], ?_, ?_⟩
      · simp only [ChildFrameSemantics.completedStatus, sourceFound]
        exact .language _
      · rfl
  | ok account =>
      obtain ⟨account, identity⟩ := account
      have sourceFound : StorageSemantics.get state.runtime.runtime.runtime.runtime.storage.world
          state.runtime.runtime.runtime.runtime.storage.address state.runtime.runtime.runtime.runtime.storage.complete = .ok account := by
        simpa only [found, Except.map] using source.symm
      exact ⟨statusValue, WordMapping.encode account.storage,
        by simpa only [ChildFrameSemantics.completedStatus, sourceFound] using related, by rfl⟩

theorem finish_evaluates {depth : Nat} {environment : Environment} {store : Store} {result : Code}
    {status : Semantics.Result Semantics.Value} {statusValue : Value}
    {state : RuntimeReturnDataEffectsSemantics.State} {accounts : StorageCorrespondence.Accounts}
    {response : Semantics.Result AccountCallSemantics.Response}
    (statusRelated : ResultRel .unit status statusValue)
    (world : accounts.map Prod.fst = state.runtime.runtime.runtime.runtime.storage.world)
    (responded : ChildResultSemantics.Respond
      (ChildFrameSemantics.completedStatus status state.runtime.runtime.runtime.runtime)
      state.runtime.runtime.runtime.runtime response)
    (framed : CodeValue depth environment result
      (frameCompletionValue statusValue (RuntimeReturnDataEffectsFrameCorrespondence.snapshotValues state accounts)
        (StorageCorrespondence.get accounts state.runtime.runtime.runtime.runtime.storage.address
          state.runtime.runtime.runtime.runtime.storage.complete))) :
    ∃ target final, CallTransportCorrespondence.ResponseRel response target ∧
      Core.Evaluates environment store (AccountRuntime.childResult result depth) target final ∧ StoreRetains store final := by
  obtain ⟨completed, storage, related, same⟩ := completion_components statusRelated world
  rw [same] at framed
  exact ChildResultCorrespondence.childResult_evaluates responded related framed

theorem bind_evaluates {depth : Nat} {environment : Environment} {initial store : Store}
    {function argument : Code}
    {status : Semantics.Result Semantics.Value} {statusValue : Value}
    {state : RuntimeReturnDataEffectsSemantics.State} {accounts : StorageCorrespondence.Accounts}
    {response : Semantics.Result AccountCallSemantics.Response}
    (statusRelated : ResultRel .unit status statusValue)
    (world : accounts.map Prod.fst = state.runtime.runtime.runtime.runtime.storage.world)
    (responded : ChildResultSemantics.Respond
      (ChildFrameSemantics.completedStatus status state.runtime.runtime.runtime.runtime)
      state.runtime.runtime.runtime.runtime response)
    (called : Core.Evaluates environment initial (apply function argument depth)
      (frameCompletionValue statusValue (RuntimeReturnDataEffectsFrameCorrespondence.snapshotValues state accounts)
        (StorageCorrespondence.get accounts state.runtime.runtime.runtime.runtime.storage.address
          state.runtime.runtime.runtime.runtime.storage.complete)) store) :
    ∃ target final, CallTransportCorrespondence.ResponseRel response target ∧
      Core.Evaluates environment initial (bind (apply function argument) AccountRuntime.childResult depth) target final ∧
      StoreRetains store final := by
  obtain ⟨target, final, related, evaluated, retained⟩ := finish_evaluates (store := store)
    statusRelated world responded (CodeValue.bound depth environment _)
  exact ⟨target, final, related, .letE called evaluated, retained⟩

end Solcore.Frontend.RustHull.ChildFrameCorrespondence
