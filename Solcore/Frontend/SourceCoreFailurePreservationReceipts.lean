import Solcore.Frontend.SourceCoreExecution

/-! Actual finite native failure determines the failed branch of the same
public resume event. Failure requires no output decoding budget. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.Frontend.SourceCoreIndexedSession

theorem Checkpoint.ResumeAt.native_failed {artifact : Artifact}
    {checkpoint : Checkpoint artifact} {fuel boundaryFuel : Nat} {outcome : Outcome artifact}
    {native : Core.Value} {store : Core.Store} {reason : Core.Word}
    (receipt : checkpoint.ResumeAt fuel boundaryFuel outcome)
    (completed : checkpoint.NativeDone fuel native store)
    (decoded : Core.LanguageResult.decode? native = some (.failed reason)) :
    ∃ returned : Session artifact, outcome = .failed reason returned ∧
      checkpoint.FailedResultAt fuel native store reason returned := by
  unfold Checkpoint.NativeDone at completed
  rcases receipt with ⟨generation, value, actualStore, executed, same⟩ | ⟨state, exhausted, suspended⟩
  · rw [completed] at executed
    cases executed
    obtain ⟨returned, failed, receipt⟩ := checkpoint.native_failed_result_receipt
      (generation := generation) (boundaryFuel := boundaryFuel) completed decoded
    exact ⟨returned, same.symm.trans failed, receipt⟩
  · rw [completed] at exhausted
    cases exhausted

end Solcore.Frontend.SourceCoreIndexedSession

namespace Solcore.Frontend.SourceCoreExecution

theorem Checkpoint.ResumeAt.native_failed {artifact : Artifact}
    {checkpoint : Checkpoint artifact} {fuel boundaryFuel : Nat} {outcome : Outcome artifact}
    {native : SourceCoreIndexedSession.Artifact} {indexed : SourceCoreIndexedSession.Checkpoint native}
    {value : Core.Value} {store : Core.Store} {reason : Core.Word}
    (atCheckpoint : checkpoint.IndexedAt indexed)
    (receipt : checkpoint.ResumeAt fuel boundaryFuel outcome)
    (completed : indexed.NativeDone fuel value store)
    (decoded : Core.LanguageResult.decode? value = some (.failed reason)) :
    ∃ returned : Session artifact, outcome = .failed reason returned := by
  rcases artifact with ⟨compiled, opened⟩
  cases opened with
  | empty selected => rcases checkpoint with ⟨impossible⟩; exact nomatch impossible
  | indexed recipe selected actualNative atRecipe =>
      rcases checkpoint with ⟨actualCheckpoint⟩
      rcases atCheckpoint with ⟨rfl, same⟩
      cases eq_of_heq same
      obtain ⟨actualOutcome, resumed, returned⟩ := receipt
      obtain ⟨actual, failed, _receipt⟩ := resumed.native_failed completed decoded
      rw [failed] at returned
      cases outcome with
      | failed publicReason publicSession =>
          have reasonEq : reason = publicReason := (Outcome.failed.inj returned).1
          exact ⟨publicSession, by rw [reasonEq]⟩
      | succeeded completion => cases returned
      | outOfFuel checkpoint => cases returned
      | exportError error session => cases returned

end Solcore.Frontend.SourceCoreExecution
