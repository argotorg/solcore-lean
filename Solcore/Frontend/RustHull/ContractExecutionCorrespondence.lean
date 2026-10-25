import Solcore.Frontend.RustHull.Contract
import Solcore.Core.FuelResumptionProperties

/-! Actual contract receipt export and genuine checkpoint chains retain the
transition cost and result of the compiled runtime expression. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.Contract

theorem finish_not_checkpoint (limit : Nat) (value : Core.Value) (checkpoint : Core.State) :
    (finish limit value).outcome ≠ .outOfFuel checkpoint := by
  intro equality
  unfold finish at equality
  split at equality <;> try cases equality
  all_goals
    dsimp only at equality
    split at equality <;> try cases equality
  all_goals
    try split at equality <;> try cases equality
  all_goals
    conv at equality => lhs; whnf
    dsimp only [Pure.pure, Bind.bind] at equality
  repeat (any_goals (first | cases equality | split at equality))

theorem resumeWithReceipt_checkpoint_iff {start checkpoint : Core.State} {fuel limit : Nat} :
    (resumeWithReceipt start fuel limit).outcome = .outOfFuel checkpoint ↔
      Core.runStateful fuel start = .outOfFuel checkpoint := by
  cases executed : Core.runStateful fuel start with
  | done value store =>
      simp only [resumeWithReceipt, executed]
      exact iff_of_false (finish_not_checkpoint limit value checkpoint) (by intro impossible; cases impossible)
  | outOfFuel suspended => simp only [resumeWithReceipt, executed, Outcome.outOfFuel.injEq, Core.StatefulRunResult.outOfFuel.injEq]
  | fault error state => simp only [resumeWithReceipt, executed, reduceCtorEq]

/-- All steps use the checkpoint actually returned by the previous public
receipt, with a fixed export limit and cumulative additional fuel. -/
inductive ReceiptResumes (limit : Nat) : Receipt → Nat → Receipt → Prop where
  | refl (receipt : Receipt) : ReceiptResumes limit receipt 0 receipt
  | step {first previous : Receipt} {spent : Nat} {checkpoint : Core.State}
      (path : ReceiptResumes limit first spent previous)
      (exhausted : previous.outcome = .outOfFuel checkpoint) (additional : Nat) :
      ReceiptResumes limit first (spent + additional) (resumeWithReceipt checkpoint additional limit)

theorem ReceiptResumes.eq_combined_run {limit : Nat} {first last : Receipt} {additional : Nat}
    (path : ReceiptResumes limit first additional last) (prepared : Prepared) (fuel : Nat)
    (initial : first = runWithReceipt prepared fuel limit) :
    last = runWithReceipt prepared (fuel + additional) limit := by
  induction path with
  | refl => simpa only [Nat.add_zero] using initial
  | @step previous spent checkpoint path exhausted more ih =>
      have stopped := (resumeWithReceipt_checkpoint_iff).mp (ih.symm ▸ exhausted)
      simp only [runWithReceipt, resumeWithReceipt, Core.runStateful_resume stopped more, Nat.add_assoc]

theorem evaluation_run_complete {prepared : Prepared} {value : Core.Value} {store : Core.Store}
    (evaluation : Core.Evaluates [] [] prepared.expression value store) :
    ∃ required, ∀ fuel, required ≤ fuel → ∀ limit,
      runWithReceipt prepared fuel limit = finish limit value := by
  obtain ⟨required, completed⟩ := Core.evaluation_runStateful_complete_with_sufficient_fuel evaluation
  exact ⟨required, fun fuel enough limit => by
    simp only [runWithReceipt, resumeWithReceipt, completed fuel enough]⟩

theorem evaluation_resumes_exact {prepared : Prepared} {value : Core.Value} {store : Core.Store}
    (evaluation : Core.Evaluates [] [] prepared.expression value store) :
    ∃ required, ∀ fuel additional limit last,
      ReceiptResumes limit (runWithReceipt prepared fuel limit) additional last →
      (last = finish limit value ↔ required ≤ fuel + additional) ∧
      ((∃ checkpoint, last.outcome = .outOfFuel checkpoint) ↔ fuel + additional < required) := by
  obtain ⟨required, path⟩ := evaluation.toSteps
  refine ⟨required, ?_⟩
  intro fuel additional limit last resumed
  rw [resumed.eq_combined_run prepared fuel rfl]
  have exhausted : (∃ checkpoint, (runWithReceipt prepared (fuel + additional) limit).outcome = .outOfFuel checkpoint) ↔
      fuel + additional < required := by
    simpa only [runWithReceipt, resumeWithReceipt_checkpoint_iff] using path.runStateful_outOfFuel_iff (fuel := fuel + additional)
  refine ⟨⟨?_, ?_⟩, exhausted⟩
  · intro completed
    by_cases enough : required ≤ fuel + additional
    · exact enough
    exfalso
    obtain ⟨checkpoint, found⟩ := exhausted.mpr (by omega)
    rw [completed] at found
    exact finish_not_checkpoint limit value checkpoint found
  · intro enough
    simp only [runWithReceipt, resumeWithReceipt, path.runStateful_done_iff.mpr enough]

end Solcore.Frontend.RustHull.Contract
