import Solcore.Semantics.OneLevelNestedExecutionResumption

/-! Exact split-fuel laws for one-level nested checked-Core execution. -/

set_option autoImplicit false

namespace Solcore.Semantics.OneLevelNestedExecution

/-- Resuming an actual bounded run is exactly one run at the summed budget. -/
theorem resumeWithFuel_runMode
    {initialWorld : WorldState}
    {rootContract : CheckedCoreContract}
    {rootInvocation : TopLevelInvocation}
    (registry : CheckedContractRegistry)
    (fuel additional : Nat)
    (mode : Mode initialWorld rootContract rootInvocation) :
    resumeWithFuel (runMode registry fuel mode) additional =
      runMode registry (fuel + additional) mode := by
  induction fuel, mode using runMode.induct registry generalizing additional with
  | case1 fuel frame value stepEq =>
      have prefixEq :
          runMode registry fuel (.root frame) =
            .completed (frame.finalizeDone value stepEq) := by
        rw [runMode.eq_1]
        split <;> rename_i _ branchEq
        all_goals
          cases branchEq.symm.trans stepEq <;> rfl
      have summedEq :
          runMode registry (fuel + additional) (.root frame) =
            .completed (frame.finalizeDone value stepEq) := by
        rw [runMode.eq_1]
        split <;> rename_i _ branchEq
        all_goals
          cases branchEq.symm.trans stepEq <;> rfl
      rw [prefixEq, summedEq]
      rfl
  | case2 frame next stepEq =>
      have prefixEq :
          runMode registry 0 (.root frame) =
            .outOfFuel registry (.root frame) := by
        rw [runMode.eq_1]
        split <;> rename_i _ branchEq
        all_goals
          cases branchEq.symm.trans stepEq <;> rfl
      rw [prefixEq]
      simp only [resumeWithFuel, Nat.zero_add]
  | case3 frame next stepEq remaining ih =>
      have prefixEq :
          runMode registry remaining.succ (.root frame) =
            runMode registry remaining
              (.root (frame.afterNext next stepEq)) := by
        rw [runMode.eq_1]
        split <;> rename_i _ branchEq
        all_goals
          cases branchEq.symm.trans stepEq <;> rfl
      have summedEq :
          runMode registry (remaining.succ + additional) (.root frame) =
            runMode registry (remaining + additional)
              (.root (frame.afterNext next stepEq)) := by
        rw [Nat.succ_add]
        rw [runMode.eq_1]
        split <;> rename_i _ branchEq
        all_goals
          cases branchEq.symm.trans stepEq <;> rfl
      rw [prefixEq, summedEq]
      exact ih additional
  | case4 frame suspension stepEq =>
      have prefixEq :
          runMode registry 0 (.root frame) =
            .outOfFuel registry (.root frame) := by
        rw [runMode.eq_1]
        split <;> rename_i _ branchEq
        all_goals
          cases branchEq.symm.trans stepEq <;> rfl
      rw [prefixEq]
      simp only [resumeWithFuel, Nat.zero_add]
  | case5 frame suspension stepEq remaining ih =>
      have prefixEq :
          runMode registry remaining.succ (.root frame) =
            runMode registry remaining
              (frame.afterSuspension registry suspension stepEq) := by
        rw [runMode.eq_1]
        split <;> rename_i _ branchEq
        all_goals
          cases branchEq.symm.trans stepEq <;> rfl
      have summedEq :
          runMode registry (remaining.succ + additional) (.root frame) =
            runMode registry (remaining + additional)
              (frame.afterSuspension registry suspension stepEq) := by
        rw [Nat.succ_add]
        rw [runMode.eq_1]
        split <;> rename_i _ branchEq
        all_goals
          cases branchEq.symm.trans stepEq <;> rfl
      rw [prefixEq, summedEq]
      exact ih additional
  | case6 fuel frame value stepEq ih =>
      have prefixEq :
          runMode registry fuel (.child frame) =
            runMode registry fuel
              (.root (frame.resumeRoot (frame.outcomeDone value stepEq))) := by
        rw [runMode.eq_2]
        split <;> rename_i _ branchEq
        all_goals
          cases branchEq.symm.trans stepEq <;> rfl
      have summedEq :
          runMode registry (fuel + additional) (.child frame) =
            runMode registry (fuel + additional)
              (.root (frame.resumeRoot (frame.outcomeDone value stepEq))) := by
        rw [runMode.eq_2]
        split <;> rename_i _ branchEq
        all_goals
          cases branchEq.symm.trans stepEq <;> rfl
      rw [prefixEq, summedEq]
      exact ih additional
  | case7 frame next stepEq =>
      have prefixEq :
          runMode registry 0 (.child frame) =
            .outOfFuel registry (.child frame) := by
        rw [runMode.eq_2]
        split <;> rename_i _ branchEq
        all_goals
          cases branchEq.symm.trans stepEq <;> rfl
      rw [prefixEq]
      simp only [resumeWithFuel, Nat.zero_add]
  | case8 frame next stepEq remaining ih =>
      have prefixEq :
          runMode registry remaining.succ (.child frame) =
            runMode registry remaining
              (.child (frame.afterNext next stepEq)) := by
        rw [runMode.eq_2]
        split <;> rename_i _ branchEq
        all_goals
          cases branchEq.symm.trans stepEq <;> rfl
      have summedEq :
          runMode registry (remaining.succ + additional) (.child frame) =
            runMode registry (remaining + additional)
              (.child (frame.afterNext next stepEq)) := by
        rw [Nat.succ_add]
        rw [runMode.eq_2]
        split <;> rename_i _ branchEq
        all_goals
          cases branchEq.symm.trans stepEq <;> rfl
      rw [prefixEq, summedEq]
      exact ih additional
  | case9 frame suspension stepEq =>
      have prefixEq :
          runMode registry 0 (.child frame) =
            .outOfFuel registry (.child frame) := by
        rw [runMode.eq_2]
        split <;> rename_i _ branchEq
        all_goals
          cases branchEq.symm.trans stepEq <;> rfl
      rw [prefixEq]
      simp only [resumeWithFuel, Nat.zero_add]
  | case10 frame suspension stepEq remaining ih =>
      have prefixEq :
          runMode registry remaining.succ (.child frame) =
            runMode registry remaining
              (.child (frame.afterHandledSuspension suspension stepEq)) := by
        rw [runMode.eq_2]
        split <;> rename_i _ branchEq
        all_goals
          cases branchEq.symm.trans stepEq <;> rfl
      have summedEq :
          runMode registry (remaining.succ + additional) (.child frame) =
            runMode registry (remaining + additional)
              (.child (frame.afterHandledSuspension suspension stepEq)) := by
        rw [Nat.succ_add]
        rw [runMode.eq_2]
        split <;> rename_i _ branchEq
        all_goals
          cases branchEq.symm.trans stepEq <;> rfl
      rw [prefixEq, summedEq]
      exact ih additional

/-- A terminal nested result remains terminal under every added budget. -/
@[simp] theorem resumeWithFuel_completed
    {initialWorld : WorldState}
    {rootContract : CheckedCoreContract}
    {rootInvocation : TopLevelInvocation}
    (terminal : TerminalResult initialWorld rootContract rootInvocation)
    (additional : Nat) :
    resumeWithFuel (.completed terminal) additional = .completed terminal :=
  rfl

/-- An exhausted result resumes with its retained registry and active mode. -/
@[simp] theorem resumeWithFuel_outOfFuel
    {initialWorld : WorldState}
    {rootContract : CheckedCoreContract}
    {rootInvocation : TopLevelInvocation}
    (registry : CheckedContractRegistry)
    (mode : Mode initialWorld rootContract rootInvocation)
    (additional : Nat) :
    resumeWithFuel (.outOfFuel registry mode) additional =
      runMode registry additional mode :=
  rfl

/-- Zero additional fuel is an identity for every actual scheduler run. -/
@[simp] theorem resumeWithFuel_runMode_zero
    {initialWorld : WorldState}
    {rootContract : CheckedCoreContract}
    {rootInvocation : TopLevelInvocation}
    (registry : CheckedContractRegistry)
    (fuel : Nat)
    (mode : Mode initialWorld rootContract rootInvocation) :
    resumeWithFuel (runMode registry fuel mode) 0 =
      runMode registry fuel mode := by
  rw [resumeWithFuel_runMode]
  simp only [Nat.add_zero]

/-- Sequential additions associate for every retained scheduler result. -/
theorem resumeWithFuel_add
    {initialWorld : WorldState}
    {rootContract : CheckedCoreContract}
    {rootInvocation : TopLevelInvocation}
    (result : Result initialWorld rootContract rootInvocation)
    (first second : Nat) :
    resumeWithFuel (resumeWithFuel result first) second =
      resumeWithFuel result (first + second) := by
  cases result with
  | completed terminal => rfl
  | outOfFuel registry mode =>
      exact resumeWithFuel_runMode registry first second mode

/-- Two additions after an actual run equal one run at the total budget. -/
theorem resumeWithFuel_runMode_add
    {initialWorld : WorldState}
    {rootContract : CheckedCoreContract}
    {rootInvocation : TopLevelInvocation}
    (registry : CheckedContractRegistry)
    (fuel first second : Nat)
    (mode : Mode initialWorld rootContract rootInvocation) :
    resumeWithFuel
        (resumeWithFuel (runMode registry fuel mode) first) second =
      runMode registry (fuel + first + second) mode := by
  rw [resumeWithFuel_runMode, resumeWithFuel_runMode]

end Solcore.Semantics.OneLevelNestedExecution
