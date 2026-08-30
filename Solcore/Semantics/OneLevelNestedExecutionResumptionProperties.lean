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
    (mode : Mode initialWorld rootContract rootInvocation)
    (reachable : Reachable registry mode) :
    resumeWithFuel (runMode registry fuel mode reachable) additional =
      runMode registry (fuel + additional) mode reachable := by
  induction fuel, mode, reachable using runMode.induct registry
      generalizing additional with
  | case1 fuel frame reachable value stepEq active =>
      have active_eq : active = reachable := Subsingleton.elim _ _
      subst active
      have prefixView :
          (runMode registry fuel (.root frame) reachable).view =
            .completed (frame.finalizeDone value stepEq) := by
        rw [runMode.eq_1]
        split <;> rename_i _ branchEq
        all_goals cases branchEq.symm.trans stepEq <;> rfl
      have summedView :
          (runMode registry (fuel + additional) (.root frame) reachable).view =
            .completed (frame.finalizeDone value stepEq) := by
        rw [runMode.eq_1]
        split <;> rename_i _ branchEq
        all_goals cases branchEq.symm.trans stepEq <;> rfl
      apply Result.eq_of_view_eq
      simp [resumeWithFuel, prefixView, summedView]
  | case2 frame reachable next stepEq active =>
      have active_eq : active = reachable := Subsingleton.elim _ _
      subst active
      have prefixView :
          (runMode registry 0 (.root frame) reachable).view =
            .outOfFuel registry (.root frame) reachable := by
        rw [runMode.eq_1]
        split <;> rename_i _ branchEq
        all_goals cases branchEq.symm.trans stepEq <;> rfl
      apply Result.eq_of_view_eq
      simp [resumeWithFuel, prefixView]
  | case3 frame reachable next stepEq remaining active ih =>
      have active_eq : active = reachable := Subsingleton.elim _ _
      subst active
      have prefixEq :
          runMode registry remaining.succ (.root frame) reachable =
            runMode registry remaining
              (.root (frame.afterNext next stepEq))
              (.rootNext reachable stepEq) := by
        apply Result.eq_of_view_eq
        rw [runMode.eq_1]
        split <;> rename_i _ branchEq
        all_goals cases branchEq.symm.trans stepEq <;> rfl
      have summedEq :
          runMode registry (remaining.succ + additional) (.root frame)
              reachable =
            runMode registry (remaining + additional)
              (.root (frame.afterNext next stepEq))
              (.rootNext reachable stepEq) := by
        rw [Nat.succ_add]
        apply Result.eq_of_view_eq
        rw [runMode.eq_1]
        split <;> rename_i _ branchEq
        all_goals cases branchEq.symm.trans stepEq <;> rfl
      rw [prefixEq, summedEq]
      exact ih additional
  | case4 frame reachable suspension stepEq active =>
      have active_eq : active = reachable := Subsingleton.elim _ _
      subst active
      have prefixView :
          (runMode registry 0 (.root frame) reachable).view =
            .outOfFuel registry (.root frame) reachable := by
        rw [runMode.eq_1]
        split <;> rename_i _ branchEq
        all_goals cases branchEq.symm.trans stepEq <;> rfl
      apply Result.eq_of_view_eq
      simp [resumeWithFuel, prefixView]
  | case5 frame reachable suspension stepEq remaining active ih =>
      have active_eq : active = reachable := Subsingleton.elim _ _
      subst active
      have prefixEq :
          runMode registry remaining.succ (.root frame) reachable =
            runMode registry remaining
              (frame.afterSuspension registry suspension stepEq)
              (.rootSuspended reachable stepEq) := by
        apply Result.eq_of_view_eq
        rw [runMode.eq_1]
        split <;> rename_i _ branchEq
        all_goals cases branchEq.symm.trans stepEq <;> rfl
      have summedEq :
          runMode registry (remaining.succ + additional) (.root frame)
              reachable =
            runMode registry (remaining + additional)
              (frame.afterSuspension registry suspension stepEq)
              (.rootSuspended reachable stepEq) := by
        rw [Nat.succ_add]
        apply Result.eq_of_view_eq
        rw [runMode.eq_1]
        split <;> rename_i _ branchEq
        all_goals cases branchEq.symm.trans stepEq <;> rfl
      rw [prefixEq, summedEq]
      exact ih additional
  | case6 fuel frame reachable value stepEq active ih =>
      have active_eq : active = reachable := Subsingleton.elim _ _
      subst active
      have prefixEq :
          runMode registry fuel (.child frame) reachable =
            runMode registry fuel
              (.root (frame.resumeRoot (frame.outcomeDone value stepEq)))
              (.childDone reachable stepEq) := by
        apply Result.eq_of_view_eq
        rw [runMode.eq_2]
        split <;> rename_i _ branchEq
        all_goals cases branchEq.symm.trans stepEq <;> rfl
      have summedEq :
          runMode registry (fuel + additional) (.child frame) reachable =
            runMode registry (fuel + additional)
              (.root (frame.resumeRoot (frame.outcomeDone value stepEq)))
              (.childDone reachable stepEq) := by
        apply Result.eq_of_view_eq
        rw [runMode.eq_2]
        split <;> rename_i _ branchEq
        all_goals cases branchEq.symm.trans stepEq <;> rfl
      rw [prefixEq, summedEq]
      exact ih additional
  | case7 frame reachable next stepEq active =>
      have active_eq : active = reachable := Subsingleton.elim _ _
      subst active
      have prefixView :
          (runMode registry 0 (.child frame) reachable).view =
            .outOfFuel registry (.child frame) reachable := by
        rw [runMode.eq_2]
        split <;> rename_i _ branchEq
        all_goals cases branchEq.symm.trans stepEq <;> rfl
      apply Result.eq_of_view_eq
      simp [resumeWithFuel, prefixView]
  | case8 frame reachable next stepEq remaining active ih =>
      have active_eq : active = reachable := Subsingleton.elim _ _
      subst active
      have prefixEq :
          runMode registry remaining.succ (.child frame) reachable =
            runMode registry remaining
              (.child (frame.afterNext next stepEq))
              (.childNext reachable stepEq) := by
        apply Result.eq_of_view_eq
        rw [runMode.eq_2]
        split <;> rename_i _ branchEq
        all_goals cases branchEq.symm.trans stepEq <;> rfl
      have summedEq :
          runMode registry (remaining.succ + additional) (.child frame)
              reachable =
            runMode registry (remaining + additional)
              (.child (frame.afterNext next stepEq))
              (.childNext reachable stepEq) := by
        rw [Nat.succ_add]
        apply Result.eq_of_view_eq
        rw [runMode.eq_2]
        split <;> rename_i _ branchEq
        all_goals cases branchEq.symm.trans stepEq <;> rfl
      rw [prefixEq, summedEq]
      exact ih additional
  | case9 frame reachable suspension stepEq active =>
      have active_eq : active = reachable := Subsingleton.elim _ _
      subst active
      have prefixView :
          (runMode registry 0 (.child frame) reachable).view =
            .outOfFuel registry (.child frame) reachable := by
        rw [runMode.eq_2]
        split <;> rename_i _ branchEq
        all_goals cases branchEq.symm.trans stepEq <;> rfl
      apply Result.eq_of_view_eq
      simp [resumeWithFuel, prefixView]
  | case10 frame reachable suspension stepEq remaining active ih =>
      have active_eq : active = reachable := Subsingleton.elim _ _
      subst active
      have prefixEq :
          runMode registry remaining.succ (.child frame) reachable =
            runMode registry remaining
              (.child (frame.afterHandledSuspension suspension stepEq))
              (.childSuspended reachable stepEq) := by
        apply Result.eq_of_view_eq
        rw [runMode.eq_2]
        split <;> rename_i _ branchEq
        all_goals cases branchEq.symm.trans stepEq <;> rfl
      have summedEq :
          runMode registry (remaining.succ + additional) (.child frame)
              reachable =
            runMode registry (remaining + additional)
              (.child (frame.afterHandledSuspension suspension stepEq))
              (.childSuspended reachable stepEq) := by
        rw [Nat.succ_add]
        apply Result.eq_of_view_eq
        rw [runMode.eq_2]
        split <;> rename_i _ branchEq
        all_goals cases branchEq.symm.trans stepEq <;> rfl
      rw [prefixEq, summedEq]
      exact ih additional

/-- A terminal nested result remains terminal under every added budget. -/
@[simp] theorem resumeWithFuel_completed
    {initialWorld : WorldState}
    {rootContract : CheckedCoreContract}
    {rootInvocation : TopLevelInvocation}
    (result : Result initialWorld rootContract rootInvocation)
    (terminal : TerminalResult initialWorld rootContract rootInvocation)
    (completed : result.view = .completed terminal)
    (additional : Nat) :
    resumeWithFuel result additional = result := by
  simp [resumeWithFuel, completed]

/-- An exhausted result resumes with its retained registry and active mode. -/
@[simp] theorem resumeWithFuel_outOfFuel
    {initialWorld : WorldState}
    {rootContract : CheckedCoreContract}
    {rootInvocation : TopLevelInvocation}
    (registry : CheckedContractRegistry)
    (mode : Mode initialWorld rootContract rootInvocation)
    (reachable : Reachable registry mode)
    (result : Result initialWorld rootContract rootInvocation)
    (exhausted : result.view = .outOfFuel registry mode reachable)
    (additional : Nat) :
    resumeWithFuel result additional =
      runMode registry additional mode reachable := by
  simp [resumeWithFuel, exhausted]

/-- Zero additional fuel is an identity for every actual scheduler run. -/
@[simp] theorem resumeWithFuel_runMode_zero
    {initialWorld : WorldState}
    {rootContract : CheckedCoreContract}
    {rootInvocation : TopLevelInvocation}
    (registry : CheckedContractRegistry)
    (fuel : Nat)
    (mode : Mode initialWorld rootContract rootInvocation)
    (reachable : Reachable registry mode) :
    resumeWithFuel (runMode registry fuel mode reachable) 0 =
      runMode registry fuel mode reachable := by
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
  cases observed : result.view with
  | completed terminal =>
      simp [resumeWithFuel, observed]
  | outOfFuel registry mode reachable =>
      rw [resumeWithFuel_outOfFuel registry mode reachable result observed]
      rw [resumeWithFuel_outOfFuel registry mode reachable result observed]
      exact resumeWithFuel_runMode registry first second mode reachable

/-- Two additions after an actual run equal one run at the total budget. -/
theorem resumeWithFuel_runMode_add
    {initialWorld : WorldState}
    {rootContract : CheckedCoreContract}
    {rootInvocation : TopLevelInvocation}
    (registry : CheckedContractRegistry)
    (fuel first second : Nat)
    (mode : Mode initialWorld rootContract rootInvocation)
    (reachable : Reachable registry mode) :
    resumeWithFuel
        (resumeWithFuel (runMode registry fuel mode reachable) first) second =
      runMode registry (fuel + first + second) mode reachable := by
  rw [resumeWithFuel_runMode, resumeWithFuel_runMode]

/-- Splitting fuel at the installed-root API is exactly one larger run. -/
theorem resumeWithFuel_run
    {initialWorld : WorldState}
    (rootContract : CheckedCoreContract)
    (rootInvocation : TopLevelInvocation)
    (installed :
      InstalledCheckedCoreContract initialWorld rootInvocation.target
        rootContract)
    (registry : CheckedContractRegistry)
    (fuel additional : Nat) :
    resumeWithFuel
        (run rootContract rootInvocation installed registry fuel) additional =
      run rootContract rootInvocation installed registry
        (fuel + additional) := by
  exact resumeWithFuel_runMode registry fuel additional
    (Mode.initialRoot rootContract rootInvocation installed)
    (.initial installed)

/-- Zero additional fuel is an identity for every installed-root run. -/
@[simp] theorem resumeWithFuel_run_zero
    {initialWorld : WorldState}
    (rootContract : CheckedCoreContract)
    (rootInvocation : TopLevelInvocation)
    (installed :
      InstalledCheckedCoreContract initialWorld rootInvocation.target
        rootContract)
    (registry : CheckedContractRegistry)
    (fuel : Nat) :
    resumeWithFuel
        (run rootContract rootInvocation installed registry fuel) 0 =
      run rootContract rootInvocation installed registry fuel := by
  rw [resumeWithFuel_run]
  simp only [Nat.add_zero]

/-- Sequential resumption at the public API uses the summed shared budget. -/
theorem resumeWithFuel_run_add
    {initialWorld : WorldState}
    (rootContract : CheckedCoreContract)
    (rootInvocation : TopLevelInvocation)
    (installed :
      InstalledCheckedCoreContract initialWorld rootInvocation.target
        rootContract)
    (registry : CheckedContractRegistry)
    (fuel first second : Nat) :
    resumeWithFuel
        (resumeWithFuel
          (run rootContract rootInvocation installed registry fuel) first)
        second =
      run rootContract rootInvocation installed registry
        (fuel + first + second) := by
  rw [resumeWithFuel_run, resumeWithFuel_run]

end Solcore.Semantics.OneLevelNestedExecution
