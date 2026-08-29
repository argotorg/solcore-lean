import Solcore.Semantics.HostDriverFuelProperties

/-! Relational completeness of generic handled host execution. -/

set_option autoImplicit false

namespace Solcore.Semantics

universe u

namespace HostDriver

private theorem run_done_complete_of_steps
    {Context : Type u}
    (handler : HostHandler Context)
    {spent fuel : Nat}
    {startContext finalContext : Context}
    {start finish : Core.State}
    {value : Core.Value}
    (path :
      HandledSteps handler spent startContext start finalContext finish)
    (terminal : Core.hostAdvance finish = .done value)
    (enough : spent ≤ fuel) :
    run handler startContext fuel start =
      ⟨finalContext, .done value finish.store⟩ := by
  induction path generalizing fuel with
  | core corePath =>
      apply run_of_done
      exact Core.hostRun_done_complete_of_steps corePath terminal enough
  | @handle prefixSteps suffixSteps context nextContext finalContext
      start requestState resumed finish suspension prefixPath emission
      handled suffix ih =>
      let remainingFuel := fuel - prefixSteps - 1
      have accounting :
          prefixSteps + remainingFuel + 1 = fuel := by
        dsimp [remainingFuel]
        omega
      have suffixEnough : suffixSteps ≤ remainingFuel := by
        dsimp [remainingFuel]
        omega
      have execution :
          Core.hostRun fuel start =
            .suspended suspension remainingFuel :=
        Core.hostRun_suspended_complete_of_steps
          prefixPath emission accounting
      rw [run_of_suspended handler context fuel remainingFuel start
        suspension execution]
      rw [handled]
      exact ih terminal suffixEnough

/-- A bounded handled path to a final state replays to the exact done result. -/
theorem run_done_complete
    {Context : Type u}
    (handler : HostHandler Context)
    {spent fuel : Nat}
    {startContext finalContext : Context}
    {start : Core.State}
    {value : Core.Value}
    {store : Core.Store}
    (path :
      HandledSteps handler spent startContext start finalContext
        (Core.State.final value store))
    (enough : spent ≤ fuel) :
    run handler startContext fuel start =
      ⟨finalContext, .done value store⟩ := by
  exact run_done_complete_of_steps handler path
    (Core.hostAdvance_done_iff.mpr ⟨store, rfl⟩) enough

/-- A bounded handled path to a raw fault replays to that exact fault result. -/
theorem run_fault_complete
    {Context : Type u}
    (handler : HostHandler Context)
    {spent fuel : Nat}
    {startContext finalContext : Context}
    {start faultState : Core.State}
    {error : Core.MachineFault}
    (path :
      HandledSteps handler spent startContext start finalContext faultState)
    (terminal : Core.hostAdvance faultState = .fault error)
    (enough : spent ≤ fuel) :
    run handler startContext fuel start =
      ⟨finalContext, .fault error faultState⟩ := by
  induction path generalizing fuel with
  | core corePath =>
      apply run_of_fault
      exact Core.hostRun_fault_complete_of_steps corePath terminal enough
  | @handle prefixSteps suffixSteps context nextContext finalContext
      start requestState resumed finish suspension prefixPath emission
      handled suffix ih =>
      let remainingFuel := fuel - prefixSteps - 1
      have accounting :
          prefixSteps + remainingFuel + 1 = fuel := by
        dsimp [remainingFuel]
        omega
      have suffixEnough : suffixSteps ≤ remainingFuel := by
        dsimp [remainingFuel]
        omega
      have execution :
          Core.hostRun fuel start =
            .suspended suspension remainingFuel :=
        Core.hostRun_suspended_complete_of_steps
          prefixPath emission accounting
      rw [run_of_suspended handler context fuel remainingFuel start
        suspension execution]
      rw [handled]
      exact ih terminal suffixEnough

/--
An exact-length handled path to a transition- or request-ready state replays to
exhaustion.
-/
theorem run_outOfFuel_complete
    {Context : Type u}
    (handler : HostHandler Context)
    {fuel : Nat}
    {startContext finalContext : Context}
    {start exhausted : Core.State}
    (path :
      HandledSteps handler fuel startContext start finalContext exhausted)
    (ready :
      (∃ next, Core.HostTransition exhausted next) ∨
        ∃ suspension, Core.HostRequestEmission exhausted suspension) :
    run handler startContext fuel start =
      ⟨finalContext, .outOfFuel exhausted⟩ := by
  induction path with
  | core corePath =>
      apply run_of_outOfFuel
      exact Core.hostRun_outOfFuel_complete corePath ready
  | @handle prefixSteps suffixSteps context nextContext finalContext
      start requestState resumed finish suspension prefixPath emission
      handled suffix ih =>
      have accounting :
          prefixSteps + suffixSteps + 1 =
            prefixSteps + 1 + suffixSteps := by
        omega
      have execution :
          Core.hostRun (prefixSteps + 1 + suffixSteps) start =
            .suspended suspension suffixSteps :=
        Core.hostRun_suspended_complete_of_steps
          prefixPath emission accounting
      rw [run_of_suspended handler context
        (prefixSteps + 1 + suffixSteps) suffixSteps start suspension execution]
      rw [handled]
      exact ih ready

/-- Any fuel-sound relational witness determines the executable driver result. -/
theorem run_eq_of_fuelSoundWith
    {Context : Type u}
    (handler : HostHandler Context)
    (startContext : Context)
    (fuel : Nat)
    (start : Core.State)
    (result : HostDriverResult Context)
    (sound :
      result.FuelSoundWith handler fuel startContext start) :
    run handler startContext fuel start = result := by
  cases result with
  | mk finalContext outcome =>
      cases outcome with
      | done value store =>
          change ∃ spent, spent ≤ fuel ∧ _ at sound
          obtain ⟨spent, enough, path⟩ := sound
          exact run_done_complete handler path enough
      | outOfFuel exhausted =>
          change _ ∧ _ at sound
          exact run_outOfFuel_complete handler sound.1 sound.2
      | fault error faultState =>
          change ∃ spent, spent ≤ fuel ∧ _ ∧ _ at sound
          obtain ⟨spent, enough, path, terminal⟩ := sound
          exact run_fault_complete handler path terminal enough

/-- Executable generic driver results are exactly the fuel-sound results. -/
theorem run_eq_iff_fuelSoundWith
    {Context : Type u}
    (handler : HostHandler Context)
    (startContext : Context)
    (fuel : Nat)
    (start : Core.State)
    (result : HostDriverResult Context) :
    run handler startContext fuel start = result ↔
      result.FuelSoundWith handler fuel startContext start := by
  constructor
  · intro execution
    rw [← execution]
    exact run_fuelSound handler startContext fuel start
  · exact run_eq_of_fuelSoundWith handler startContext fuel start result

/-- A completed result is unchanged when the driver receives more fuel. -/
theorem run_done_stable
    {Context : Type u}
    (handler : HostHandler Context)
    {fuel largerFuel : Nat}
    {startContext finalContext : Context}
    {start : Core.State}
    {value : Core.Value}
    {store : Core.Store}
    (execution :
      run handler startContext fuel start =
        ⟨finalContext, .done value store⟩)
    (more : fuel ≤ largerFuel) :
    run handler startContext largerFuel start =
      ⟨finalContext, .done value store⟩ := by
  have sound := run_fuelSound handler startContext fuel start
  rw [execution] at sound
  change ∃ spent, spent ≤ fuel ∧ _ at sound
  obtain ⟨spent, enough, path⟩ := sound
  apply run_done_complete handler path
  exact Nat.le_trans enough more

/-- A raw fault result is unchanged when the driver receives more fuel. -/
theorem run_fault_stable
    {Context : Type u}
    (handler : HostHandler Context)
    {fuel largerFuel : Nat}
    {startContext finalContext : Context}
    {start faultState : Core.State}
    {error : Core.MachineFault}
    (execution :
      run handler startContext fuel start =
        ⟨finalContext, .fault error faultState⟩)
    (more : fuel ≤ largerFuel) :
    run handler startContext largerFuel start =
      ⟨finalContext, .fault error faultState⟩ := by
  have sound := run_fuelSound handler startContext fuel start
  rw [execution] at sound
  change ∃ spent, spent ≤ fuel ∧ _ ∧ _ at sound
  obtain ⟨spent, enough, path, terminal⟩ := sound
  apply run_fault_complete handler path terminal
  exact Nat.le_trans enough more

end HostDriver

namespace HostDriverResult.FuelSoundWith

/-- Two fuel-sound witnesses for one exact budget determine the same result. -/
theorem result_unique
    {Context : Type u}
    {handler : HostHandler Context}
    {fuel : Nat}
    {startContext : Context}
    {start : Core.State}
    {left right : HostDriverResult Context}
    (leftSound :
      left.FuelSoundWith handler fuel startContext start)
    (rightSound :
      right.FuelSoundWith handler fuel startContext start) :
    left = right := by
  exact
    (HostDriver.run_eq_of_fuelSoundWith
      handler startContext fuel start left leftSound).symm.trans
    (HostDriver.run_eq_of_fuelSoundWith
      handler startContext fuel start right rightSound)

/-- Done evidence remains valid when its fuel allowance is increased. -/
theorem done_mono
    {Context : Type u}
    {handler : HostHandler Context}
    {fuel largerFuel : Nat}
    {startContext finalContext : Context}
    {start : Core.State}
    {value : Core.Value}
    {store : Core.Store}
    (sound :
      (⟨finalContext, .done value store⟩ :
        HostDriverResult Context).FuelSoundWith
          handler fuel startContext start)
    (more : fuel ≤ largerFuel) :
    (⟨finalContext, .done value store⟩ :
      HostDriverResult Context).FuelSoundWith
        handler largerFuel startContext start := by
  change ∃ spent, spent ≤ fuel ∧ _ at sound
  change ∃ spent, spent ≤ largerFuel ∧ _
  obtain ⟨spent, bound, path⟩ := sound
  exact ⟨spent, Nat.le_trans bound more, path⟩

/-- Raw-fault evidence remains valid when its fuel allowance is increased. -/
theorem fault_mono
    {Context : Type u}
    {handler : HostHandler Context}
    {fuel largerFuel : Nat}
    {startContext finalContext : Context}
    {start faultState : Core.State}
    {error : Core.MachineFault}
    (sound :
      (⟨finalContext, .fault error faultState⟩ :
        HostDriverResult Context).FuelSoundWith
          handler fuel startContext start)
    (more : fuel ≤ largerFuel) :
    (⟨finalContext, .fault error faultState⟩ :
      HostDriverResult Context).FuelSoundWith
        handler largerFuel startContext start := by
  change ∃ spent, spent ≤ fuel ∧ _ ∧ _ at sound
  change ∃ spent, spent ≤ largerFuel ∧ _ ∧ _
  obtain ⟨spent, bound, path, terminal⟩ := sound
  exact ⟨spent, Nat.le_trans bound more, path, terminal⟩

/-- Done witnesses at any two budgets retain the exact same complete result. -/
theorem done_result_unique
    {Context : Type u}
    {handler : HostHandler Context}
    {leftFuel rightFuel : Nat}
    {startContext leftContext rightContext : Context}
    {start : Core.State}
    {leftValue rightValue : Core.Value}
    {leftStore rightStore : Core.Store}
    (leftSound :
      (⟨leftContext, .done leftValue leftStore⟩ :
        HostDriverResult Context).FuelSoundWith
          handler leftFuel startContext start)
    (rightSound :
      (⟨rightContext, .done rightValue rightStore⟩ :
        HostDriverResult Context).FuelSoundWith
          handler rightFuel startContext start) :
    (⟨leftContext, .done leftValue leftStore⟩ :
      HostDriverResult Context) =
      ⟨rightContext, .done rightValue rightStore⟩ := by
  exact result_unique
    (done_mono leftSound (Nat.le_max_left leftFuel rightFuel))
    (done_mono rightSound (Nat.le_max_right leftFuel rightFuel))

/-- Fault witnesses at any two budgets retain the exact same complete result. -/
theorem fault_result_unique
    {Context : Type u}
    {handler : HostHandler Context}
    {leftFuel rightFuel : Nat}
    {startContext leftContext rightContext : Context}
    {start leftFaultState rightFaultState : Core.State}
    {leftError rightError : Core.MachineFault}
    (leftSound :
      (⟨leftContext, .fault leftError leftFaultState⟩ :
        HostDriverResult Context).FuelSoundWith
          handler leftFuel startContext start)
    (rightSound :
      (⟨rightContext, .fault rightError rightFaultState⟩ :
        HostDriverResult Context).FuelSoundWith
          handler rightFuel startContext start) :
    (⟨leftContext, .fault leftError leftFaultState⟩ :
      HostDriverResult Context) =
      ⟨rightContext, .fault rightError rightFaultState⟩ := by
  exact result_unique
    (fault_mono leftSound (Nat.le_max_left leftFuel rightFuel))
    (fault_mono rightSound (Nat.le_max_right leftFuel rightFuel))

end HostDriverResult.FuelSoundWith

end Solcore.Semantics
