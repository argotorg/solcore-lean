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

end Solcore.Semantics
